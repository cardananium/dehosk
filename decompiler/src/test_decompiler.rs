//! Run the decompiler over Plutus scripts from a CSV file and collect
//! statistics.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use miette::{IntoDiagnostic, Result};
use serde::{Deserialize, Serialize};

use dehosk::{DecompileOptions, ScriptVersion, decompile_with_large_stack};

#[derive(Parser)]
#[command(name = "test-decompiler")]
#[command(about = "Test decompiler on scripts from CSV file")]
struct Args {
    /// Path to CSV file with Plutus scripts
    #[arg(short, long)]
    csv: PathBuf,

    /// Output directory for decompiled scripts (optional)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Maximum number of scripts to process (for testing)
    #[arg(short, long)]
    limit: Option<usize>,

    /// Process only a specific script id from CSV
    #[arg(long)]
    script_id: Option<String>,

    /// Deterministically sample scripts across the whole CSV
    #[arg(long)]
    sample_size: Option<usize>,

    /// Show verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Don't recognize high-level patterns (output raw translation)
    #[arg(long)]
    raw: bool,

    /// Don't infer types
    #[arg(long)]
    no_types: bool,

    /// Don't optimize output
    #[arg(long)]
    no_optimize: bool,

    /// Safer, less opinionated decompilation (disables ambiguous rewrites)
    #[arg(long)]
    safe_mode: bool,

    /// Print categorized residual thunk patterns (force/delay clusters)
    #[arg(long)]
    thunk_patterns: bool,

    /// Write per-script metrics and cluster impact report as JSON
    #[arg(long)]
    metrics_json: Option<PathBuf>,

    /// Compare current run against previously saved metrics JSON report
    #[arg(long)]
    compare_metrics_json: Option<PathBuf>,

    /// Rank safe rewrite candidates from residual thunk patterns
    #[arg(long)]
    rank_rewrites: bool,

    /// Write ranked rewrite candidates as JSON
    #[arg(long)]
    rewrite_candidates_json: Option<PathBuf>,

    /// Number of top rewrite candidates to print
    #[arg(long, default_value_t = 12)]
    top_candidates: usize,

    /// Inspect one thunk cluster with top signatures and examples
    #[arg(long)]
    inspect_cluster: Option<String>,

    /// Number of signatures to print for --inspect-cluster
    #[arg(long, default_value_t = 8)]
    inspect_top_signatures: usize,

    /// Number of example script hits per signature for --inspect-cluster
    #[arg(long, default_value_t = 3)]
    inspect_examples: usize,

    /// Write --inspect-cluster output as JSON
    #[arg(long)]
    inspect_cluster_json: Option<PathBuf>,
}

const THUNK_PATTERNS: [(&str, &str); 10] = [
    ("force(force(", "double_force_chain"),
    ("force(let", "force_let"),
    ("force(debug", "force_debug"),
    ("force(trace", "force_trace"),
    ("delay(force(", "delay_force"),
    ("delay(let", "delay_let"),
    ("delay(when", "delay_when"),
    ("delay(fn", "delay_fn"),
    ("delay(Data.Constr", "delay_data_constr"),
    ("delay(fail", "delay_fail"),
];

#[derive(Debug, Clone)]
struct ScriptInfo {
    id: String,
    #[allow(dead_code)]
    tx_id: String,
    hash: String,
    script_type: String,
    bytes: String,
    #[allow(dead_code)]
    serialised_size: Option<usize>,
}

#[derive(Debug)]
struct DecompileResult {
    success: bool,
    output: Option<String>,
    output_length: usize,
    error: Option<String>,
    decompile_time: u128, // milliseconds
}

#[derive(Debug, Serialize, Deserialize)]
struct ScriptMetricsRow {
    script_id: String,
    script_hash: String,
    script_type: String,
    success: bool,
    output_length: usize,
    decompile_time_ms: u128,
    readability: ReadabilitySignals,
    thunk_hits: BTreeMap<String, usize>,
    script_score: usize,
    error: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ClusterImpactRow {
    key: String,
    total_hits: usize,
    scripts: usize,
    impact_score: usize,
}

#[derive(Debug, Serialize, Deserialize)]
struct MetricsSummary {
    total: usize,
    successful: usize,
    failed: usize,
    avg_output_length: usize,
    avg_decompile_time_ms: f64,
    total_force: usize,
    total_delay: usize,
}

#[derive(Debug, Serialize, Deserialize)]
struct MetricsReport {
    summary: MetricsSummary,
    cluster_impact: Vec<ClusterImpactRow>,
    scripts: Vec<ScriptMetricsRow>,
}

#[derive(Debug, Serialize, Deserialize)]
struct RewriteCandidateRow {
    cluster_key: String,
    signature: String,
    total_hits: usize,
    scripts: usize,
    impact_score: usize,
    safety_score: f64,
    avg_script_score: f64,
    candidate_score: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct RewriteCandidatesReport {
    total_signatures: usize,
    top_candidates: Vec<RewriteCandidateRow>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let options = if args.raw {
        DecompileOptions::raw()
    } else {
        DecompileOptions {
            type_passes: if args.no_types {
                dehosk::decompile::TypePasses::all_off()
            } else {
                dehosk::decompile::TypePasses::all_on()
            },
            simplify_passes: if args.no_optimize {
                dehosk::decompile::SimplifyPasses::all_off()
            } else {
                dehosk::decompile::SimplifyPasses::all_on()
            },
            safe_mode: args.safe_mode,
            ..DecompileOptions::default()
        }
    };

    if args.verbose {
        eprintln!("Reading CSV file: {}", args.csv.display());
    }

    let scripts = read_csv(&args.csv)?;

    if args.verbose {
        eprintln!("Found {} scripts in CSV", scripts.len());
    }

    if let Some(ref output_dir) = args.output {
        std::fs::create_dir_all(output_dir).into_diagnostic()?;
        if args.verbose {
            eprintln!("Output directory: {}", output_dir.display());
        }
    }

    let mut scripts_to_process = if let Some(sample_size) = args.sample_size {
        deterministic_sample(&scripts, sample_size)
    } else {
        scripts
    };
    if let Some(ref script_id) = args.script_id {
        scripts_to_process.retain(|s| &s.id == script_id);
    }
    if let Some(limit) = args.limit {
        scripts_to_process.truncate(limit);
    }

    if args.verbose {
        eprintln!("Processing {} scripts...", scripts_to_process.len());
    }

    let mut results = Vec::new();
    let mut stats = Stats::new();

    for (idx, script) in scripts_to_process.iter().enumerate() {
        if args.verbose && (idx + 1) % 100 == 0 {
            eprintln!(
                "Processed {}/{} scripts...",
                idx + 1,
                scripts_to_process.len()
            );
        }

        let result = decompile_script(script, &options);

        stats.total += 1;
        if result.success {
            stats.successful += 1;
            stats.total_output_length += result.output_length;
            if result.output_length > stats.max_output_length {
                stats.max_output_length = result.output_length;
            }
            if result.output_length < stats.min_output_length {
                stats.min_output_length = result.output_length;
            }
            if let Some(ref output) = result.output {
                let signals = analyze_readability(output);
                stats.readability_total.add_assign(signals);
                stats
                    .readability_hit_scripts
                    .add_assign(signals.hit_flags());
            }
        } else {
            stats.failed += 1;
            if let Some(ref error) = result.error {
                stats
                    .error_counts
                    .entry(error.clone())
                    .and_modify(|e| *e += 1)
                    .or_insert(1);
            }
        }
        stats.total_decompile_time += result.decompile_time;

        if let Some(ref output_dir) = args.output
            && result.success
            && let Some(ref output) = result.output
        {
            let output_file = output_dir.join(format!("{}.dehosk", script.id));
            if let Err(e) = std::fs::write(
                &output_file,
                format!(
                    "// Script ID: {}\n// Hash: {}\n// Type: {}\n\n{}",
                    script.id, script.hash, script.script_type, output
                ),
            ) {
                eprintln!(
                    "Warning: Failed to write output for script {}: {}",
                    script.id, e
                );
            }
        }

        results.push((script.clone(), result));
    }

    print_statistics(&stats, &results, args.verbose);
    if args.thunk_patterns {
        print_thunk_patterns(&results);
    }
    if args.metrics_json.is_some() || args.compare_metrics_json.is_some() {
        let report = build_metrics_report(&stats, &results);

        if let Some(path) = &args.compare_metrics_json {
            let previous_raw = std::fs::read_to_string(path).into_diagnostic()?;
            let previous: MetricsReport = serde_json::from_str(&previous_raw).into_diagnostic()?;
            print_metrics_delta(&previous, &report);
        }

        if let Some(path) = &args.metrics_json {
            let json = serde_json::to_string_pretty(&report).into_diagnostic()?;
            std::fs::write(path, json).into_diagnostic()?;
            println!("\nMetrics JSON written: {}", path.display());
        }
    }

    if args.rank_rewrites || args.rewrite_candidates_json.is_some() {
        let candidates = rank_rewrite_candidates(&results, args.top_candidates);
        print_rewrite_candidates(&candidates);

        if let Some(path) = &args.rewrite_candidates_json {
            let json = serde_json::to_string_pretty(&candidates).into_diagnostic()?;
            std::fs::write(path, json).into_diagnostic()?;
            println!("Rewrite candidates JSON written: {}", path.display());
        }
    }

    if let Some(cluster) = &args.inspect_cluster {
        let report = build_cluster_inspection(
            &results,
            cluster,
            args.inspect_top_signatures,
            args.inspect_examples,
        );
        print_cluster_inspection(&report);
        if let Some(path) = &args.inspect_cluster_json {
            let json = serde_json::to_string_pretty(&report).into_diagnostic()?;
            std::fs::write(path, json).into_diagnostic()?;
            println!("Cluster inspection JSON written: {}", path.display());
        }
    }

    Ok(())
}

fn read_csv(path: &PathBuf) -> Result<Vec<ScriptInfo>> {
    let mut reader = csv::Reader::from_path(path).into_diagnostic()?;
    let mut scripts = Vec::new();

    for result in reader.records() {
        let record = result.into_diagnostic()?;

        // CSV columns: #, id, tx_id, hash, type, json, bytes, serialised_size
        if record.len() < 8 {
            continue;
        }

        // Skip if first column is "#" (header row)
        if record.get(0).map(|s| s.trim() == "#").unwrap_or(false) {
            continue;
        }

        let bytes_str = record.get(6).unwrap_or("").trim();
        if bytes_str.is_empty() || !bytes_str.starts_with("0x") {
            continue;
        }

        let hex_bytes = bytes_str.strip_prefix("0x").unwrap_or(bytes_str);

        let serialised_size = record.get(7).and_then(|s| s.trim().parse::<usize>().ok());

        let script = ScriptInfo {
            id: record.get(1).unwrap_or("").to_string(), // id is at index 1
            tx_id: record.get(2).unwrap_or("").to_string(), // tx_id is at index 2
            hash: record.get(3).unwrap_or("").to_string(), // hash is at index 3
            script_type: record.get(4).unwrap_or("").to_string(), // type is at index 4
            bytes: hex_bytes.to_string(),
            serialised_size,
        };

        scripts.push(script);
    }

    Ok(scripts)
}

fn decompile_script(script: &ScriptInfo, options: &DecompileOptions) -> DecompileResult {
    let start = Instant::now();

    let mut opts = options.clone();
    opts.script_version = match script.script_type.as_str() {
        "plutusV1" => Some(ScriptVersion::PlutusV1),
        "plutusV2" => Some(ScriptVersion::PlutusV2),
        "plutusV3" => Some(ScriptVersion::PlutusV3),
        _ => None,
    };

    match decompile_with_large_stack(&script.bytes, opts) {
        Ok(output) => {
            let elapsed = start.elapsed().as_millis();
            let output_len = output.len();
            DecompileResult {
                success: true,
                output: Some(output),
                output_length: output_len,
                error: None,
                decompile_time: elapsed,
            }
        }
        Err(e) => {
            let elapsed = start.elapsed().as_millis();
            let error_msg = format!("{}", e);
            DecompileResult {
                success: false,
                output: None,
                output_length: 0,
                error: Some(error_msg),
                decompile_time: elapsed,
            }
        }
    }
}

fn deterministic_sample(items: &[ScriptInfo], sample_size: usize) -> Vec<ScriptInfo> {
    if sample_size == 0 || items.is_empty() {
        return Vec::new();
    }
    if sample_size >= items.len() {
        return items.to_vec();
    }

    let step = items.len() as f64 / sample_size as f64;
    let mut out = Vec::with_capacity(sample_size);
    for i in 0..sample_size {
        let mut idx = (i as f64 * step).floor() as usize;
        if idx >= items.len() {
            idx = items.len() - 1;
        }
        out.push(items[idx].clone());
    }
    out
}

fn analyze_readability(output: &str) -> ReadabilitySignals {
    ReadabilitySignals {
        constr_unknown: count_occurrences(output, "Constr<"),
        data_placeholder: count_occurrences(output, "Data(...)"),
        force_nodes: count_occurrences(output, "force("),
        delay_nodes: count_occurrences(output, "delay("),
        trace_nodes: count_occurrences(output, "trace "),
        expect_calls: count_occurrences(output, "expect "),
        when_forms: count_occurrences(output, "when "),
        if_forms: count_occurrences(output, "if "),
        and_ops: count_occurrences(output, " && "),
        or_ops: count_occurrences(output, " || "),
    }
}

fn count_occurrences(haystack: &str, needle: &str) -> usize {
    haystack.match_indices(needle).count()
}

#[derive(Debug)]
struct Stats {
    total: usize,
    successful: usize,
    failed: usize,
    total_output_length: usize,
    max_output_length: usize,
    min_output_length: usize,
    total_decompile_time: u128,
    error_counts: HashMap<String, usize>,
    readability_total: ReadabilitySignals,
    readability_hit_scripts: ReadabilitySignals,
}

impl Stats {
    fn new() -> Self {
        Self {
            total: 0,
            successful: 0,
            failed: 0,
            total_output_length: 0,
            max_output_length: 0,
            min_output_length: usize::MAX,
            total_decompile_time: 0,
            error_counts: HashMap::new(),
            readability_total: ReadabilitySignals::default(),
            readability_hit_scripts: ReadabilitySignals::default(),
        }
    }
}

#[derive(Debug, Default, Clone, Copy, Serialize, Deserialize)]
struct ReadabilitySignals {
    constr_unknown: usize,
    data_placeholder: usize,
    force_nodes: usize,
    delay_nodes: usize,
    trace_nodes: usize,
    expect_calls: usize,
    when_forms: usize,
    if_forms: usize,
    and_ops: usize,
    or_ops: usize,
}

impl ReadabilitySignals {
    fn add_assign(&mut self, other: ReadabilitySignals) {
        self.constr_unknown += other.constr_unknown;
        self.data_placeholder += other.data_placeholder;
        self.force_nodes += other.force_nodes;
        self.delay_nodes += other.delay_nodes;
        self.trace_nodes += other.trace_nodes;
        self.expect_calls += other.expect_calls;
        self.when_forms += other.when_forms;
        self.if_forms += other.if_forms;
        self.and_ops += other.and_ops;
        self.or_ops += other.or_ops;
    }

    fn hit_flags(self) -> ReadabilitySignals {
        ReadabilitySignals {
            constr_unknown: usize::from(self.constr_unknown > 0),
            data_placeholder: usize::from(self.data_placeholder > 0),
            force_nodes: usize::from(self.force_nodes > 0),
            delay_nodes: usize::from(self.delay_nodes > 0),
            trace_nodes: usize::from(self.trace_nodes > 0),
            expect_calls: usize::from(self.expect_calls > 0),
            when_forms: usize::from(self.when_forms > 0),
            if_forms: usize::from(self.if_forms > 0),
            and_ops: usize::from(self.and_ops > 0),
            or_ops: usize::from(self.or_ops > 0),
        }
    }
}

fn print_statistics(stats: &Stats, results: &[(ScriptInfo, DecompileResult)], verbose: bool) {
    println!("\n=== Decompiler Test Statistics ===\n");

    println!("Total scripts processed: {}", stats.total);
    println!(
        "Successful: {} ({:.2}%)",
        stats.successful,
        if stats.total > 0 {
            (stats.successful as f64 / stats.total as f64) * 100.0
        } else {
            0.0
        }
    );
    println!(
        "Failed: {} ({:.2}%)",
        stats.failed,
        if stats.total > 0 {
            (stats.failed as f64 / stats.total as f64) * 100.0
        } else {
            0.0
        }
    );

    if stats.successful > 0 {
        println!("\nOutput Statistics (successful decompilations):");
        println!(
            "  Average output length: {} chars",
            stats.total_output_length / stats.successful
        );
        println!("  Max output length: {} chars", stats.max_output_length);
        if stats.min_output_length != usize::MAX {
            println!("  Min output length: {} chars", stats.min_output_length);
        }

        println!("\nReadability signals:");
        print_signal(
            "Unknown constructors (Constr<...>)",
            stats.readability_total.constr_unknown,
            stats.readability_hit_scripts.constr_unknown,
            stats.successful,
        );
        print_signal(
            "Data placeholders (Data(...))",
            stats.readability_total.data_placeholder,
            stats.readability_hit_scripts.data_placeholder,
            stats.successful,
        );
        print_signal(
            "Residual force(...)",
            stats.readability_total.force_nodes,
            stats.readability_hit_scripts.force_nodes,
            stats.successful,
        );
        print_signal(
            "Residual delay(...)",
            stats.readability_total.delay_nodes,
            stats.readability_hit_scripts.delay_nodes,
            stats.successful,
        );
        print_signal(
            "trace occurrences",
            stats.readability_total.trace_nodes,
            stats.readability_hit_scripts.trace_nodes,
            stats.successful,
        );
        print_signal(
            "expect forms",
            stats.readability_total.expect_calls,
            stats.readability_hit_scripts.expect_calls,
            stats.successful,
        );
        print_signal(
            "when forms",
            stats.readability_total.when_forms,
            stats.readability_hit_scripts.when_forms,
            stats.successful,
        );
        print_signal(
            "if forms",
            stats.readability_total.if_forms,
            stats.readability_hit_scripts.if_forms,
            stats.successful,
        );
        print_signal(
            "&& forms",
            stats.readability_total.and_ops,
            stats.readability_hit_scripts.and_ops,
            stats.successful,
        );
        print_signal(
            "|| forms",
            stats.readability_total.or_ops,
            stats.readability_hit_scripts.or_ops,
            stats.successful,
        );
    }

    if stats.total > 0 {
        println!("\nPerformance:");
        println!(
            "  Average decompile time: {:.2} ms",
            stats.total_decompile_time as f64 / stats.total as f64
        );
        println!("  Total time: {:.2} ms", stats.total_decompile_time);
    }

    if !stats.error_counts.is_empty() {
        println!("\nError Summary:");
        let mut errors: Vec<_> = stats.error_counts.iter().collect();
        errors.sort_by(|a, b| b.1.cmp(a.1));

        for (error, count) in errors.iter().take(10) {
            println!(
                "  {}: {} occurrences",
                error.lines().next().unwrap_or(error),
                count
            );
        }
        if errors.len() > 10 {
            println!("  ... and {} more error types", errors.len() - 10);
        }
    }

    if verbose && !results.is_empty() {
        println!("\nFirst few results:");
        for (script, result) in results.iter().take(5) {
            println!(
                "\nScript ID: {}, TX ID: {}, Hash: {}",
                script.id,
                script.tx_id,
                &script.hash[..16.min(script.hash.len())]
            );
            if let Some(size) = script.serialised_size {
                println!("  Serialised size: {} bytes", size);
            }
            println!("  Success: {}", result.success);
            if result.success {
                println!("  Output length: {} chars", result.output_length);
            } else if let Some(ref error) = result.error {
                println!("  Error: {}", error.lines().next().unwrap_or(error));
            }
            println!("  Time: {} ms", result.decompile_time);
        }
    }
}

fn print_thunk_patterns(results: &[(ScriptInfo, DecompileResult)]) {
    let mut total_hits: HashMap<&'static str, usize> = HashMap::new();
    let mut script_hits: HashMap<&'static str, usize> = HashMap::new();
    let mut impact_scores: HashMap<&'static str, usize> = HashMap::new();

    for (_, result) in results.iter() {
        let Some(output) = &result.output else {
            continue;
        };

        for (needle, key) in THUNK_PATTERNS {
            let hits = count_occurrences(output, needle);
            if hits > 0 {
                *total_hits.entry(key).or_insert(0) += hits;
                *script_hits.entry(key).or_insert(0) += 1;
                *impact_scores.entry(key).or_insert(0) += hits * thunk_pattern_weight(key);
            }
        }
    }

    let mut rows: Vec<(&str, usize, usize, usize)> = THUNK_PATTERNS
        .iter()
        .map(|(_, key)| {
            (
                *key,
                *total_hits.get(key).unwrap_or(&0),
                *script_hits.get(key).unwrap_or(&0),
                *impact_scores.get(key).unwrap_or(&0),
            )
        })
        .collect();

    rows.sort_by(|a, b| {
        b.3.cmp(&a.3)
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| b.2.cmp(&a.2))
    });

    println!("\nResidual thunk pattern clusters:");
    for (key, total, scripts, impact) in rows {
        if total > 0 {
            println!(
                "  {}: {} total, {} scripts, impact {}",
                key, total, scripts, impact
            );
        }
    }

    print_top_thunk_offenders(results);
}

fn print_top_thunk_offenders(results: &[(ScriptInfo, DecompileResult)]) {
    let mut by_force: Vec<(String, usize)> = Vec::new();
    let mut by_delay: Vec<(String, usize)> = Vec::new();
    let mut by_double_force: Vec<(String, usize)> = Vec::new();
    let mut by_delay_force: Vec<(String, usize)> = Vec::new();

    for (script, result) in results {
        if let Some(output) = &result.output {
            by_force.push((script.id.clone(), count_occurrences(output, "force(")));
            by_delay.push((script.id.clone(), count_occurrences(output, "delay(")));
            by_double_force.push((script.id.clone(), count_occurrences(output, "force(force(")));
            by_delay_force.push((script.id.clone(), count_occurrences(output, "delay(force(")));
        }
    }

    by_force.sort_by(|a, b| b.1.cmp(&a.1));
    by_delay.sort_by(|a, b| b.1.cmp(&a.1));
    by_double_force.sort_by(|a, b| b.1.cmp(&a.1));
    by_delay_force.sort_by(|a, b| b.1.cmp(&a.1));

    fn print_top(label: &str, rows: &[(String, usize)]) {
        println!("\nTop scripts by {}:", label);
        for (id, count) in rows.iter().take(10) {
            if *count > 0 {
                println!("  script_id {}: {}", id, count);
            }
        }
    }

    print_top("force(", &by_force);
    print_top("delay(", &by_delay);
    print_top("force(force(", &by_double_force);
    print_top("delay(force(", &by_delay_force);
}

fn thunk_pattern_weight(key: &str) -> usize {
    match key {
        "double_force_chain" => 5,
        "delay_force" => 4,
        "delay_fn" => 3,
        "delay_let" | "delay_when" | "delay_data_constr" | "force_let" => 2,
        _ => 1,
    }
}

fn collect_thunk_hits(output: &str) -> BTreeMap<String, usize> {
    let mut map = BTreeMap::new();
    for (needle, key) in THUNK_PATTERNS {
        let hits = count_occurrences(output, needle);
        if hits > 0 {
            map.insert(key.to_string(), hits);
        }
    }
    map
}

fn compute_script_score(
    signals: ReadabilitySignals,
    thunk_hits: &BTreeMap<String, usize>,
) -> usize {
    let mut score = 2 * signals.force_nodes + 2 * signals.delay_nodes;
    score += 5 * count_occurrences_in_hits(thunk_hits, "double_force_chain");
    score += 4 * count_occurrences_in_hits(thunk_hits, "delay_force");
    for (key, hits) in thunk_hits {
        score += thunk_pattern_weight(key) * *hits;
    }
    score
}

fn count_occurrences_in_hits(thunk_hits: &BTreeMap<String, usize>, key: &str) -> usize {
    *thunk_hits.get(key).unwrap_or(&0)
}

fn build_metrics_report(stats: &Stats, results: &[(ScriptInfo, DecompileResult)]) -> MetricsReport {
    let mut scripts = Vec::with_capacity(results.len());
    let mut cluster_totals: HashMap<String, usize> = HashMap::new();
    let mut cluster_scripts: HashMap<String, usize> = HashMap::new();
    let mut cluster_impact: HashMap<String, usize> = HashMap::new();

    for (script, result) in results {
        let (readability, thunk_hits, script_score) = if let Some(output) = &result.output {
            let readability = analyze_readability(output);
            let thunk_hits = collect_thunk_hits(output);
            let score = compute_script_score(readability, &thunk_hits);
            (readability, thunk_hits, score)
        } else {
            (ReadabilitySignals::default(), BTreeMap::new(), 0)
        };

        for (key, hits) in &thunk_hits {
            *cluster_totals.entry(key.clone()).or_insert(0) += *hits;
            *cluster_scripts.entry(key.clone()).or_insert(0) += 1;
            *cluster_impact.entry(key.clone()).or_insert(0) += thunk_pattern_weight(key) * *hits;
        }

        scripts.push(ScriptMetricsRow {
            script_id: script.id.clone(),
            script_hash: script.hash.clone(),
            script_type: script.script_type.clone(),
            success: result.success,
            output_length: result.output_length,
            decompile_time_ms: result.decompile_time,
            readability,
            thunk_hits,
            script_score,
            error: result.error.clone(),
        });
    }

    let mut cluster_rows: Vec<ClusterImpactRow> = cluster_impact
        .into_iter()
        .map(|(key, impact_score)| ClusterImpactRow {
            total_hits: *cluster_totals.get(&key).unwrap_or(&0),
            scripts: *cluster_scripts.get(&key).unwrap_or(&0),
            key,
            impact_score,
        })
        .collect();
    cluster_rows.sort_by(|a, b| {
        b.impact_score
            .cmp(&a.impact_score)
            .then_with(|| b.total_hits.cmp(&a.total_hits))
    });

    let avg_output_length = if stats.successful > 0 {
        stats.total_output_length / stats.successful
    } else {
        0
    };
    let avg_decompile_time_ms = if stats.total > 0 {
        stats.total_decompile_time as f64 / stats.total as f64
    } else {
        0.0
    };

    MetricsReport {
        summary: MetricsSummary {
            total: stats.total,
            successful: stats.successful,
            failed: stats.failed,
            avg_output_length,
            avg_decompile_time_ms,
            total_force: stats.readability_total.force_nodes,
            total_delay: stats.readability_total.delay_nodes,
        },
        cluster_impact: cluster_rows,
        scripts,
    }
}

fn print_metrics_delta(previous: &MetricsReport, current: &MetricsReport) {
    println!("\n=== Metrics Delta (vs baseline JSON) ===\n");

    let force_delta = current.summary.total_force as isize - previous.summary.total_force as isize;
    let delay_delta = current.summary.total_delay as isize - previous.summary.total_delay as isize;
    let success_delta = current.summary.successful as isize - previous.summary.successful as isize;

    println!(
        "Summary delta: successful {:+}, force {:+}, delay {:+}",
        success_delta, force_delta, delay_delta
    );

    let mut previous_impact: HashMap<&str, usize> = HashMap::new();
    for row in &previous.cluster_impact {
        previous_impact.insert(row.key.as_str(), row.impact_score);
    }

    let mut rows: Vec<(&str, usize, isize)> = current
        .cluster_impact
        .iter()
        .map(|row| {
            let prev = *previous_impact.get(row.key.as_str()).unwrap_or(&0);
            (
                row.key.as_str(),
                row.impact_score,
                row.impact_score as isize - prev as isize,
            )
        })
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| b.2.cmp(&a.2)));

    println!("Top cluster impact now:");
    for (key, impact, delta) in rows.iter().take(8) {
        println!("  {}: {} ({:+})", key, impact, delta);
    }
    if let Some((key, impact, delta)) = rows.first() {
        println!(
            "Suggested next target: {} (impact {}, delta {:+})",
            key, impact, delta
        );
    }
}

fn print_signal(name: &str, total_hits: usize, scripts_with_hits: usize, successful: usize) {
    let pct = if successful > 0 {
        (scripts_with_hits as f64 / successful as f64) * 100.0
    } else {
        0.0
    };
    println!(
        "  {}: {} total, {} scripts ({:.2}%)",
        name, total_hits, scripts_with_hits, pct
    );
}

#[derive(Debug, Clone)]
struct SignatureAgg {
    cluster_key: String,
    signature: String,
    total_hits: usize,
    script_ids: HashSet<String>,
    total_script_score: usize,
}

fn rank_rewrite_candidates(
    results: &[(ScriptInfo, DecompileResult)],
    top_n: usize,
) -> RewriteCandidatesReport {
    let mut by_signature: HashMap<(String, String), SignatureAgg> = HashMap::new();

    for (script, result) in results {
        let Some(output) = &result.output else {
            continue;
        };
        let signals = analyze_readability(output);
        let thunk_hits = collect_thunk_hits(output);
        let script_score = compute_script_score(signals, &thunk_hits);

        for (needle, key) in THUNK_PATTERNS {
            for (signature, hits) in extract_pattern_signatures(output, needle) {
                let entry = by_signature
                    .entry((key.to_string(), signature.clone()))
                    .or_insert_with(|| SignatureAgg {
                        cluster_key: key.to_string(),
                        signature,
                        total_hits: 0,
                        script_ids: HashSet::new(),
                        total_script_score: 0,
                    });
                entry.total_hits += hits;
                if entry.script_ids.insert(script.id.clone()) {
                    entry.total_script_score += script_score;
                }
            }
        }
    }

    let mut rows: Vec<RewriteCandidateRow> = by_signature
        .into_values()
        .map(|agg| {
            let scripts = agg.script_ids.len();
            let avg_script_score = if scripts > 0 {
                agg.total_script_score as f64 / scripts as f64
            } else {
                0.0
            };
            let impact_score = agg.total_hits * thunk_pattern_weight(&agg.cluster_key);
            let safety = safety_score(&agg.cluster_key, &agg.signature);
            let coverage = (scripts as f64 + 1.0).ln();
            let candidate_score =
                impact_score as f64 * coverage * safety * (1.0 + (avg_script_score / 200.0));

            RewriteCandidateRow {
                cluster_key: agg.cluster_key,
                signature: agg.signature,
                total_hits: agg.total_hits,
                scripts,
                impact_score,
                safety_score: safety,
                avg_script_score,
                candidate_score,
            }
        })
        .collect();

    rows.sort_by(|a, b| {
        b.candidate_score
            .total_cmp(&a.candidate_score)
            .then_with(|| b.impact_score.cmp(&a.impact_score))
            .then_with(|| b.total_hits.cmp(&a.total_hits))
    });
    let total_signatures = rows.len();
    rows.truncate(top_n);

    RewriteCandidatesReport {
        total_signatures,
        top_candidates: rows,
    }
}

fn print_rewrite_candidates(report: &RewriteCandidatesReport) {
    println!("\n=== Ranked Rewrite Candidates ===\n");
    println!("Distinct signatures analyzed: {}", report.total_signatures);
    for row in &report.top_candidates {
        println!(
            "  {} | score {:.1} | impact {} | safety {:.2} | scripts {} | hits {}",
            row.cluster_key,
            row.candidate_score,
            row.impact_score,
            row.safety_score,
            row.scripts,
            row.total_hits
        );
        println!("    signature: {}", row.signature);
    }
}

fn extract_pattern_signatures(output: &str, needle: &str) -> Vec<(String, usize)> {
    const WINDOW: usize = 48;
    let mut counts: HashMap<String, usize> = HashMap::new();
    for (idx, _) in output.match_indices(needle) {
        let start = idx.saturating_sub(WINDOW);
        let end = (idx + needle.len() + WINDOW).min(output.len());
        let context = &output[start..end];
        let signature = normalize_signature(context);
        *counts.entry(signature).or_insert(0) += 1;
    }
    counts.into_iter().collect()
}

fn extract_pattern_occurrences(output: &str, needle: &str) -> Vec<(String, String)> {
    const WINDOW: usize = 48;
    let mut out = Vec::new();
    for (idx, _) in output.match_indices(needle) {
        let start = idx.saturating_sub(WINDOW);
        let end = (idx + needle.len() + WINDOW).min(output.len());
        let context = output[start..end].replace('\n', " ");
        let signature = normalize_signature(&context);
        out.push((signature, context));
    }
    out
}

fn normalize_signature(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch.is_ascii_whitespace() {
            if !out.ends_with(' ') {
                out.push(' ');
            }
            continue;
        }

        if ch.is_ascii_digit() {
            while let Some(next) = chars.peek() {
                if next.is_ascii_digit() {
                    chars.next();
                } else {
                    break;
                }
            }
            out.push('#');
            continue;
        }

        if ch.is_ascii_alphabetic() || ch == '_' {
            let mut token = String::new();
            token.push(ch);
            while let Some(next) = chars.peek() {
                if next.is_ascii_alphanumeric() || *next == '_' || *next == '.' {
                    token.push(*next);
                    chars.next();
                } else {
                    break;
                }
            }
            if token == "force"
                || token == "delay"
                || token == "let"
                || token == "when"
                || token == "if"
                || token == "fn"
                || token == "expect"
                || token == "trace"
                || token == "debug"
                || token == "fail"
                || token == "error"
                || token == "Data.Constr"
            {
                out.push_str(&token);
            } else {
                out.push('v');
            }
            continue;
        }

        out.push(ch);
    }

    out.trim().to_string()
}

fn safety_score(cluster_key: &str, signature: &str) -> f64 {
    let mut score: f64 = 0.2;

    match cluster_key {
        "delay_let" | "delay_when" | "delay_data_constr" | "force_let" => score += 0.35,
        "delay_fn" | "delay_force" => score += 0.2,
        "double_force_chain" => score -= 0.6,
        _ => score += 0.1,
    }

    if signature.contains("builtin")
        || signature.contains("if_then_else")
        || signature.contains("choose_list")
    {
        score -= 0.2;
    }

    if signature.contains("force(force(") {
        score -= 0.2;
    }

    if signature.contains("force(let") || signature.contains("delay(let") {
        score += 0.15;
    }

    score.clamp(0.0, 1.0)
}

#[derive(Debug, Clone)]
struct ClusterExample {
    script_id: String,
    hits: usize,
    context: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct ClusterInspectionExample {
    script_id: String,
    hits: usize,
    context: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct ClusterInspectionSignature {
    signature: String,
    total_hits: usize,
    scripts: usize,
    examples: Vec<ClusterInspectionExample>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ClusterInspectionReport {
    cluster_key: String,
    signatures: Vec<ClusterInspectionSignature>,
}

fn build_cluster_inspection(
    results: &[(ScriptInfo, DecompileResult)],
    cluster_key: &str,
    top_signatures: usize,
    examples_per_signature: usize,
) -> ClusterInspectionReport {
    let Some((needle, _)) = THUNK_PATTERNS.iter().find(|(_, key)| *key == cluster_key) else {
        return ClusterInspectionReport {
            cluster_key: cluster_key.to_string(),
            signatures: vec![],
        };
    };

    let mut totals: HashMap<String, usize> = HashMap::new();
    let mut scripts: HashMap<String, HashSet<String>> = HashMap::new();
    let mut examples: HashMap<String, Vec<ClusterExample>> = HashMap::new();

    for (script, result) in results {
        let Some(output) = &result.output else {
            continue;
        };

        let mut per_script: HashMap<String, (usize, String)> = HashMap::new();
        for (signature, context) in extract_pattern_occurrences(output, needle) {
            let entry = per_script.entry(signature).or_insert((0, context));
            entry.0 += 1;
        }

        for (signature, (hits, context)) in per_script {
            *totals.entry(signature.clone()).or_insert(0) += hits;
            scripts
                .entry(signature.clone())
                .or_default()
                .insert(script.id.clone());
            examples.entry(signature).or_default().push(ClusterExample {
                script_id: script.id.clone(),
                hits,
                context,
            });
        }
    }

    let mut rows: Vec<(String, usize, usize)> = totals
        .iter()
        .map(|(sig, hits)| {
            let script_count = scripts.get(sig).map_or(0, |s| s.len());
            (sig.clone(), *hits, script_count)
        })
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| b.2.cmp(&a.2)));

    let mut signatures = Vec::new();
    for (signature, total_hits, script_count) in rows.into_iter().take(top_signatures) {
        let mut out_examples = Vec::new();
        if let Some(exs) = examples.get_mut(&signature) {
            exs.sort_by(|a, b| b.hits.cmp(&a.hits));
            for ex in exs.iter().take(examples_per_signature) {
                out_examples.push(ClusterInspectionExample {
                    script_id: ex.script_id.clone(),
                    hits: ex.hits,
                    context: ex.context.clone(),
                });
            }
        }
        signatures.push(ClusterInspectionSignature {
            signature,
            total_hits,
            scripts: script_count,
            examples: out_examples,
        });
    }

    ClusterInspectionReport {
        cluster_key: cluster_key.to_string(),
        signatures,
    }
}

fn print_cluster_inspection(report: &ClusterInspectionReport) {
    println!("\n=== Cluster Inspection: {} ===\n", report.cluster_key);
    if report.signatures.is_empty() {
        println!("No signatures found.");
        return;
    }
    for row in &report.signatures {
        println!(
            "signature: {} | hits {} | scripts {}",
            row.signature, row.total_hits, row.scripts
        );
        for ex in &row.examples {
            println!(
                "  script {} hits {} | context: {}",
                ex.script_id, ex.hits, ex.context
            );
        }
    }
}
