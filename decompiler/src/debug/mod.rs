use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use uplc::ast::{Constant, NamedDeBruijn, Program, Term};
use uplc::builtins::DefaultFunction;

use crate::decompile::{
    DecompileOptions, PipelineTelemetry, render_decompiled_expr_with_registry_and_final_types,
    run_pipeline_with_artifacts,
};
use crate::error::Result;
use crate::pseudo::ast::{PseudoExpr, PseudoNodeId, PseudoProvenanceGraph};
use crate::pseudo::mid::expr_id::SourceSpan;

pub(crate) type ExprId = u32;
pub(crate) type BindingId = u32;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugBundle {
    pub version: String,

    // UPLC-level structural graph (runtime-friendly provenance)
    pub root_expr: ExprId,
    pub nodes: Vec<DebugNode>,
    pub bindings: Vec<BindingInfo>,
    pub edges: Vec<DebugEdge>,
    pub binding_uses: Vec<BindingUse>,
    pub ambiguities: Vec<AmbiguityNote>,

    // Pass-by-pass snapshots on decompiled pseudo AST
    pub pass_snapshots: Vec<PassSnapshot>,
    pub pass_mappings: Vec<PassMapping>,

    // Rewrite journal (coarse-grained, pass-level)
    pub rewrites: Vec<RewriteEvent>,

    #[serde(default)]
    pub pipeline_telemetry: PipelineDebugTelemetry,

    // Human-readable outputs
    pub code: String,
    pub rendered_uplc_code: String,
    pub uplc_source_map: Vec<SpanMap>,
    pub code_source_map: Vec<SpanMap>,
    // Backward-compatible alias of `uplc_source_map`.
    #[serde(default)]
    pub source_map: Vec<SpanMap>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugNode {
    pub id: ExprId,
    pub kind: DebugNodeKind,
    pub origins: Vec<TermOrigin>,
    pub confidence: f32,
    pub notes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DebugNodeKind {
    Var {
        name: String,
        binding: Option<BindingId>,
        debruijn_index: usize,
    },
    Lambda {
        binding: BindingId,
        body: ExprId,
    },
    Apply {
        function: ExprId,
        argument: ExprId,
    },
    Constant {
        repr: String,
    },
    Builtin {
        name: String,
    },
    Force {
        body: ExprId,
    },
    Delay {
        body: ExprId,
    },
    Error,
    Constr {
        tag: usize,
        fields: Vec<ExprId>,
    },
    Case {
        subject: ExprId,
        branches: Vec<ExprId>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TermOrigin {
    pub uplc_uniq_id: isize,
    pub role: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BindingInfo {
    pub id: BindingId,
    pub name_hint: String,
    pub display_name: String,
    pub binder_expr: ExprId,
    pub scope_depth: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugEdge {
    pub from_expr: ExprId,
    pub to_expr: ExprId,
    pub role: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BindingUse {
    pub binding: BindingId,
    pub use_expr: ExprId,
    pub debruijn_index: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AmbiguityNote {
    pub node_id: ExprId,
    pub category: String,
    pub confidence: f32,
    pub alternatives: Vec<String>,
    pub details: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewriteEvent {
    pub pass: String,
    pub input_roots: Vec<u32>,
    pub output_roots: Vec<u32>,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanMap {
    pub expr_id: ExprId,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PassSnapshot {
    pub pass: String,
    pub root: u32,
    pub nodes: Vec<PassNode>,
    pub provenance: PseudoProvenanceGraph,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PassNode {
    pub id: u32,
    pub pseudo_node_id: PseudoNodeId,
    pub stable_id: u64,
    pub parent: Option<u32>,
    pub kind: String,
    pub summary: String,
    pub children: Vec<u32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PassMapping {
    pub from_pass: String,
    pub to_pass: String,
    pub matches: Vec<NodeMatch>,
    pub removed: Vec<u32>,
    pub added: Vec<u32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeMatch {
    pub from: u32,
    pub to: u32,
    pub confidence: f32,
    pub reason: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PipelineDebugTelemetry {
    pub fixed_point: FixedPointDebugTelemetry,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixedPointDebugTelemetry {
    pub max_iterations: usize,
    pub attempted_iterations: usize,
    pub converged: bool,
    pub hit_iteration_limit: bool,
}

pub fn decompile_program_debug(program: &Program<NamedDeBruijn>) -> Result<DebugBundle> {
    decompile_program_debug_with_options(program, DecompileOptions::default())
}

pub fn decompile_program_debug_with_options(
    program: &Program<NamedDeBruijn>,
    mut options: DecompileOptions,
) -> Result<DebugBundle> {
    // Capture the polarity-oracle runtime inputs before `options`
    // is consumed downstream — used only by the polarity-report layer.
    let oracle_data_args = options.oracle_data_args.clone();
    let oracle_tx = options.oracle_tx.clone();
    // 1) Build runtime-oriented UPLC structural graph (with uniq_id provenance)
    let mut builder = DebugBuilder::new();
    let root_expr = builder.lower(&program.term);

    builder.rewrites.push(RewriteEvent {
        pass: "lower_uplc".to_string(),
        input_roots: vec![root_expr],
        output_roots: vec![root_expr],
        reason: "Initial structural lowering from UPLC terms".to_string(),
    });

    let mut rendered_uplc_code = String::new();
    let mut uplc_source_map = Vec::new();
    builder.render(root_expr, &mut rendered_uplc_code, &mut uplc_source_map);

    // 2) Run actual decompiler pipeline and capture pass snapshots
    let mut pass_snapshots = Vec::new();
    let show_types = options.type_passes.any_enabled();
    // Capture the render-time toggles BEFORE `options` is moved into the
    // pipeline, so `bundle.code` honors them exactly like the public
    // `decompile_program` render.
    let decode_church = options.decode_church_to_native;
    let expect_or_fail = options.expect_or_fail;
    let compilable_data_access = options.compilable_data_access;
    let strip_all_traces = options.strip_all_traces;
    let strip_plutustx_traces = options.strip_plutustx_traces;
    // Honor `--emit` so `bundle.code` mirrors `decompile_program`'s
    // output for the chosen layer. Captured before `options` moves
    // into the pipeline.
    let output_layer = options.output_layer;
    // Seed `options.script_version` with the plan version BEFORE the
    // pipeline so version-gated passes behave as under
    // `decompile_program`; the field-naming version drives the render
    // guard (the `tx_info.fields[N]` → named-field relabel).
    let (plan_version, render_field_version) =
        crate::decompile::resolve_render_versions(program, options.script_version);
    options.script_version = plan_version;
    let pipeline_output = run_pipeline_with_artifacts(program, options, |pass, expr| {
        pass_snapshots.push(snapshot_pseudo(pass, expr));
    })?;
    let pipeline_telemetry = pipeline_debug_telemetry(&pipeline_output.telemetry);
    let final_types = pipeline_output.final_types.clone();

    // `bundle.code` mirrors `decompile_program`'s output for the
    // selected layer. Intermediate layers render the bare AST (or echo
    // UPLC) and skip the stub-ADT dressing; the rest of the bundle
    // (per-pass snapshots, UPLC graph) is captured either way.
    use crate::decompile::OutputLayer;
    let (rendered_body, rendered_spans, stub_prefix) = match output_layer {
        OutputLayer::Uplc | OutputLayer::UplcCanonical => {
            // Echo the decoded program with unique variable names; no pseudo
            // render → no spans. `UplcCanonical` selects the binary-nested layout.
            let canonical = output_layer == OutputLayer::UplcCanonical;
            (
                crate::decompile::render_uplc_layer(program, canonical),
                Vec::new(),
                String::new(),
            )
        }
        OutputLayer::RawPseudo | OutputLayer::PostPipeline => {
            // Bare layer render with every opt-in pinned to its
            // faithful-view default (`layer_pretty_config`'s `RenderCtx`);
            // no stub-ADT dressing.
            let (body, spans) = pipeline_output
                .expr
                .to_pretty_with_spans_and_config(crate::decompile::layer_pretty_config(show_types));
            (body, spans, String::new())
        }
        OutputLayer::PrepProfile => {
            // Cost diagnostic: the bundle's `code` is the profile table.
            // Prepared with the default context — the bundle's own render
            // context is built further down, and this layer returns before
            // the stub-ADT dressing that the real one measures.
            let prepared = crate::decompile::render_prep::prepare_for_render_with_notes(
                &pipeline_output.expr,
                &crate::decompile::RenderCtx::default(),
            );
            (
                prepared.profile.render_table(0.005),
                Vec::new(),
                String::new(),
            )
        }
        OutputLayer::PolarityReport => {
            // Diagnostic layer: the pipeline already detected + stashed the
            // church-bool polarity signals; emit the report (heuristic + the
            // executable oracle over `program`) as the body.
            (
                crate::decompile::church_polarity::render_polarity_report(
                    program,
                    &pipeline_output.church_polarity_signals,
                    &oracle_data_args,
                    oracle_tx.as_ref(),
                ),
                Vec::new(),
                String::new(),
            )
        }
        OutputLayer::Decompiled => {
            // Mirror the stub-ADT synthesis that `decompile_program`
            // runs: without it the debug bundle keeps the bare
            // `Constr<N>` placeholders the public render resolves to
            // `Unknown_*` names.
            let groups = crate::decompile::render_prep::stub_adt::collect_unresolved_constr_shapes(
                &pipeline_output.expr,
            );
            let (expr, blueprint_registry, stub_prefix) = if groups.is_empty() {
                (
                    pipeline_output.expr,
                    pipeline_output.blueprint_registry.clone(),
                    String::new(),
                )
            } else {
                let ordinals =
                    crate::decompile::render_prep::stub_adt::assign_class_ordinals(&groups);
                let mut registry: crate::decompile::BlueprintHintRegistry =
                    (*pipeline_output.blueprint_registry).clone();
                let names = crate::decompile::render_prep::stub_adt::register_stub_adts_in_registry(
                    &groups,
                    &ordinals,
                    &mut registry,
                );
                let rewritten = crate::decompile::render_prep::stub_adt::rewrite_unresolved_constrs(
                    pipeline_output.expr,
                    &names,
                );
                let prefix =
                    crate::decompile::render_prep::stub_adt::format_stub_adt_prefix(&names);
                (rewritten, std::rc::Rc::new(registry), prefix)
            };

            // The render context for exactly this render; without it
            // `bundle.code` would ignore `--decode-church-to-native`,
            // `--expect-or-fail` and `--compilable-data-access`.
            let (rendered_body, rendered_spans) = {
                // Match the public render's SC-level naming (plan version as
                // the sc channel) so the debug bundle agrees with it under
                // V1/V2 ambiguity.
                let render_ctx =
                    crate::decompile::RenderCtx::new(render_field_version, plan_version)
                        // Same guess condition the public render uses: the
                        // strict channel abstained while the plan still has
                        // a stance.
                        .with_version_guessed(
                            render_field_version.is_none() && plan_version.is_some(),
                        )
                        .with_decode_church(decode_church)
                        .with_compilable_data_access(compilable_data_access)
                        .with_strip_all_traces(strip_all_traces)
                        .with_strip_plutustx_traces(strip_plutustx_traces)
                        .with_expect_or_fail(expect_or_fail);
                render_decompiled_expr_with_registry_and_final_types(
                    &expr,
                    show_types,
                    &blueprint_registry,
                    &final_types,
                    &render_ctx,
                )
            };
            (rendered_body, rendered_spans, stub_prefix)
        }
    };
    assign_stable_ids(&mut pass_snapshots);
    // Spans anchor against `rendered_body`; the stub prefix is
    // prepended for `code` only — consumers walking
    // `code_source_map` must treat that region as unmapped
    // synthetic text, offset by the prefix length (`bundle.code`
    // length minus body length).
    let code_source_map = if matches!(output_layer, OutputLayer::Uplc | OutputLayer::UplcCanonical)
    {
        // The UPLC layer's `code` is echoed program text with no
        // pseudo-node lineage. Empty render spans would trip
        // `build_code_source_map`'s heuristic fallback, which maps the
        // snapshot root over the entire UPLC text — a spurious
        // pseudo↔UPLC correlation. RawPseudo/PostPipeline carry real
        // pseudo spans and map coherently against the final snapshot.
        Vec::new()
    } else {
        build_code_source_map(pass_snapshots.last(), &rendered_spans, &rendered_body)
    };
    let code = if stub_prefix.is_empty() {
        rendered_body
    } else {
        format!("{stub_prefix}{rendered_body}")
    };

    // 3) Build pass mappings and coarse rewrite journal
    let mut pass_mappings = Vec::new();
    let mut rewrites = builder.rewrites;

    for window in pass_snapshots.windows(2) {
        let from = &window[0];
        let to = &window[1];
        let mapping = map_snapshots(from, to);

        rewrites.push(RewriteEvent {
            pass: format!("{}->{}", from.pass, to.pass),
            input_roots: vec![from.root],
            output_roots: vec![to.root],
            reason: "Automatic node correspondence by signature".to_string(),
        });

        pass_mappings.push(mapping);
    }

    let edges = extract_edges(&builder.nodes);
    let binding_uses = extract_binding_uses(&builder.nodes);
    let ambiguities = detect_ambiguities(&builder.nodes);

    Ok(DebugBundle {
        version: "debug-ir/v3".to_string(),
        root_expr,
        nodes: builder.nodes,
        bindings: builder.bindings,
        edges,
        binding_uses,
        ambiguities,
        pass_snapshots,
        pass_mappings,
        rewrites,
        pipeline_telemetry,
        code,
        rendered_uplc_code,
        uplc_source_map: uplc_source_map.clone(),
        code_source_map,
        source_map: uplc_source_map,
    })
}

fn pipeline_debug_telemetry(telemetry: &PipelineTelemetry) -> PipelineDebugTelemetry {
    PipelineDebugTelemetry {
        fixed_point: FixedPointDebugTelemetry {
            max_iterations: telemetry.fixed_point.max_iterations,
            attempted_iterations: telemetry.fixed_point.attempted_iterations,
            converged: telemetry.fixed_point.converged,
            hit_iteration_limit: telemetry.fixed_point.hit_iteration_limit,
        },
    }
}

struct DebugBuilder {
    next_expr_id: ExprId,
    next_binding_id: BindingId,
    nodes: Vec<DebugNode>,
    bindings: Vec<BindingInfo>,
    rewrites: Vec<RewriteEvent>,
    scope: Vec<BindingId>, // 0 = nearest (DeBruijn 1)
    names: HashMap<BindingId, String>,
}

impl DebugBuilder {
    fn new() -> Self {
        Self {
            next_expr_id: 1,
            next_binding_id: 1,
            nodes: Vec::new(),
            bindings: Vec::new(),
            rewrites: Vec::new(),
            scope: Vec::new(),
            names: HashMap::new(),
        }
    }

    fn alloc_expr(&mut self, kind: DebugNodeKind, uniq_id: isize, role: &str) -> ExprId {
        let id = self.next_expr_id;
        self.next_expr_id += 1;

        self.nodes.push(DebugNode {
            id,
            kind,
            origins: vec![TermOrigin {
                uplc_uniq_id: uniq_id,
                role: role.to_string(),
            }],
            confidence: 1.0,
            notes: Vec::new(),
        });

        id
    }

    fn alloc_binding(&mut self, name_hint: &str, binder_expr: ExprId) -> BindingId {
        let id = self.next_binding_id;
        self.next_binding_id += 1;

        let base = if name_hint.is_empty() { "v" } else { name_hint };
        let display_name = format!("{}_{}", base, id);

        self.bindings.push(BindingInfo {
            id,
            name_hint: base.to_string(),
            display_name: display_name.clone(),
            binder_expr,
            scope_depth: self.scope.len(),
        });
        self.names.insert(id, display_name);

        id
    }

    fn lower(&mut self, term: &Term<NamedDeBruijn>) -> ExprId {
        match term {
            Term::Var { name, uniq_id } => {
                let index = name.index.inner();
                let binding = if index > 0 {
                    self.scope.get(index - 1).copied()
                } else {
                    None
                };

                self.alloc_expr(
                    DebugNodeKind::Var {
                        name: name.text.clone(),
                        binding,
                        debruijn_index: index,
                    },
                    *uniq_id,
                    "term",
                )
            }
            Term::Lambda {
                parameter_name,
                body,
                uniq_id,
            } => {
                let placeholder =
                    self.alloc_expr(DebugNodeKind::Error, *uniq_id, "lambda_placeholder");
                let binding = self.alloc_binding(&parameter_name.text, placeholder);

                self.scope.insert(0, binding);
                let body_id = self.lower(body);
                self.scope.remove(0);

                self.update_node_kind(
                    placeholder,
                    DebugNodeKind::Lambda {
                        binding,
                        body: body_id,
                    },
                );
                placeholder
            }
            Term::Apply {
                function,
                argument,
                uniq_id,
            } => {
                let function_id = self.lower(function);
                let argument_id = self.lower(argument);
                self.alloc_expr(
                    DebugNodeKind::Apply {
                        function: function_id,
                        argument: argument_id,
                    },
                    *uniq_id,
                    "term",
                )
            }
            Term::Constant { value, uniq_id } => self.alloc_expr(
                DebugNodeKind::Constant {
                    repr: constant_to_string(value),
                },
                *uniq_id,
                "term",
            ),
            Term::Builtin { fun, uniq_id } => self.alloc_expr(
                DebugNodeKind::Builtin {
                    name: builtin_to_name(*fun),
                },
                *uniq_id,
                "term",
            ),
            Term::Force { body, uniq_id } => {
                let body_id = self.lower(body);
                self.alloc_expr(DebugNodeKind::Force { body: body_id }, *uniq_id, "term")
            }
            Term::Delay { body, uniq_id } => {
                let body_id = self.lower(body);
                self.alloc_expr(DebugNodeKind::Delay { body: body_id }, *uniq_id, "term")
            }
            Term::Error { uniq_id } => self.alloc_expr(DebugNodeKind::Error, *uniq_id, "term"),
            Term::Constr {
                tag,
                fields,
                uniq_id,
            } => {
                let fields = fields.iter().map(|f| self.lower(f)).collect();
                self.alloc_expr(
                    DebugNodeKind::Constr { tag: *tag, fields },
                    *uniq_id,
                    "term",
                )
            }
            Term::Case {
                constr,
                branches,
                uniq_id,
            } => {
                let subject = self.lower(constr);
                let branches = branches.iter().map(|b| self.lower(b)).collect();
                self.alloc_expr(DebugNodeKind::Case { subject, branches }, *uniq_id, "term")
            }
        }
    }

    fn update_node_kind(&mut self, id: ExprId, new_kind: DebugNodeKind) {
        if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
            node.kind = new_kind;
            node.notes.push("node kind resolved".to_string());
        }
    }

    fn render(&self, id: ExprId, out: &mut String, spans: &mut Vec<SpanMap>) {
        let start = out.len();
        let Some(node) = self.nodes.iter().find(|n| n.id == id) else {
            out.push_str("<missing>");
            return;
        };

        match &node.kind {
            DebugNodeKind::Var { binding, .. } => {
                if let Some(binding) = binding {
                    out.push_str(self.display_name(*binding).as_str());
                } else {
                    out.push_str("<free>");
                }
            }
            DebugNodeKind::Lambda { binding, body } => {
                out.push_str("fn(");
                out.push_str(self.display_name(*binding).as_str());
                out.push_str(") {");
                self.render(*body, out, spans);
                out.push('}');
            }
            DebugNodeKind::Apply { function, argument } => {
                self.render(*function, out, spans);
                out.push('(');
                self.render(*argument, out, spans);
                out.push(')');
            }
            DebugNodeKind::Constant { repr } => out.push_str(repr),
            DebugNodeKind::Builtin { name } => out.push_str(name),
            DebugNodeKind::Force { body } => {
                out.push_str("force(");
                self.render(*body, out, spans);
                out.push(')');
            }
            DebugNodeKind::Delay { body } => {
                out.push_str("delay(");
                self.render(*body, out, spans);
                out.push(')');
            }
            DebugNodeKind::Error => out.push_str("error"),
            DebugNodeKind::Constr { tag, fields } => {
                out.push_str(format!("Constr<{}>(", tag).as_str());
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.render(*field, out, spans);
                }
                out.push(')');
            }
            DebugNodeKind::Case { subject, branches } => {
                out.push_str("case ");
                self.render(*subject, out, spans);
                out.push_str(" { ");
                for (i, branch) in branches.iter().enumerate() {
                    if i > 0 {
                        out.push_str("; ");
                    }
                    out.push_str(format!("{} -> ", i).as_str());
                    self.render(*branch, out, spans);
                }
                out.push_str(" }");
            }
        }

        let end = out.len();
        spans.push(SpanMap {
            expr_id: id,
            start,
            end,
        });
    }

    fn display_name(&self, binding: BindingId) -> String {
        self.names
            .get(&binding)
            .cloned()
            .unwrap_or_else(|| format!("v_{}", binding))
    }
}

fn snapshot_pseudo(pass: &str, expr: &PseudoExpr) -> PassSnapshot {
    let mut nodes = Vec::<PassNode>::new();
    let mut next_id = 1u32;
    let root = flatten_pseudo(
        expr,
        &mut next_id,
        &mut nodes,
        None,
        PseudoExpr::provenance_root_path_hash(),
    );
    let provenance = expr.provenance_graph();
    PassSnapshot {
        pass: pass.to_string(),
        root,
        nodes,
        provenance,
    }
}

/// One continuation point of the `flatten_pseudo` walk.
///
/// `Enter` numbers a node and schedules its children; `Exit` runs once every
/// child of that node has been emitted, so it can collect their ids.
enum FlattenStep<'a> {
    Enter {
        expr: &'a PseudoExpr,
        parent: Option<u32>,
        path_hash: u64,
    },
    Exit {
        expr: &'a PseudoExpr,
        id: u32,
        parent: Option<u32>,
        pseudo_node_id: PseudoNodeId,
        child_count: usize,
    },
}

/// Flatten a pseudo AST into `out` as a parent/child id graph.
fn flatten_pseudo<'a>(
    expr: &'a PseudoExpr,
    next_id: &mut u32,
    out: &mut Vec<PassNode>,
    parent: Option<u32>,
    path_hash: u64,
) -> u32 {
    let mut stack = vec![FlattenStep::Enter {
        expr,
        parent,
        path_hash,
    }];
    // Ids of finished subtrees, in emission order; an `Exit` pops exactly its
    // own children off the tail.
    let mut done = Vec::<u32>::new();

    while let Some(step) = stack.pop() {
        match step {
            FlattenStep::Enter {
                expr,
                parent,
                path_hash,
            } => {
                let id = *next_id;
                *next_id += 1;
                let pseudo_node_id = expr.provenance_node_id_from_path_hash(path_hash);

                let kids: Vec<(&'a PseudoExpr, u64)> = match expr {
                    PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
                    | PseudoExpr::Var { .. }
                    | PseudoExpr::Error { .. }
                    | PseudoExpr::Raw { .. }
                    | PseudoExpr::Data(_)
                    | PseudoExpr::HelperSymbol(_) => vec![],
                    PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                        vec![(
                            body.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        )]
                    }
                    PseudoExpr::Apply { function, args } => {
                        let mut kids = vec![(
                            function.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        )];
                        for (index, arg) in args.iter().enumerate() {
                            let child_index = index as u32 + 1;
                            kids.push((
                                arg,
                                PseudoExpr::provenance_child_path_hash(path_hash, child_index),
                            ));
                        }
                        kids
                    }
                    PseudoExpr::Let { value, body, .. } => vec![
                        (
                            value.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        ),
                        (
                            body.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 1),
                        ),
                    ],
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => vec![
                        (
                            condition.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        ),
                        (
                            then_branch.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 1),
                        ),
                        (
                            else_branch.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 2),
                        ),
                    ],
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        let mut next_child_index = 0u32;
                        let mut kids = vec![(
                            subject.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, next_child_index),
                        )];
                        next_child_index += 1;
                        for clause in clauses {
                            if matches!(clause.pattern, crate::pseudo::ast::WhenPattern::Literal(_))
                            {
                                next_child_index += 1;
                            }
                            if clause.guard.is_some() {
                                next_child_index += 1;
                            }
                            kids.push((
                                &clause.body,
                                PseudoExpr::provenance_child_path_hash(path_hash, next_child_index),
                            ));
                            next_child_index += 1;
                        }
                        kids
                    }
                    PseudoExpr::List { elements, tail } => {
                        let mut kids = Vec::new();
                        for (index, e) in elements.iter().enumerate() {
                            kids.push((
                                e,
                                PseudoExpr::provenance_child_path_hash(path_hash, index as u32),
                            ));
                        }
                        if let Some(t) = tail {
                            kids.push((
                                t.as_ref(),
                                PseudoExpr::provenance_child_path_hash(
                                    path_hash,
                                    elements.len() as u32,
                                ),
                            ));
                        }
                        kids
                    }
                    PseudoExpr::Tuple(elements) => elements
                        .iter()
                        .enumerate()
                        .map(|(index, e)| {
                            (
                                e,
                                PseudoExpr::provenance_child_path_hash(path_hash, index as u32),
                            )
                        })
                        .collect(),
                    PseudoExpr::Pair(a, b) => vec![
                        (
                            a.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        ),
                        (
                            b.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 1),
                        ),
                    ],
                    PseudoExpr::Constr { fields, .. } => fields
                        .iter()
                        .enumerate()
                        .map(|(index, f)| {
                            (
                                f,
                                PseudoExpr::provenance_child_path_hash(path_hash, index as u32),
                            )
                        })
                        .collect(),
                    PseudoExpr::FieldAccess { record, .. } => vec![(
                        record.as_ref(),
                        PseudoExpr::provenance_child_path_hash(path_hash, 0),
                    )],
                    PseudoExpr::IndexAccess { collection, .. } => vec![(
                        collection.as_ref(),
                        PseudoExpr::provenance_child_path_hash(path_hash, 0),
                    )],
                    PseudoExpr::BinOp { left, right, .. } => vec![
                        (
                            left.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        ),
                        (
                            right.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 1),
                        ),
                    ],
                    PseudoExpr::UnOp { operand, .. } => vec![(
                        operand.as_ref(),
                        PseudoExpr::provenance_child_path_hash(path_hash, 0),
                    )],
                    PseudoExpr::BuiltinCall { args, .. } => args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            (
                                arg,
                                PseudoExpr::provenance_child_path_hash(path_hash, index as u32),
                            )
                        })
                        .collect(),
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => vec![(
                        inner.as_ref(),
                        PseudoExpr::provenance_child_path_hash(path_hash, 0),
                    )],
                    PseudoExpr::Trace { message, value } => vec![
                        (
                            message.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 0),
                        ),
                        (
                            value.as_ref(),
                            PseudoExpr::provenance_child_path_hash(path_hash, 1),
                        ),
                    ],
                };

                stack.push(FlattenStep::Exit {
                    expr,
                    id,
                    parent,
                    pseudo_node_id,
                    child_count: kids.len(),
                });
                for (child, child_path_hash) in kids.into_iter().rev() {
                    stack.push(FlattenStep::Enter {
                        expr: child,
                        parent: Some(id),
                        path_hash: child_path_hash,
                    });
                }
            }
            FlattenStep::Exit {
                expr,
                id,
                parent,
                pseudo_node_id,
                child_count,
            } => {
                let children = done.split_off(done.len() - child_count);

                let (kind, summary): (String, String) = match expr {
                    PseudoExpr::Int(n) => ("int".to_string(), n.to_string()),
                    PseudoExpr::ByteArray(bs) => ("bytes".to_string(), format!("len={}", bs.len())),
                    PseudoExpr::String(s) => ("string".to_string(), s.clone()),
                    PseudoExpr::Bool(b) => ("bool".to_string(), b.to_string()),
                    PseudoExpr::Unit => ("unit".to_string(), "Void".to_string()),
                    PseudoExpr::Var { name, .. } => ("var".to_string(), name.clone()),
                    PseudoExpr::Lambda { params, .. } => (
                        "lambda".to_string(),
                        params
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(","),
                    ),
                    PseudoExpr::RecFn { name, params, .. } => (
                        "recfn".to_string(),
                        format!(
                            "{}({})",
                            name,
                            params
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(",")
                        ),
                    ),
                    PseudoExpr::Apply { args, .. } => {
                        ("apply".to_string(), format!("argc={}", args.len()))
                    }
                    PseudoExpr::Let { name, .. } => ("let".to_string(), name.clone()),
                    PseudoExpr::If { .. } => ("if".to_string(), "if".to_string()),
                    PseudoExpr::When { clauses, .. } => {
                        ("when".to_string(), format!("clauses={}", clauses.len()))
                    }
                    PseudoExpr::List { elements, .. } => {
                        ("list".to_string(), format!("len={}", elements.len()))
                    }
                    PseudoExpr::Tuple(elements) => {
                        ("tuple".to_string(), format!("len={}", elements.len()))
                    }
                    PseudoExpr::Pair(_, _) => ("pair".to_string(), "pair".to_string()),
                    PseudoExpr::Constr { tag, shape, .. } => (
                        "constr".to_string(),
                        format!("{}#{}", shape.pretty_name().unwrap_or("?"), tag),
                    ),
                    PseudoExpr::FieldAccess { selector, .. } => {
                        ("field".to_string(), selector.as_pretty_name().to_string())
                    }
                    PseudoExpr::IndexAccess { index, .. } => {
                        ("index".to_string(), index.to_string())
                    }
                    PseudoExpr::BinOp { op, .. } => ("binop".to_string(), op.symbol().to_string()),
                    PseudoExpr::UnOp { op, .. } => ("unop".to_string(), op.symbol().to_string()),
                    PseudoExpr::BuiltinCall { name, args } => {
                        ("builtin".to_string(), format!("{}({})", name, args.len()))
                    }
                    PseudoExpr::Error { message } => {
                        ("error".to_string(), message.clone().unwrap_or_default())
                    }
                    PseudoExpr::Delay(_) => ("delay".to_string(), "delay".to_string()),
                    PseudoExpr::Force(_) => ("force".to_string(), "force".to_string()),
                    PseudoExpr::Trace { .. } => ("trace".to_string(), "trace".to_string()),
                    PseudoExpr::Raw { reason, .. } => ("raw".to_string(), reason.clone()),
                    PseudoExpr::Data(_) => ("data".to_string(), "data".to_string()),
                    PseudoExpr::HelperSymbol(intrinsic) => {
                        ("helper_symbol".to_string(), format!("{:?}", intrinsic))
                    }
                };

                out.push(PassNode {
                    id,
                    pseudo_node_id,
                    stable_id: 0,
                    parent,
                    kind,
                    summary,
                    children,
                });
                done.push(id);
            }
        }
    }

    done.pop().expect("flatten_pseudo always emits a root node")
}

fn map_snapshots(from: &PassSnapshot, to: &PassSnapshot) -> PassMapping {
    let (matches, removed, added) = build_node_matches(from, to);

    PassMapping {
        from_pass: from.pass.clone(),
        to_pass: to.pass.clone(),
        matches,
        removed,
        added,
    }
}

fn node_sig(n: &PassNode) -> String {
    format!("{}|{}|{}", n.kind, n.summary, n.children.len())
}

fn assign_stable_ids(snapshots: &mut [PassSnapshot]) {
    if snapshots.is_empty() {
        return;
    }

    let mut next_stable = 1u64;
    for node in &mut snapshots[0].nodes {
        node.stable_id = next_stable;
        next_stable += 1;
    }

    for idx in 1..snapshots.len() {
        let (left, right) = snapshots.split_at_mut(idx);
        let prev = &left[idx - 1];
        let curr = &mut right[0];

        let (matches, _, _) = build_node_matches(prev, curr);
        let prev_stable: HashMap<u32, u64> =
            prev.nodes.iter().map(|n| (n.id, n.stable_id)).collect();

        let mut current_stable: HashMap<u32, u64> = HashMap::new();
        for m in matches {
            if let Some(stable) = prev_stable.get(&m.from) {
                current_stable.insert(m.to, *stable);
            }
        }

        for node in &mut curr.nodes {
            if let Some(stable_id) = current_stable.get(&node.id) {
                node.stable_id = *stable_id;
            } else {
                node.stable_id = next_stable;
                next_stable += 1;
            }
        }
    }
}

fn build_node_matches(
    from: &PassSnapshot,
    to: &PassSnapshot,
) -> (Vec<NodeMatch>, Vec<u32>, Vec<u32>) {
    let mut from_map: HashMap<String, Vec<u32>> = HashMap::new();
    let mut to_map: HashMap<String, Vec<u32>> = HashMap::new();
    let from_by_id: HashMap<u32, &PassNode> = from.nodes.iter().map(|n| (n.id, n)).collect();
    let to_by_id: HashMap<u32, &PassNode> = to.nodes.iter().map(|n| (n.id, n)).collect();

    for n in &from.nodes {
        from_map.entry(node_sig(n)).or_default().push(n.id);
    }
    for n in &to.nodes {
        to_map.entry(node_sig(n)).or_default().push(n.id);
    }

    let mut matches = Vec::new();
    let mut used_from = HashMap::<u32, bool>::new();
    let mut used_to = HashMap::<u32, bool>::new();

    // Exact signature pairing.
    for (sig, left_ids) in &from_map {
        if let Some(right_ids) = to_map.get(sig) {
            let pair_count = left_ids.len().min(right_ids.len());
            for i in 0..pair_count {
                let l = left_ids[i];
                let r = right_ids[i];
                used_from.insert(l, true);
                used_to.insert(r, true);
                matches.push(NodeMatch {
                    from: l,
                    to: r,
                    confidence: 1.0,
                    reason: format!("exact signature: {}", sig),
                });
            }
        }
    }

    // Fuzzy matching for nodes with same shape but changed details.
    let mut fuzzy_candidates: Vec<(f32, u32, u32, String)> = Vec::new();
    for left in &from.nodes {
        if used_from.contains_key(&left.id) {
            continue;
        }
        for right in &to.nodes {
            if used_to.contains_key(&right.id) {
                continue;
            }
            if left.kind != right.kind {
                continue;
            }
            if left.children.len() != right.children.len() {
                continue;
            }

            let (score, reason) = fuzzy_similarity(left, right, &from_by_id, &to_by_id);
            if score >= 0.55 {
                fuzzy_candidates.push((score, left.id, right.id, reason));
            }
        }
    }

    fuzzy_candidates.sort_by(|a, b| {
        b.0.total_cmp(&a.0)
            .then_with(|| a.1.cmp(&b.1))
            .then_with(|| a.2.cmp(&b.2))
    });

    for (score, l, r, reason) in fuzzy_candidates {
        if used_from.contains_key(&l) || used_to.contains_key(&r) {
            continue;
        }
        used_from.insert(l, true);
        used_to.insert(r, true);
        matches.push(NodeMatch {
            from: l,
            to: r,
            confidence: score,
            reason,
        });
    }

    let removed = from
        .nodes
        .iter()
        .filter(|n| !used_from.contains_key(&n.id))
        .map(|n| n.id)
        .collect();

    let added = to
        .nodes
        .iter()
        .filter(|n| !used_to.contains_key(&n.id))
        .map(|n| n.id)
        .collect();

    (matches, removed, added)
}

fn fuzzy_similarity(
    left: &PassNode,
    right: &PassNode,
    from_by_id: &HashMap<u32, &PassNode>,
    to_by_id: &HashMap<u32, &PassNode>,
) -> (f32, String) {
    if left.summary == right.summary {
        return (
            0.92,
            "fuzzy: same kind/arity with exact summary".to_string(),
        );
    }

    let left_norm = normalize_summary(&left.summary);
    let right_norm = normalize_summary(&right.summary);
    let summary_score = if left_norm == right_norm {
        0.82
    } else if left_norm.starts_with(&right_norm) || right_norm.starts_with(&left_norm) {
        0.74
    } else if left_norm
        .chars()
        .zip(right_norm.chars())
        .take(10)
        .all(|(a, b)| a == b)
    {
        0.66
    } else {
        0.56
    };

    let child_kind_match = left
        .children
        .iter()
        .zip(right.children.iter())
        .filter(|(l, r)| {
            let lk = from_by_id
                .get(l)
                .map(|n| n.kind.as_str())
                .unwrap_or_default();
            let rk = to_by_id.get(r).map(|n| n.kind.as_str()).unwrap_or_default();
            lk == rk
        })
        .count();

    let arity = left.children.len().max(1) as f32;
    let child_bonus = (child_kind_match as f32 / arity) * 0.08;
    let confidence = (summary_score + child_bonus).min(0.95);

    (
        confidence,
        format!(
            "fuzzy: same kind/arity, summary {} -> {}",
            left.summary, right.summary
        ),
    )
}

fn normalize_summary(summary: &str) -> String {
    let mut out = String::with_capacity(summary.len());
    for ch in summary.chars() {
        if ch.is_ascii_digit() {
            out.push('#');
        } else if ch.is_ascii_whitespace() {
            out.push(' ');
        } else {
            out.push(ch);
        }
    }
    out
}

fn extract_edges(nodes: &[DebugNode]) -> Vec<DebugEdge> {
    let mut edges = Vec::new();
    for node in nodes {
        match &node.kind {
            DebugNodeKind::Lambda { body, .. } => edges.push(DebugEdge {
                from_expr: node.id,
                to_expr: *body,
                role: "body".to_string(),
            }),
            DebugNodeKind::Apply { function, argument } => {
                edges.push(DebugEdge {
                    from_expr: node.id,
                    to_expr: *function,
                    role: "function".to_string(),
                });
                edges.push(DebugEdge {
                    from_expr: node.id,
                    to_expr: *argument,
                    role: "argument".to_string(),
                });
            }
            DebugNodeKind::Force { body } | DebugNodeKind::Delay { body } => {
                edges.push(DebugEdge {
                    from_expr: node.id,
                    to_expr: *body,
                    role: "body".to_string(),
                })
            }
            DebugNodeKind::Constr { fields, .. } => {
                for field in fields {
                    edges.push(DebugEdge {
                        from_expr: node.id,
                        to_expr: *field,
                        role: "field".to_string(),
                    });
                }
            }
            DebugNodeKind::Case { subject, branches } => {
                edges.push(DebugEdge {
                    from_expr: node.id,
                    to_expr: *subject,
                    role: "subject".to_string(),
                });
                for branch in branches {
                    edges.push(DebugEdge {
                        from_expr: node.id,
                        to_expr: *branch,
                        role: "branch".to_string(),
                    });
                }
            }
            DebugNodeKind::Var { .. }
            | DebugNodeKind::Constant { .. }
            | DebugNodeKind::Builtin { .. }
            | DebugNodeKind::Error => {}
        }
    }
    edges
}

fn extract_binding_uses(nodes: &[DebugNode]) -> Vec<BindingUse> {
    nodes
        .iter()
        .filter_map(|node| match &node.kind {
            DebugNodeKind::Var {
                binding: Some(binding),
                debruijn_index,
                ..
            } => Some(BindingUse {
                binding: *binding,
                use_expr: node.id,
                debruijn_index: *debruijn_index,
            }),
            _ => None,
        })
        .collect()
}

fn detect_ambiguities(nodes: &[DebugNode]) -> Vec<AmbiguityNote> {
    let mut notes = Vec::new();
    for node in nodes {
        match &node.kind {
            DebugNodeKind::Var {
                debruijn_index, ..
            } => notes.push(AmbiguityNote {
                node_id: node.id,
                category: "naming".to_string(),
                confidence: 0.45,
                alternatives: vec![
                    "original user variable name".to_string(),
                    "compiler-generated helper binding".to_string(),
                ],
                details: format!(
                    "DeBruijn index {} preserves scope, but original symbol name is not recoverable.",
                    debruijn_index
                ),
            }),
            DebugNodeKind::Apply { .. } => notes.push(AmbiguityNote {
                node_id: node.id,
                category: "call_shape".to_string(),
                confidence: 0.62,
                alternatives: vec![
                    "plain function call".to_string(),
                    "encoded operator/builtin".to_string(),
                    "constructor helper application".to_string(),
                ],
                details: "UPLC application chains are overloaded and can represent multiple high-level constructs.".to_string(),
            }),
            DebugNodeKind::Force { .. } | DebugNodeKind::Delay { .. } => notes.push(AmbiguityNote {
                node_id: node.id,
                category: "evaluation_strategy".to_string(),
                confidence: 0.58,
                alternatives: vec![
                    "type instantiation artifact".to_string(),
                    "explicit lazy thunk in user code".to_string(),
                ],
                details: "Force/Delay may come from polymorphism lowering or intentional delayed evaluation.".to_string(),
            }),
            DebugNodeKind::Constr { tag, .. } => notes.push(AmbiguityNote {
                node_id: node.id,
                category: "constructor_identity".to_string(),
                confidence: 0.55,
                alternatives: vec![
                    "custom ADT constructor".to_string(),
                    "generic Data constructor".to_string(),
                ],
                details: format!(
                    "Constructor tag {} is available, but original ADT/variant names may be missing without blueprint hints.",
                    tag
                ),
            }),
            DebugNodeKind::Case { .. } => notes.push(AmbiguityNote {
                node_id: node.id,
                category: "pattern_shape".to_string(),
                confidence: 0.57,
                alternatives: vec![
                    "high-level when/case".to_string(),
                    "desugared branch dispatch".to_string(),
                ],
                details: "Case branches can correspond to multiple source-level pattern styles.".to_string(),
            }),
            DebugNodeKind::Builtin { .. }
            | DebugNodeKind::Lambda { .. }
            | DebugNodeKind::Constant { .. }
            | DebugNodeKind::Error => {}
        }
    }
    notes
}

fn build_code_source_map(
    final_snapshot: Option<&PassSnapshot>,
    rendered_spans: &[(PseudoNodeId, SourceSpan)],
    code: &str,
) -> Vec<SpanMap> {
    let Some(snapshot) = final_snapshot else {
        return Vec::new();
    };

    let spans = build_code_source_map_from_rendered_spans(snapshot, rendered_spans, code);
    if spans.is_empty() {
        build_code_source_map_heuristic(snapshot, code)
    } else {
        spans
    }
}

fn build_code_source_map_from_rendered_spans(
    snapshot: &PassSnapshot,
    rendered_spans: &[(PseudoNodeId, SourceSpan)],
    code: &str,
) -> Vec<SpanMap> {
    let node_ids_by_pseudo: HashMap<PseudoNodeId, u32> = snapshot
        .nodes
        .iter()
        .map(|node| (node.pseudo_node_id, node.id))
        .collect();

    let mut spans = Vec::new();
    for (pseudo_node_id, span) in rendered_spans {
        let Some(expr_id) = node_ids_by_pseudo.get(pseudo_node_id) else {
            continue;
        };
        let Some((start, end)) = source_span_to_byte_range(code, *span) else {
            continue;
        };
        spans.push(SpanMap {
            expr_id: *expr_id,
            start,
            end,
        });
    }

    spans.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then_with(|| b.end.cmp(&a.end))
            .then_with(|| a.expr_id.cmp(&b.expr_id))
    });
    spans.dedup_by(|a, b| a.expr_id == b.expr_id && a.start == b.start && a.end == b.end);
    spans
}

fn build_code_source_map_heuristic(snapshot: &PassSnapshot, code: &str) -> Vec<SpanMap> {
    let mut spans = Vec::<SpanMap>::new();
    if !code.is_empty() {
        spans.push(SpanMap {
            expr_id: snapshot.root,
            start: 0,
            end: code.len(),
        });
    }

    let node_by_id: HashMap<u32, &PassNode> = snapshot.nodes.iter().map(|n| (n.id, n)).collect();
    let mut leaf_spans: HashMap<u32, (usize, usize)> = HashMap::new();
    let mut cursor = 0usize;

    for node in snapshot.nodes.iter().filter(|n| n.children.is_empty()) {
        if let Some((start, end)) = locate_node_span(node, code, cursor) {
            cursor = end;
            leaf_spans.insert(node.id, (start, end));
            spans.push(SpanMap {
                expr_id: node.id,
                start,
                end,
            });
        }
    }

    for node in snapshot.nodes.iter().filter(|n| !n.children.is_empty()) {
        let child_ranges: Vec<(usize, usize)> = node
            .children
            .iter()
            .filter_map(|child| leaf_spans.get(child).copied())
            .collect();

        if let (Some(min_start), Some(max_end)) = (
            child_ranges.iter().map(|(s, _)| *s).min(),
            child_ranges.iter().map(|(_, e)| *e).max(),
        ) {
            spans.push(SpanMap {
                expr_id: node.id,
                start: min_start,
                end: max_end,
            });
        } else if let Some(parent_id) = node.parent
            && let Some(parent) = node_by_id.get(&parent_id)
            && let Some((start, end)) = locate_node_span(parent, code, 0)
        {
            spans.push(SpanMap {
                expr_id: node.id,
                start,
                end,
            });
        }
    }

    spans.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then_with(|| b.end.cmp(&a.end))
            .then_with(|| a.expr_id.cmp(&b.expr_id))
    });
    spans.dedup_by(|a, b| a.expr_id == b.expr_id && a.start == b.start && a.end == b.end);
    spans
}

fn source_span_to_byte_range(code: &str, span: SourceSpan) -> Option<(usize, usize)> {
    let start = line_col_to_byte_offset(code, span.start_line, span.start_col)?;
    let end_inclusive = line_col_to_byte_offset(code, span.end_line, span.end_col)?;
    Some((start, end_inclusive.saturating_add(1).min(code.len())))
}

fn line_col_to_byte_offset(code: &str, target_line: u32, target_col: u32) -> Option<usize> {
    if target_line == 0 || target_col == 0 {
        return None;
    }

    let mut line = 1u32;
    let mut col = 1u32;

    for (offset, byte) in code.bytes().enumerate() {
        if line == target_line && col == target_col {
            return Some(offset);
        }

        if byte == b'\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }

    if line == target_line && col == target_col {
        Some(code.len())
    } else {
        None
    }
}

fn locate_node_span(node: &PassNode, code: &str, from: usize) -> Option<(usize, usize)> {
    for token in node_probe_tokens(node) {
        if token.is_empty() {
            continue;
        }
        if let Some(start) = find_token(code, &token, from).or_else(|| find_token(code, &token, 0))
        {
            return Some((start, start + token.len()));
        }
    }
    None
}

fn find_token(haystack: &str, token: &str, from: usize) -> Option<usize> {
    if from >= haystack.len() {
        return None;
    }
    haystack[from..].find(token).map(|idx| from + idx)
}

fn node_probe_tokens(node: &PassNode) -> Vec<String> {
    match node.kind.as_str() {
        "var" => vec![node.summary.clone()],
        "int" => vec![node.summary.clone()],
        "string" => vec![
            format!("@\"{}\"", node.summary.replace('"', "\\\"")),
            format!("\"{}\"", node.summary.replace('"', "\\\"")),
        ],
        "bool" => vec![
            if node.summary == "true" {
                "True".to_string()
            } else if node.summary == "false" {
                "False".to_string()
            } else {
                node.summary.clone()
            },
            node.summary.clone(),
        ],
        "unit" => vec!["Void".to_string()],
        "builtin" => {
            let name = node
                .summary
                .split('(')
                .next()
                .unwrap_or(node.summary.as_str());
            vec![name.to_string(), node.summary.clone()]
        }
        "constr" => {
            let name = node
                .summary
                .split('#')
                .next()
                .unwrap_or(node.summary.as_str());
            vec![name.to_string(), node.summary.clone()]
        }
        "error" => vec!["fail".to_string(), "error".to_string()],
        "raw" => vec![node.summary.clone()],
        _ => Vec::new(),
    }
}

fn builtin_to_name(builtin: DefaultFunction) -> String {
    builtin.aiken_name()
}

fn constant_to_string(c: &Constant) -> String {
    match c {
        Constant::Integer(i) => i.to_string(),
        Constant::ByteString(bytes) => {
            let hex = hex::encode(bytes);
            format!("#\"{}\"", hex)
        }
        Constant::String(s) => format!("\"{}\"", s.replace('"', "\\\"")),
        Constant::Bool(b) => {
            if *b {
                "True".to_string()
            } else {
                "False".to_string()
            }
        }
        Constant::Unit => "Void".to_string(),
        Constant::Data(_) => "Data(...)".to_string(),
        Constant::ProtoList(_, xs) => format!("List(len={})", xs.len()),
        Constant::ProtoPair(_, _, _, _) => "Pair(...)".to_string(),
        Constant::Bls12_381G1Element(_) => "G1Element(...)".to_string(),
        Constant::Bls12_381G2Element(_) => "G2Element(...)".to_string(),
        Constant::Bls12_381MlResult(_) => "MillerLoopResult(...)".to_string(),
    }
}

#[cfg(test)]
mod tests;
