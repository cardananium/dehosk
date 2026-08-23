//! Names taken from the script's own `trace` messages.
//!
//! A trace string is the one place a compiled script carries text its
//! author wrote, so a helper that traces `"insufficient funds"` can be
//! named after it — subject to `trace_message_to_name`'s sanitising.

use super::*;

/// Extract naming hints from trace messages in the body.
pub(super) fn hint_from_trace_messages(body: &PseudoExpr) -> Option<String> {
    let mut traces = Vec::new();
    collect_trace_messages(body, &mut traces, 0);

    if traces.is_empty() {
        return None;
    }

    let msg = &traces[0];
    Some(trace_message_to_name(msg))
}

/// Convert a trace message string to a snake_case function name.
pub(super) fn trace_message_to_name(msg: &str) -> String {
    // Common patterns in trace messages
    let lower = msg.to_lowercase();

    if lower.contains("signer") && lower.contains("claim") {
        return "check_signer_eligibility".to_string();
    }
    if lower.contains("validity") && lower.contains("range") {
        return "check_validity_range".to_string();
    }
    if lower.contains("insufficient") && lower.contains("claim") {
        return "check_claim_amount".to_string();
    }
    if lower.contains("value") && lower.contains("match") {
        return "check_value_match".to_string();
    }
    if lower.contains("expect") {
        return "check_expectation".to_string();
    }

    // Generic: take first few words, convert to snake_case
    let words: Vec<&str> = msg.split_whitespace().take(4).collect();

    if words.is_empty() {
        return "traced_fn".to_string();
    }

    let name = words
        .iter()
        .map(|w| {
            w.chars()
                .filter(|c| c.is_alphanumeric() || *c == '_')
                .collect::<String>()
                .to_lowercase()
        })
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>()
        .join("_");

    if name.is_empty() {
        "traced_fn".to_string()
    } else {
        // Prefix with "check_" if it looks like a validation message
        if lower.contains("not") || lower.contains("invalid") || lower.contains("exceed") {
            format!("check_{}", name)
        } else {
            name
        }
    }
}

/// Collect trace message strings from the body.
pub(super) fn collect_trace_messages(expr: &PseudoExpr, traces: &mut Vec<String>, depth: usize) {
    if depth > 50 {
        return;
    }
    match expr {
        PseudoExpr::Trace { message, value } => {
            if let PseudoExpr::String(msg) = message.as_ref() {
                traces.push(msg.clone());
            }
            collect_trace_messages(value, traces, depth + 1);
        }
        PseudoExpr::Let { value, body, .. } => {
            collect_trace_messages(value, traces, depth + 1);
            collect_trace_messages(body, traces, depth + 1);
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_trace_messages(condition, traces, depth + 1);
            collect_trace_messages(then_branch, traces, depth + 1);
            collect_trace_messages(else_branch, traces, depth + 1);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            collect_trace_messages(subject, traces, depth + 1);
            for c in clauses {
                collect_trace_messages(&c.body, traces, depth + 1);
            }
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            collect_trace_messages(body, traces, depth + 1);
        }
        _ => {}
    }
}
