//! Bidirectional source map between UPLC, MidExpr, and decompiled source.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::pseudo::ast::PseudoNodeId;
use crate::pseudo::mid::expr_id::{MidExprId, SourceSpan};
use crate::pseudo::var_id::VarId;
use uplc::ast::{NamedDeBruijn, Term};

/// Bidirectional mapping between UPLC execution positions and decompiled source.
#[derive(Debug, Default)]
pub(crate) struct SourceMap {
    /// UPLC uniq_id → source span in decompiled code.
    pub uplc_to_source: HashMap<isize, SourceSpan>,
    /// Source line → list of UPLC uniq_ids that map to this line.
    pub line_to_uplc: HashMap<u32, Vec<isize>>,
    /// MidExprId → UPLC uniq_ids (may be many-to-one after optimization).
    pub mid_to_uplc: HashMap<MidExprId, Vec<isize>>,
    /// MidExprIds in MIR traversal order.
    pub mid_order: Vec<MidExprId>,
    /// MidExprId → source span.
    pub mid_to_source: HashMap<MidExprId, SourceSpan>,
    /// Initial lowered pseudo-node → originating MidExprIds.
    pub initial_pseudo_to_mid: HashMap<PseudoNodeId, Vec<MidExprId>>,
    /// Final rendered pseudo-node → originating MidExprIds after pass projection.
    pub final_pseudo_to_mid: HashMap<PseudoNodeId, Vec<MidExprId>>,
    /// VarId → display name (for variable inspection).
    pub var_names: HashMap<VarId, String>,
    /// Mids with NO HEIR: every pseudo node that lowered them was deleted
    /// before rendering, so their span reached them only by lineage
    /// projection donating them to a surviving ancestor, and a donation
    /// guarantees COVERAGE, never POSITION.
    ///
    /// Populated by the render-prep projection; empty where nothing
    /// projected, which makes the abstain channel a no-op there rather than
    /// a guess.
    pub heirless_mids: HashSet<MidExprId>,
    /// Terms whose provenance DECLINED its donated position — see
    /// [`SourceMap::apply_abstain_channel`].
    ///
    /// Kept after the withdrawal because saturation must not hand them a
    /// position either: a saturated span is a neighbour's, propagated by
    /// graph distance, so refilling a hole opened *because* the position was
    /// not evidence just swaps one unfounded line for another.
    pub abstained_uplc_ids: HashSet<isize>,
}

/// The only kinds the abstain channel will withdraw: the INTERSECTION of two
/// sets this module and the step bridge already maintain for other reasons.
///
///  * `StepBridge::at_statement_term` — {Apply, Case, Constr, Error} — the
///    kinds a navigation control can stop on. Abstaining outside it removes no
///    stop, because nothing stops there, but it still removes breakpoint
///    evidence: breakpoints are deliberately NOT narrowed by
///    `at_statement_term`. A wider set pays the full cost for none of the
///    benefit.
///
///  * `FlatTerm::is_structural` — {Apply, Force, Delay, Error} — the kinds that
///    print nothing of their own and can only ever inherit a position. This is
///    what makes the withdrawal SOUND rather than merely cheap: a term with no
///    surface cannot be the construct a block header opens, so a block-scale
///    position it holds was necessarily inherited, and if (a) says nothing it
///    inherited from is still standing then the position is a donation and
///    nothing else.
///
/// The intersection is {Apply, Error}. The excluded kinds are exactly Case and
/// Constr, which `narrow_uplc_spans_to_subtree_hull` already refuses to pull
/// down for the same reason: a `Case` term IS the `when` and a `Constr` the
/// constructor call that wraps its block, so for those two the withdrawn
/// position can be the term's own surface, and losing a position known to be
/// right is worse than keeping one that merely reads wide.
fn is_abstainable_kind(term: &Term<NamedDeBruijn>) -> bool {
    matches!(term, Term::Apply { .. } | Term::Error { .. })
}

/// Minimum span height, in lines, for a donated position to be withdrawn.
///
/// A shorter donated span is not a block header; withdrawing it would remove
/// an honest small position. Raising the threshold does not make the channel
/// safer: the taller a span, the closer its start creeps to line 1, which is
/// genuinely correct for what the pipeline prints at the top of a file, so
/// the ratio of correct-to-incorrect withdrawals gets WORSE as it rises.
const ABSTAIN_MIN_SPAN_HEIGHT: u32 = 10;

/// What one run of the stepping span sequence did.
#[derive(Debug, Default, Clone)]
pub(crate) struct SteppingSpanResolution {
    /// Terms pulled onto the region their own subtree proves.
    pub pulled: usize,
    /// Terms whose donated position was withdrawn.
    pub abstained: usize,
    /// Terms saturation gave a neighbour's span to.
    pub saturated: usize,
    /// `uplc_to_source` as narrowing and abstention left it: every position
    /// that is a rendered-span FACT, before saturation guessed anything.
    ///
    /// Returned rather than re-derived by each caller because "the moment
    /// before saturation" is a property of this sequence — the step bridge's
    /// `directly_mapped` set and the span-anatomy instrument's
    /// `uplc_after_narrow` stage must key off the same instant, or the
    /// instrument describes a pipeline the product does not run.
    pub pre_saturation: HashMap<isize, SourceSpan>,
}

impl SourceMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a MidExprId with its UPLC origins (from provenance).
    pub(crate) fn register_mid(&mut self, mid_id: MidExprId, uplc_ids: &[isize]) {
        if !self.mid_to_uplc.contains_key(&mid_id) {
            self.mid_order.push(mid_id);
        }
        self.mid_to_uplc.insert(mid_id, uplc_ids.to_vec());
    }

    /// Set the source span for a MidExprId (called during pretty-printing).
    pub(crate) fn set_mid_span(&mut self, mid_id: MidExprId, span: SourceSpan) {
        self.mid_to_source.insert(mid_id, span);
        if let Some(uplc_ids) = self.mid_to_uplc.get(&mid_id) {
            for uid in uplc_ids.clone() {
                self.register_uplc_span(uid, span);
            }
        }
    }

    /// Register a direct UPLC uniq_id → source span mapping.
    ///
    /// Re-registering an id under a span starting on a different line
    /// withdraws it from the previous line's entry — `line_to_uplc` mirrors
    /// `uplc_to_source` exactly, so a breakpoint lookup never sees an id on
    /// a line its authoritative span no longer starts on.
    pub(crate) fn register_uplc_span(&mut self, uplc_id: isize, span: SourceSpan) {
        // An abstained term declined its position; nothing may hand it back.
        // The saturation write-back already skips these, but that is one site:
        // this guard is the invariant itself, so no other writer can silently
        // re-register an id recorded as heirless. Inert until the channel
        // runs, because the set is populated after every legitimate write.
        if self.abstained_uplc_ids.contains(&uplc_id) {
            return;
        }
        if let Some(previous) = self.uplc_to_source.insert(uplc_id, span)
            && previous.start_line != span.start_line
            && let Some(previous_entry) = self.line_to_uplc.get_mut(&previous.start_line)
        {
            previous_entry.retain(|id| *id != uplc_id);
            if previous_entry.is_empty() {
                self.line_to_uplc.remove(&previous.start_line);
            }
        }
        let line_entry = self.line_to_uplc.entry(span.start_line).or_default();
        if !line_entry.contains(&uplc_id) {
            line_entry.push(uplc_id);
        }
    }

    /// Register the lowered pseudo-node corresponding to a MidExpr.
    pub(crate) fn register_initial_pseudo_mid(
        &mut self,
        pseudo_node_id: PseudoNodeId,
        mid_id: MidExprId,
    ) {
        let mids = self
            .initial_pseudo_to_mid
            .entry(pseudo_node_id)
            .or_default();
        if !mids.contains(&mid_id) {
            mids.push(mid_id);
        }
    }

    /// Replace projected final pseudo-node lineage.
    pub(crate) fn set_final_pseudo_to_mid(
        &mut self,
        final_pseudo_to_mid: HashMap<PseudoNodeId, Vec<MidExprId>>,
    ) {
        self.final_pseudo_to_mid = final_pseudo_to_mid;
    }

    pub(crate) fn register_var(&mut self, var: VarId, name: String) {
        self.var_names.insert(var, name);
    }

    pub(crate) fn source_for_uplc(&self, uplc_id: isize) -> Option<&SourceSpan> {
        self.uplc_to_source.get(&uplc_id)
    }

    /// Look up UPLC ids for a source line.
    ///
    /// Keyed by span START line only. A breakpoint placed on the interior
    /// line of a multi-line span will find nothing here; use
    /// [`SourceMap::uplc_covering_line`] to resolve those.
    pub(crate) fn uplc_for_line(&self, line: u32) -> &[isize] {
        self.line_to_uplc
            .get(&line)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Look up UPLC ids whose span COVERS a source line (start, interior, or
    /// end), most specific span first.
    ///
    /// `line_to_uplc` keys only `span.start_line`, so a multi-line construct
    /// (a `when` block, a wrapped `let` value) registers nothing on its
    /// interior lines and a breakpoint lookup there comes up empty. This
    /// query resolves such a line to the ids of every span containing it,
    /// ordered by (line height, column width) so the tightest enclosing
    /// construct comes first and a caller can snap a breakpoint to the most
    /// specific unit of execution. Interior lines are deliberately NOT
    /// registered eagerly in `line_to_uplc`: whole-program wrapper spans
    /// would fan every id across hundreds of lines, misleading exact-line
    /// consumers.
    ///
    /// Consumed by `StepBridge::breakpoint_anchor_line`, which takes the
    /// tightest *directly mapped* covering id and uses its span as the bound
    /// on where a breakpoint set on an interior line may be armed.
    pub(crate) fn uplc_covering_line(&self, line: u32) -> Vec<isize> {
        let mut covering: Vec<(u32, u32, isize)> = self
            .uplc_to_source
            .iter()
            .filter(|(_, span)| span.start_line <= line && line <= span.end_line)
            .map(|(uplc_id, span)| {
                let height = span.end_line - span.start_line;
                let width = if height == 0 {
                    span.end_col.saturating_sub(span.start_col)
                } else {
                    u32::MAX
                };
                (height, width, *uplc_id)
            })
            .collect();
        covering.sort_unstable();
        covering
            .into_iter()
            .map(|(_, _, uplc_id)| uplc_id)
            .collect()
    }

    /// Narrow every UPLC term's span to the tightest ancestor bound, so
    /// a term stops reporting the header of a block it merely sits in.
    ///
    /// One MidExpr often owns many UPLC terms and inherits one block
    /// span. `line_to_uplc` keys `span.start_line`, so a leaf `Var`
    /// then claims the `fn` header. A term renders *within* its parent,
    /// so a span that strictly contains the parent's cannot be its own
    /// surface. The walk carries the nearest mapped ancestor down and
    /// replaces any span that strictly contains it.
    ///
    /// The replacement is always a subset of what the term already
    /// claimed — unlike `saturate_uplc_term_spans`, which can move a
    /// term anywhere. Children are not consulted: definitions are
    /// hoisted, so a child's span may sit in another region.
    ///
    /// `Lambda` is exempt: the pipeline relocates it to a top-level
    /// `fn` / `rec fn`, so a wider span is the definition, not an
    /// inversion. Its span becomes the bound for its subtree.
    ///
    /// Run before `saturate_uplc_term_spans`. The proportional-index
    /// fallback (`finalize_source_map`) does not: every fabricated
    /// span is one whole line. `mid_to_source` stays — the mid really
    /// was carried by that block-scale node.
    ///
    /// Returns how many terms were narrowed.
    pub(crate) fn narrow_uplc_spans_to_term_tree(&mut self, term: &Term<NamedDeBruijn>) -> usize {
        let mut narrowed = 0;
        // Pre-order walk: a node is visited only after every ancestor, so the
        // bound it sees is already narrowed.
        let mut stack: Vec<(&Term<NamedDeBruijn>, Option<SourceSpan>)> = vec![(term, None)];
        while let Some((current, bound)) = stack.pop() {
            let id = term_uniq_id(current);
            let own = self.uplc_to_source.get(&id).copied();
            let effective = match (own, bound) {
                (Some(own_span), Some(bound_span))
                    if !is_hoistable_definition(current)
                        && bound_span != own_span
                        && span_contains(own_span, bound_span) =>
                {
                    self.register_uplc_span(id, bound_span);
                    narrowed += 1;
                    Some(bound_span)
                }
                // The term's own span is the tightest thing known about its
                // subtree, including when it overlaps the bound only partly or
                // not at all (a hoisted definition).
                (Some(own_span), _) => Some(own_span),
                // A hoistable definition ends the bound even when it carries no
                // span of its own: its body renders at the hoisted site, so the
                // call site's span is not evidence about anything inside it.
                // Checking hoistability only in the mapped arm above would leak
                // the call-site bound past an unmapped lambda onto its body.
                (None, _) if is_hoistable_definition(current) => None,
                // Unmapped: keep carrying the nearest mapped ancestor's bound
                // so an inversion deeper down is still caught.
                (None, carried) => carried,
            };
            match current {
                Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
                    stack.push((body, effective));
                }
                Term::Apply {
                    function, argument, ..
                } => {
                    stack.push((function, effective));
                    stack.push((argument, effective));
                }
                Term::Constr { fields, .. } => {
                    for field in fields.iter() {
                        stack.push((field, effective));
                    }
                }
                Term::Case {
                    constr, branches, ..
                } => {
                    stack.push((constr, effective));
                    for branch in branches.iter() {
                        stack.push((branch, effective));
                    }
                }
                Term::Var { .. }
                | Term::Constant { .. }
                | Term::Builtin { .. }
                | Term::Error { .. } => {}
            }
        }
        narrowed
    }

    /// Narrow every structural term onto the region its subtree already
    /// proves — the downward mirror of
    /// [`Self::narrow_uplc_spans_to_term_tree`].
    ///
    /// The upward pass cannot help when a parent holds the same
    /// block-scale span: nothing above is tighter, yet the term is
    /// not the block's head. Evidence is on descendants that claimed
    /// tight nodes. Bottom-up:
    ///
    /// * No printed surface (`Apply` / `Force` / `Delay` / `Error`).
    ///   A `Case` is the `when` it heads and a `Constr` its call, so
    ///   a block header can be their line.
    /// * Parent holds the *identical* span (proof the term is not
    ///   the head). A different parent span may be a `let` value
    ///   that really opens the header.
    /// * Replacement is the hull of descendant spans *strictly
    ///   inside* the term's own — a subset, never a relocate.
    /// * A `Case`/`Constr` descendant still holding the identical
    ///   span vetoes: pulling the ancestor below them leaves them
    ///   wider than their parent, and the second upward pass then
    ///   drags them off the header. `Lambda` is not in that set —
    ///   it prints as a hoisted definition.
    ///
    /// A hoisted descendant sits outside the term's span and fails
    /// containment. `Lambda` and its body are skipped even when
    /// inside, so `Apply(Lambda, value)` (`let`) keeps only the
    /// bound value.
    ///
    /// Run between the two upward narrowings. `mid_to_source` stays.
    ///
    /// Returns how many terms were pulled down.
    pub(crate) fn narrow_uplc_spans_to_subtree_hull(
        &mut self,
        term: &Term<NamedDeBruijn>,
    ) -> usize {
        let moves = self.uplc_terms_pullable_to_subtree_hull(term);
        for (id, span) in &moves {
            self.register_uplc_span(*id, *span);
        }
        moves.len()
    }

    /// Every move [`Self::narrow_uplc_spans_to_subtree_hull`] would make, as
    /// `(term id, span it would be pulled onto)`, without making any of them.
    ///
    /// Decision and post-condition are the same code, so they cannot drift
    /// apart. After the pass has run this must be empty: a structural term
    /// whose parent holds the identical block span while its own subtree proves
    /// a tighter region is reporting a header line provably not about it.
    pub(crate) fn uplc_terms_pullable_to_subtree_hull(
        &self,
        term: &Term<NamedDeBruijn>,
    ) -> Vec<(isize, SourceSpan)> {
        let flat = flatten_uplc_term_tree(term);
        let mut spans: Vec<Option<SourceSpan>> = flat
            .iter()
            .map(|node| self.uplc_to_source.get(&node.id).copied())
            .collect();

        // Bottom-up: a node is visited only after every node in its subtree, so
        // a descendant already pulled down contributes its tighter span. Pre-order
        // indexing makes that a plain reverse scan, and makes each subtree a
        // contiguous range, so a hull costs one linear pass over that range.
        let mut changed: Vec<usize> = Vec::new();
        for index in (0..flat.len()).rev() {
            let node = &flat[index];
            if !node.is_structural {
                continue;
            }
            let (Some(own), Some(parent_index)) = (spans[index], node.parent) else {
                continue;
            };
            if spans[parent_index] != Some(own) {
                continue;
            }

            let mut hull: Option<SourceSpan> = None;
            let mut vetoed = false;
            let subtree_end = index + node.subtree_len;
            let mut descendant = index + 1;
            while descendant < subtree_end {
                if flat[descendant].is_definition {
                    // A `Lambda` prints three ways and its KIND tells them
                    // apart in none of them:
                    //
                    //  * CONTINUATION — the function child of an `Apply` is
                    //    this pipeline's `let`: `Apply(Lambda(x, rest), v)`
                    //    is `let x = v`, so the lambda is the statements that
                    //    FOLLOW — nested in the let's span, not its surface.
                    //  * HOISTED — lifted to a top-level `fn` / `rec fn`, so
                    //    its span lies outside this term's entirely.
                    //  * INLINE — printed in place as a call argument, a
                    //    constructor field or a branch body (`fn(x) { .. }`),
                    //    so its span lies inside this term's AND is part of
                    //    the surface this term covers.
                    //
                    // Only the third is evidence: discarding it lets the hull
                    // fall short of lines the term genuinely spans, so the
                    // term reports a position that skips its own argument.
                    // Position rules out the continuation (nested too, so
                    // containment alone cannot), containment the hoist.
                    let inline_span = if flat[descendant].is_apply_function {
                        None
                    } else {
                        spans[descendant]
                            .filter(|inner| *inner != own && span_contains(own, *inner))
                    };
                    let Some(inline_span) = inline_span else {
                        descendant += flat[descendant].subtree_len;
                        continue;
                    };
                    // Its own span already covers its whole body, so it counts
                    // once and the rest of its subtree is skipped.
                    hull = Some(match hull {
                        Some(current) => span_hull(current, inline_span),
                        None => inline_span,
                    });
                    descendant += flat[descendant].subtree_len;
                    continue;
                }
                if let Some(inner) = spans[descendant] {
                    if inner == own {
                        // A `when` or a constructor still holding this exact
                        // span may be the construct the header opens, the one
                        // descendant kind for which that is true. Pulling the
                        // structural term below it would leave it wider than
                        // its own parent, and the cascade re-narrow would
                        // drag it off the header its surface is really on.
                        if flat[descendant].is_block_surface {
                            vetoed = true;
                            break;
                        }
                    } else if span_contains(own, inner) {
                        hull = Some(match hull {
                            Some(current) => span_hull(current, inner),
                            None => inner,
                        });
                    }
                }
                descendant += 1;
            }

            if let Some(hull) = hull
                && !vetoed
                && hull != own
            {
                spans[index] = Some(hull);
                changed.push(index);
            }
        }

        changed.reverse();
        changed
            .into_iter()
            .filter_map(|index| spans[index].map(|span| (flat[index].id, span)))
            .collect()
    }

    /// Bound every term by its ancestors, pull the sandwiched ones onto the
    /// region their own subtree proves, then re-narrow.
    ///
    /// Exactly one round, deliberately. The second upward narrow tightens
    /// leaves that were still riding the block anchor, and a tightened leaf is
    /// fresh evidence for its ancestors, so further pull-downs remain available
    /// when this returns — [`Self::uplc_terms_pullable_to_subtree_hull`] still
    /// reports some, and iterating to a fixed point does converge to none.
    ///
    /// It is not iterated, because of what the extra rounds move. A term that
    /// *heads* its block — the `Apply` that is a `let`'s whole value, the
    /// `Force` that is the whole `if` — is excluded here by the parent-holds-
    /// the-same-span gate, the only evidence available that it is not the
    /// construct the header opens. Iterating manufactures that condition: once
    /// a parent has been pulled down onto such a term, the parent holds its
    /// span and the gate admits it. Rounds two and beyond buy their further
    /// block-header removals with exactly those moves — moves the evidence
    /// cannot adjudicate, in precisely the class where a header-anchoring fix
    /// is most likely to make the cursor worse. The residue is left visible
    /// rather than consumed.
    ///
    /// Returns the number of terms pulled down.
    pub(crate) fn resolve_uplc_spans_in_term_tree(&mut self, term: &Term<NamedDeBruijn>) -> usize {
        self.narrow_uplc_spans_to_term_tree(term);
        let pulled = self.narrow_uplc_spans_to_subtree_hull(term);
        self.narrow_uplc_spans_to_term_tree(term);
        pulled
    }

    /// Terms whose span still strictly contains their parent's span, as
    /// `(term id, is_hoistable_definition)`.
    ///
    /// The measurement behind [`Self::narrow_uplc_spans_to_term_tree`]: a term
    /// reporting a line from a region wider than its own parent's is anchored
    /// on an enclosing block's header rather than on itself. After narrowing,
    /// every remaining entry must be flagged `true` — a lambda printed as its
    /// own hoisted definition, the one legitimate way this relation arises.
    pub(crate) fn uplc_span_tree_inversions(
        &self,
        term: &Term<NamedDeBruijn>,
    ) -> Vec<(isize, bool)> {
        let mut out = Vec::new();
        let mut stack: Vec<(&Term<NamedDeBruijn>, Option<SourceSpan>)> = vec![(term, None)];
        while let Some((current, parent_span)) = stack.pop() {
            let id = term_uniq_id(current);
            let own = self.uplc_to_source.get(&id).copied();
            if let (Some(own_span), Some(outer)) = (own, parent_span)
                && outer != own_span
                && span_contains(own_span, outer)
            {
                out.push((id, is_hoistable_definition(current)));
            }
            // Same hoist boundary the narrowing pass applies, so the two agree
            // on what counts as an inversion: a hoistable definition never
            // passes an outer bound into its body, mapped or not.
            let carried = if is_hoistable_definition(current) {
                own
            } else {
                own.or(parent_span)
            };
            match current {
                Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
                    stack.push((body, carried));
                }
                Term::Apply {
                    function, argument, ..
                } => {
                    stack.push((function, carried));
                    stack.push((argument, carried));
                }
                Term::Constr { fields, .. } => {
                    for field in fields.iter() {
                        stack.push((field, carried));
                    }
                }
                Term::Case {
                    constr, branches, ..
                } => {
                    stack.push((constr, carried));
                    for branch in branches.iter() {
                        stack.push((branch, carried));
                    }
                }
                Term::Var { .. }
                | Term::Constant { .. }
                | Term::Builtin { .. }
                | Term::Error { .. } => {}
            }
        }
        out.sort_unstable();
        out
    }

    /// Densify UPLC -> source coverage for a concrete original UPLC tree.
    ///
    /// The rendered lineage is legitimately sparse: many UPLC nodes collapse
    /// into a single MIR or pseudo expression, yet stepping needs every
    /// original `uniq_id` in the concrete term tree to resolve directly. This
    /// pass seeds from the already-mapped ids and propagates their spans
    /// across the UPLC tree by nearest graph distance, giving a deterministic
    /// dense map over the original term.
    pub(crate) fn saturate_uplc_term_spans(&mut self, term: &Term<NamedDeBruijn>) -> usize {
        let mut nodes = Vec::new();
        let mut adjacency = HashMap::<isize, Vec<isize>>::new();
        collect_uplc_term_graph(term, &mut nodes, &mut adjacency);

        let mut assigned = HashMap::<isize, SourceSpan>::new();
        let mut queue = VecDeque::<isize>::new();

        for node_id in nodes.iter().copied() {
            if let Some(span) = self.uplc_to_source.get(&node_id).copied() {
                assigned.insert(node_id, span);
                queue.push_back(node_id);
            }
        }

        if queue.is_empty() {
            return 0;
        }

        while let Some(node_id) = queue.pop_front() {
            let span = assigned[&node_id];
            if let Some(neighbors) = adjacency.get(&node_id) {
                for &neighbor_id in neighbors {
                    if assigned.contains_key(&neighbor_id) {
                        continue;
                    }
                    assigned.insert(neighbor_id, span);
                    queue.push_back(neighbor_id);
                }
            }
        }

        let mut inserted = 0;
        for node_id in nodes {
            if self.uplc_to_source.contains_key(&node_id) {
                continue;
            }
            // An abstention is a DECISION, not a gap. The abstained node was
            // still seeded and traversed above, so spans keep flowing THROUGH
            // it to genuinely unmapped terms beyond; filtering in the seed
            // loop or the BFS instead would cut the graph at every abstention
            // and hand the terms past it a span from some unrelated direction,
            // manufacturing the span-tree inversions narrowing had already
            // eliminated.
            if self.abstained_uplc_ids.contains(&node_id) {
                continue;
            }
            if let Some(span) = assigned.get(&node_id).copied() {
                self.register_uplc_span(node_id, span);
                inserted += 1;
            }
        }

        inserted
    }

    /// Terms whose provenance declined its donated position.
    pub(crate) fn abstained_uplc_ids(&self) -> &HashSet<isize> {
        &self.abstained_uplc_ids
    }

    /// For each UPLC term, the LAST mid that stamps a span onto it.
    ///
    /// `finalize_source_map_from_rendered_spans` walks `mid_order` calling
    /// [`Self::set_mid_span`], which reaches [`Self::register_uplc_span`] and
    /// OVERWRITES: a term owned by several mids reports the span of the last
    /// one to write, and only that mid's heirship decides what the term says.
    /// Replaying the order rather than assuming a term's mids agree keeps the
    /// question about the claim that exists, not one that was overwritten.
    ///
    /// Mids absent from `mid_to_source` never wrote and are skipped, exactly as
    /// the finalizer skips them.
    fn span_writers_per_term(&self) -> HashMap<isize, Vec<(MidExprId, SourceSpan)>> {
        let mut writers = HashMap::<isize, Vec<(MidExprId, SourceSpan)>>::new();
        for mid_id in &self.mid_order {
            let Some(mid_span) = self.mid_to_source.get(mid_id).copied() else {
                continue;
            };
            if let Some(uplc_ids) = self.mid_to_uplc.get(mid_id) {
                for uplc_id in uplc_ids {
                    writers
                        .entry(*uplc_id)
                        .or_default()
                        .push((*mid_id, mid_span));
                }
            }
        }
        writers
    }

    /// Drop these terms' spans, keeping `line_to_uplc` a mirror of
    /// `uplc_to_source`.
    ///
    /// Both maps, always: the mirror invariant is documented on
    /// [`Self::register_uplc_span`] and a breakpoint lookup reads
    /// `line_to_uplc`, so removing from one alone leaves a term the stepper
    /// cannot position but a breakpoint can still find — a divergence no
    /// coverage or inversion measurement would notice.
    ///
    /// Returns what was removed, so a caller can report or restore it.
    pub(crate) fn withdraw_uplc_spans(&mut self, ids: &[isize]) -> Vec<(isize, SourceSpan)> {
        let mut removed = Vec::with_capacity(ids.len());
        for id in ids {
            let Some(span) = self.uplc_to_source.remove(id) else {
                continue;
            };
            if let Some(entry) = self.line_to_uplc.get_mut(&span.start_line) {
                entry.retain(|other| other != id);
                if entry.is_empty() {
                    self.line_to_uplc.remove(&span.start_line);
                }
            }
            removed.push((*id, span));
        }
        removed
    }

    /// Withdraw the positions that a donation invented rather than observed.
    ///
    /// A term is abstained iff ALL FOUR hold:
    ///
    /// (a) HEIRLESS — every mid that wrote the span the term currently holds
    ///     (see [`Self::span_writers_per_term`]) is in [`Self::heirless_mids`]:
    ///     every pseudo node that lowered such a mid was deleted, so the span
    ///     reached the term only by donation to a surviving ancestor.
    ///
    /// (b) DUPLICATE — the term's UPLC parent holds a span byte-identical to
    ///     the term's own, which is what makes the withdrawal FREE:
    ///     `StepBridge::breakpoint_anchor_line` arms a line from starting
    ///     evidence and then from covering evidence, and a term whose parent
    ///     holds the identical span can be the last of neither. Chains close
    ///     by induction: the topmost member of a maximal identical-span chain
    ///     has a parent with a DIFFERENT span, fails (b), and is never
    ///     withdrawn, so every abstained term keeps a surviving strict
    ///     ancestor holding its exact span — the same evidence
    ///     `narrow_uplc_spans_to_subtree_hull` gates on.
    ///
    /// (c) STOPPABLE KIND — see [`is_abstainable_kind`].
    ///
    /// (d) BLOCK-SCALE — at least [`ABSTAIN_MIN_SPAN_HEIGHT`] lines tall.
    ///
    /// Nothing is narrowed afterwards. Re-narrowing is the one operation here
    /// that would MOVE a term: withdrawing a span can expose a descendant to a
    /// tighter ancestor bound. Leaving it out means no surviving term changes
    /// line, which is worth more than the tightening — a withdrawal and a
    /// relocation are different claims and must not be measured as one.
    ///
    /// Returns the number of terms withdrawn.
    pub(crate) fn apply_abstain_channel(&mut self, term: &Term<NamedDeBruijn>) -> usize {
        if self.heirless_mids.is_empty() {
            return 0;
        }
        let writers = self.span_writers_per_term();

        let mut candidates: Vec<isize> = Vec::new();
        let mut stack: Vec<(&Term<NamedDeBruijn>, Option<isize>)> = vec![(term, None)];
        while let Some((current, parent)) = stack.pop() {
            let id = term_uniq_id(current);
            if is_abstainable_kind(current)
                && let Some(own) = self.uplc_to_source.get(&id).copied()
                && own.end_line.saturating_sub(own.start_line) >= ABSTAIN_MIN_SPAN_HEIGHT
                && let Some(parent_id) = parent
                && self.uplc_to_source.get(&parent_id) == Some(&own)
                // Adjudicate the span the term CURRENTLY holds, using only the
                // mids that wrote THAT span, and require every one of them to
                // be heirless.
                //
                // Both halves are load-bearing. Span-matching keeps the
                // question about this claim: a term the hull pass pulled onto
                // its own subtree holds a position no mid ever wrote, so its
                // writer set is EMPTY and it is not withdrawn — that position
                // was computed, not donated; and an heirful writer of an
                // earlier, overwritten span cannot veto a span it never wrote.
                // Requiring ALL of them, rather than the last, stops a heirless
                // write that merely sorts later from unearning a position an
                // heirful mid observed on a surviving node.
                && writers.get(&id).is_some_and(|written| {
                    let mut matched = written.iter().filter(|(_, span)| *span == own).peekable();
                    matched.peek().is_some()
                        && matched.all(|(mid, _)| self.heirless_mids.contains(mid))
                })
            {
                candidates.push(id);
            }
            match current {
                Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
                    stack.push((body, Some(id)));
                }
                Term::Apply {
                    function, argument, ..
                } => {
                    stack.push((function, Some(id)));
                    stack.push((argument, Some(id)));
                }
                Term::Constr { fields, .. } => {
                    for field in fields.iter() {
                        stack.push((field, Some(id)));
                    }
                }
                Term::Case {
                    constr, branches, ..
                } => {
                    stack.push((constr, Some(id)));
                    for branch in branches.iter() {
                        stack.push((branch, Some(id)));
                    }
                }
                Term::Var { .. }
                | Term::Constant { .. }
                | Term::Builtin { .. }
                | Term::Error { .. } => {}
            }
        }

        candidates.sort_unstable();
        candidates.dedup();
        let withdrawn = self.withdraw_uplc_spans(&candidates);
        self.abstained_uplc_ids
            .extend(withdrawn.iter().map(|(id, _)| *id));
        withdrawn.len()
    }

    /// The whole post-claim span sequence the stepper depends on, in one place.
    ///
    /// Narrow, then withdraw the positions narrowing cannot fix because they
    /// were never observed, then saturate whatever is still unmapped. One
    /// method, never a copy per caller: the step bridge and the span-anatomy
    /// instrument must run the identical sequence, or the instrument describes
    /// a pipeline the product does not run.
    ///
    /// `lineage_is_exact` gates everything but saturation, matching the
    /// existing contract: the proportional-index fallback fabricates one-line
    /// spans that cannot contain one another, so there is nothing to narrow and
    /// no donated block header to withdraw.
    pub(crate) fn resolve_spans_for_stepping(
        &mut self,
        term: &Term<NamedDeBruijn>,
        lineage_is_exact: bool,
    ) -> SteppingSpanResolution {
        let mut resolution = SteppingSpanResolution::default();
        if lineage_is_exact {
            resolution.pulled = self.resolve_uplc_spans_in_term_tree(term);
            resolution.abstained = self.apply_abstain_channel(term);
        }
        resolution.pre_saturation = self.uplc_to_source.clone();
        resolution.saturated = self.saturate_uplc_term_spans(term);
        resolution
    }

    /// Return original UPLC uniq_ids from `term` that still have no direct
    /// source span mapping in this `SourceMap`.
    pub(crate) fn missing_uplc_term_ids(&self, term: &Term<NamedDeBruijn>) -> Vec<isize> {
        let mut nodes = Vec::new();
        let mut adjacency = HashMap::<isize, Vec<isize>>::new();
        collect_uplc_term_graph(term, &mut nodes, &mut adjacency);
        nodes.retain(|node_id| !self.uplc_to_source.contains_key(node_id));
        nodes.sort_unstable();
        nodes.dedup();
        nodes
    }

    pub(crate) fn var_name(&self, var: VarId) -> Option<&str> {
        self.var_names.get(&var).map(|s| s.as_str())
    }
}

/// Whether this term's rendered surface can be *relocated* away from where its
/// parent renders.
///
/// Only a `Lambda` can: definition hoisting prints it as a top-level `fn` /
/// `rec fn` block, so its span may legitimately be wider than the span of the
/// `Apply` that binds or calls it. Everything else renders in place, nested
/// inside its parent's surface. `Delay` is excluded: the delays this pipeline
/// produces are in-place thunks, not hoisted definitions.
fn is_hoistable_definition(term: &Term<NamedDeBruijn>) -> bool {
    matches!(term, Term::Lambda { .. })
}

/// Whether `outer` covers all of `inner`, comparing (line, column) positions so
/// two spans on one line are ordered by column rather than treated as equal.
fn span_contains(outer: SourceSpan, inner: SourceSpan) -> bool {
    (outer.start_line, outer.start_col) <= (inner.start_line, inner.start_col)
        && (inner.end_line, inner.end_col) <= (outer.end_line, outer.end_col)
}

/// The smallest span covering both, by (line, column) position.
fn span_hull(left: SourceSpan, right: SourceSpan) -> SourceSpan {
    let (start_line, start_col) =
        (left.start_line, left.start_col).min((right.start_line, right.start_col));
    let (end_line, end_col) = (left.end_line, left.end_col).max((right.end_line, right.end_col));
    SourceSpan {
        start_line,
        start_col,
        end_line,
        end_col,
    }
}

/// One UPLC term, flattened into pre-order position.
struct FlatTerm {
    id: isize,
    /// Pre-order index of the enclosing term, `None` for the root.
    parent: Option<usize>,
    /// Number of terms in this term's subtree, itself included. Pre-order makes
    /// a subtree the contiguous range `index .. index + subtree_len`.
    subtree_len: usize,
    /// Prints nothing of its own and can only ever inherit a position.
    is_structural: bool,
    /// Prints as a definition the pipeline may hoist elsewhere.
    is_definition: bool,
    /// Owns a token whose position is not derivable from its children and that
    /// can legitimately occupy a whole block: the `when` eliminator whose
    /// header opens it, or the constructor call that wraps it.
    is_block_surface: bool,
    /// This term is the FUNCTION child of an `Apply`. For a `Lambda` that makes
    /// it a `let` continuation — the statements printed after the binding —
    /// rather than a value printed inline at this position.
    is_apply_function: bool,
}

/// Flatten a term tree into pre-order, recording each term's parent and subtree
/// size.
fn flatten_uplc_term_tree(term: &Term<NamedDeBruijn>) -> Vec<FlatTerm> {
    let mut flat: Vec<FlatTerm> = Vec::new();
    // The third element marks the FUNCTION child of an `Apply`; see
    // `FlatTerm::is_apply_function`.
    let mut stack: Vec<(&Term<NamedDeBruijn>, Option<usize>, bool)> = vec![(term, None, false)];

    while let Some((current, parent, is_apply_function)) = stack.pop() {
        let index = flat.len();
        flat.push(FlatTerm {
            id: term_uniq_id(current),
            parent,
            subtree_len: 1,
            is_structural: matches!(
                current,
                Term::Apply { .. } | Term::Force { .. } | Term::Delay { .. } | Term::Error { .. }
            ),
            is_definition: is_hoistable_definition(current),
            is_block_surface: matches!(current, Term::Case { .. } | Term::Constr { .. }),
            is_apply_function,
        });

        // Pushed in reverse so children pop in source order: the walk stays a
        // true pre-order, which is what makes a subtree contiguous.
        match current {
            Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
                stack.push((body, Some(index), false));
            }
            Term::Apply {
                function, argument, ..
            } => {
                stack.push((argument, Some(index), false));
                stack.push((function, Some(index), true));
            }
            Term::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    stack.push((field, Some(index), false));
                }
            }
            Term::Case {
                constr, branches, ..
            } => {
                for branch in branches.iter().rev() {
                    stack.push((branch, Some(index), false));
                }
                stack.push((constr, Some(index), false));
            }
            Term::Var { .. }
            | Term::Constant { .. }
            | Term::Builtin { .. }
            | Term::Error { .. } => {}
        }
    }

    // A child always follows its parent in pre-order, so one reverse sweep
    // accumulates every subtree size.
    for index in (1..flat.len()).rev() {
        let len = flat[index].subtree_len;
        if let Some(parent) = flat[index].parent {
            flat[parent].subtree_len += len;
        }
    }

    flat
}

fn term_uniq_id(term: &Term<NamedDeBruijn>) -> isize {
    match term {
        Term::Var { uniq_id, .. }
        | Term::Delay { uniq_id, .. }
        | Term::Lambda { uniq_id, .. }
        | Term::Apply { uniq_id, .. }
        | Term::Constant { uniq_id, .. }
        | Term::Force { uniq_id, .. }
        | Term::Error { uniq_id }
        | Term::Builtin { uniq_id, .. }
        | Term::Constr { uniq_id, .. }
        | Term::Case { uniq_id, .. } => *uniq_id,
    }
}

fn add_uplc_edge(adjacency: &mut HashMap<isize, Vec<isize>>, left: isize, right: isize) {
    adjacency.entry(left).or_default().push(right);
    adjacency.entry(right).or_default().push(left);
}

fn collect_uplc_term_graph(
    term: &Term<NamedDeBruijn>,
    nodes: &mut Vec<isize>,
    adjacency: &mut HashMap<isize, Vec<isize>>,
) {
    let mut stack = vec![term];

    while let Some(current) = stack.pop() {
        let current_id = term_uniq_id(current);
        nodes.push(current_id);
        adjacency.entry(current_id).or_default();

        match current {
            Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
                let child_id = term_uniq_id(body);
                add_uplc_edge(adjacency, current_id, child_id);
                stack.push(body);
            }
            Term::Apply {
                function, argument, ..
            } => {
                let function_id = term_uniq_id(function);
                add_uplc_edge(adjacency, current_id, function_id);

                let argument_id = term_uniq_id(argument);
                add_uplc_edge(adjacency, current_id, argument_id);

                stack.push(argument);
                stack.push(function);
            }
            Term::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    let field_id = term_uniq_id(field);
                    add_uplc_edge(adjacency, current_id, field_id);
                    stack.push(field);
                }
            }
            Term::Case {
                constr, branches, ..
            } => {
                let constr_id = term_uniq_id(constr);
                add_uplc_edge(adjacency, current_id, constr_id);

                for branch in branches.iter().rev() {
                    let branch_id = term_uniq_id(branch);
                    add_uplc_edge(adjacency, current_id, branch_id);
                    stack.push(branch);
                }
                stack.push(constr);
            }
            Term::Var { .. }
            | Term::Constant { .. }
            | Term::Builtin { .. }
            | Term::Error { .. } => {}
        }
    }
}

#[cfg(test)]
mod tests;
