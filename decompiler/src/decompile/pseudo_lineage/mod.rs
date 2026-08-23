use std::collections::{BTreeSet, HashMap};

use crate::pseudo::ast::{PseudoExpr, PseudoNodeId, WhenPattern};
use crate::pseudo::mid::expr_id::MidExprId;

type MidLineage = Vec<MidExprId>;

/// Owned-lineage state handed from one projection to the projection chained
/// directly after it.
///
/// The pipeline projects lineage twice: once over the executor's pass
/// snapshots, then once more over `[final_expr, prepared_for_render]`. The
/// first call's emitted map is a containment view keyed by (path, kind)
/// node-id hashes of its last snapshot, and `wrap_validator_entry_for_render`
/// runs between the calls, shifting the path hash of every node under the
/// entry lambda. Seeding the second call from those ids alone therefore
/// misses most of the tree and pools most mids on a few near-root spans.
///
/// The carry keeps the first call's last snapshot plus its pre-containment
/// owned map. The second call splices that snapshot in as an extra leading
/// window, so ownership crosses the boundary through structural matching
/// instead of exact-id lookup, which tolerates the wrap.
///
/// It travels by value from producer to consumer
/// (`pipeline::run_pipeline_with_artifacts_opts` owns both calls), never as
/// ambient per-thread state: the web render path projects inside
/// `tokio::spawn_blocking`, whose threads are REUSED between requests, so
/// anything a projection leaves on its thread is reachable by the NEXT
/// request's projection. By value also bounds the carry to the single chained
/// call instead of pinning a snapshot per thread for the process's life.
pub(crate) struct LineageCarry {
    /// Last snapshot of the producing projection.
    last_snapshot: PseudoSnapshot,
    /// Pre-containment owned lineage keyed by `last_snapshot` node ids.
    owned_by_node: HashMap<u32, MidLineage>,
    /// The same map with donations excluded — see [`project_lineage`]. It
    /// rides the carry because a mirror rebuilt from the emitted map alone
    /// would count every donated mid as having an heir.
    heir_owned_by_node: HashMap<u32, MidLineage>,
}

/// How a mid's ownership moved from one snapshot's node to the next's, in one
/// window.
///
/// `Ord` here is WORST-LAST, so `max` over a mid's transfers gives the weakest
/// link in the chain that put the mid where it is. `Anchor` is the only route
/// that carries no judgement at all: the node's (path, kind) hash was
/// unchanged, so the pipeline re-found the same node rather than deciding
/// anything. Everything below it is a heuristic, and the two donation routes
/// are not even a claim about position (see [`LineageHeirs`]).
///
/// DIAGNOSTIC ONLY. Nothing in the projection reads a `Route`; it is recorded
/// beside the transfer that produced it and never consulted by it, which is
/// what makes [`RouteRecorder`] provably unable to change the map it measures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Route {
    /// R1 — exact `pseudo_node_id` equality. The node's path and kind both
    /// survived the pass, so this is identity, not a match.
    Anchor,
    /// R2 — same `node_sig` bucket, paired `left_free[i] <-> right_free[i]` BY
    /// LIST INDEX. No structural check of any kind: two same-signature leaves
    /// (`var|x_#|0`) are paired by the order they happen to sit in the bucket.
    SigPosition,
    /// R3 — same kind and arity, `fuzzy_similarity >= 0.55`.
    Fuzzy,
    /// R4 — the removed node's own subtree image: its single matched survivor,
    /// or the LOWEST COMMON ANCESTOR of all of them.
    DonateDescLca,
    /// R5 — the nearest matched ancestor, else the first ancestor with a
    /// surviving subtree.
    DonateAncestor,
    /// R6 — the `to` root. The no-loss fallback: nothing in the window matched
    /// anywhere near this node, and its mids must land SOMEWHERE.
    DonateToRoot,
}

// Reporting accessors for span-provenance instruments. Nothing in
// this tree reads them; the routes themselves are still recorded.
#[allow(dead_code)]
impl Route {
    /// Stable key for a census, so a report keeps reading the same after a
    /// variant is added or reordered.
    pub(crate) fn key(self) -> &'static str {
        match self {
            Route::Anchor => "R1_anchor",
            Route::SigPosition => "R2_sig_position",
            Route::Fuzzy => "R3_fuzzy",
            Route::DonateDescLca => "R4_donate_desc_lca",
            Route::DonateAncestor => "R5_donate_ancestor",
            Route::DonateToRoot => "R6_donate_to_root",
        }
    }

    /// Dense index, for the fixed-width per-window counters.
    pub(crate) fn index(self) -> usize {
        match self {
            Route::Anchor => 0,
            Route::SigPosition => 1,
            Route::Fuzzy => 2,
            Route::DonateDescLca => 3,
            Route::DonateAncestor => 4,
            Route::DonateToRoot => 5,
        }
    }

    /// Every route, in `Ord` order. The one place a census iterates them.
    pub(crate) const ALL: [Route; 6] = [
        Route::Anchor,
        Route::SigPosition,
        Route::Fuzzy,
        Route::DonateDescLca,
        Route::DonateAncestor,
        Route::DonateToRoot,
    ];

    /// Is this a donation rather than a node-to-node match? Donations are a
    /// COVERAGE guarantee and never a position claim.
    pub(crate) fn is_donation(self) -> bool {
        matches!(
            self,
            Route::DonateDescLca | Route::DonateAncestor | Route::DonateToRoot
        )
    }
}

/// What the projection did to one mid, over the whole chain of windows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct MidRouteProvenance {
    /// The weakest route the mid ever took. `Anchor` means it NEVER left an
    /// exact-id match and was never donated — the render's placement of it is
    /// then not a projection decision at all.
    ///
    /// READ THE DENOMINATOR BEFORE READING THE VALUE. This is a max over TWO
    /// things at once, not one: every WINDOW in the chain (plus the spliced
    /// bridge), and every NODE that owned the mid in each of those windows.
    /// [`RouteRecorder::note_transfer`] fires once per owning node per window,
    /// and a mid is owned by more than one node whenever a donation or a
    /// [`lineage_merge`] put it under a second carrier. So a mid can be
    /// labelled by a route taken by a carrier that never printed it and never
    /// won `set_mid_span`.
    ///
    /// That asymmetry points ONE WAY:
    ///   * for "worst == `Anchor`" (did the projection DECIDE this position at
    ///     all?) it is CONSERVATIVE: `max` over a superset can only make the
    ///     label worse, so `worst == Anchor` still implies every transfer of
    ///     every carrier anchored.
    ///   * for a LIFT reading stratified by route it ATTENUATES: mids
    ///     heuristic on a carrier that never printed them pool with mids
    ///     heuristic on the carrier that did, pushing every stratum toward
    ///     the population mean and any lift toward 1.00x.
    pub worst_route: Route,
    /// Index of the first window in which the mid moved by anything other than
    /// [`Route::Anchor`]. `None` when it never did.
    pub first_non_anchor_window: Option<u32>,
    /// Transfer events that carried this mid, summed over every window. A mid
    /// owned by several nodes at once contributes one per node per window, so
    /// this is a transfer count and NOT a window count.
    pub hops: u32,
    /// The worst route the mid took in the spliced `(pre-wrap, post-wrap)`
    /// bridge window, or `None` if it did not move there. Separate because
    /// the wrap re-hashes the path of every node under the entry lambda, so
    /// this is the one window where `Anchor` is structurally unavailable.
    pub bridge_route: Option<Route>,
}

impl MidRouteProvenance {
    fn seed(route: Route, window: u32, is_bridge: bool) -> Self {
        Self {
            worst_route: route,
            first_non_anchor_window: (route != Route::Anchor).then_some(window),
            hops: 1,
            bridge_route: is_bridge.then_some(route),
        }
    }

    fn absorb(&mut self, route: Route, window: u32, is_bridge: bool) {
        self.worst_route = self.worst_route.max(route);
        if route != Route::Anchor && self.first_non_anchor_window.is_none() {
            self.first_non_anchor_window = Some(window);
        }
        self.hops = self.hops.saturating_add(1);
        if is_bridge {
            self.bridge_route = Some(match self.bridge_route {
                Some(existing) => existing.max(route),
                None => route,
            });
        }
    }
}

/// What one matched pair `(l, r)` did to the PARENT relationship it arrived
/// with, and — when it broke it — whether the window's own edits already
/// explain the break.
///
/// "The parent link did not survive" is on its own worth nothing: the pipeline
/// re-parents nodes legitimately all the time — hoisting Z-combinator helpers
/// out of their defining scope, flattening right-nested spines (else-chain into
/// `when` arms, cons spine into a list literal, curried apply into one call),
/// deleting wrappers by inlining through them. Each of those breaks a parent
/// link on a match that is CORRECT, so only the residue left after they are
/// subtracted can carry an accusation.
///
/// The two BENIGN arms are the null hypothesis and [`Self::UnrelatedParent`] is
/// the claim, measured against the window's own `removed + added` — the number
/// of subtree roots the pass could have relocated at all — and NOT against
/// [`Route::Anchor`]'s parent consistency, which is near-forced:
/// `pseudo_node_id` is a ROLLING PREFIX hash of the path, so equal ids imply
/// equal parent paths and an anchor is BY CONSTRUCTION a node that did not
/// move.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParentVerdict {
    /// `parent(l)` matched exactly to `parent(r)`, or both endpoints are their
    /// tree's root. Nothing moved.
    Consistent,
    /// (i) `parent(l)` is a REMOVED node — nothing in `to` matched it. The pass
    /// deleted the parent, so the child MUST re-parent somewhere; inlining
    /// through a wrapper and flattening a spine both land here. BENIGN.
    ParentRemoved,
    /// (ii) `parent(l)` matched to `p''`, and `parent(r)` is an ancestor or a
    /// descendant of `p''` in the `to` tree. The child moved along the ancestry
    /// it was already on — a hoist out of an enclosing block, or an extra level
    /// introduced beneath the old parent. BENIGN.
    WithinAncestry,
    /// (iii) `parent(l)` matched to `p''` and `parent(r)` is UNRELATED to `p''`
    /// in the `to` ancestry: neither an ancestor nor a descendant of it. The
    /// only arm that is a claim about the matcher.
    UnrelatedParent,
    /// Exactly one endpoint is its tree's root. A relocation, but the (iii)
    /// predicate is not defined for it (there is no `parent(l)` to match, or no
    /// `parent(r)` to place), so it is counted apart rather than folded in —
    /// folding it in would inflate the claim count.
    RootAsymmetric,
}

/// Per-window [`ParentVerdict`] counts, kept per route.
///
/// Per route because the three match passes are three different claims: R1 is
/// identity and its consistency is structurally near-forced, while R2 pairs by
/// LIST INDEX inside a signature bucket with no structural check at all and R3
/// pairs on kind, arity and a summary similarity. A pooled figure would let R1's
/// forced agreement mask the other two.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct ParentConsistencyCensus {
    /// Indexed by [`Route::index`], as every other array on this row is.
    pub consistent: [usize; 6],
    /// (i) — see [`ParentVerdict::ParentRemoved`].
    pub parent_removed: [usize; 6],
    /// (ii) — see [`ParentVerdict::WithinAncestry`].
    pub within_ancestry: [usize; 6],
    /// (iii) — see [`ParentVerdict::UnrelatedParent`]. THE claim.
    pub unrelated_parent: [usize; 6],
    /// See [`ParentVerdict::RootAsymmetric`].
    pub root_asymmetric: [usize; 6],
}

// Reporting accessors for span-provenance instruments. Nothing in
// this tree reads them; the routes themselves are still recorded.
#[allow(dead_code)]
impl ParentConsistencyCensus {
    fn note(&mut self, verdict: ParentVerdict, route: Route) {
        let slot = route.index();
        match verdict {
            ParentVerdict::Consistent => self.consistent[slot] += 1,
            ParentVerdict::ParentRemoved => self.parent_removed[slot] += 1,
            ParentVerdict::WithinAncestry => self.within_ancestry[slot] += 1,
            ParentVerdict::UnrelatedParent => self.unrelated_parent[slot] += 1,
            ParentVerdict::RootAsymmetric => self.root_asymmetric[slot] += 1,
        }
    }

    /// Every match this window classified. Equals the window's match count —
    /// the five arms partition the matches, they do not sample them.
    pub(crate) fn classified(&self) -> usize {
        self.consistent.iter().sum::<usize>()
            + self.parent_removed.iter().sum::<usize>()
            + self.within_ancestry.iter().sum::<usize>()
            + self.unrelated_parent.iter().sum::<usize>()
            + self.root_asymmetric.iter().sum::<usize>()
    }

    /// Sum of `counts` over the two HEURISTIC match routes, R2 and R3. R1 is
    /// excluded from every headline because its parent consistency is a
    /// property of the path hash, not evidence about matching.
    pub(crate) fn heuristic(counts: &[usize; 6]) -> usize {
        counts[Route::SigPosition.index()] + counts[Route::Fuzzy.index()]
    }
}

/// Per-window route counts. `removed`/`added` are reproduced verbatim from
/// [`build_node_matches`] rather than recomputed, so the census cannot drift
/// from the matching it reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WindowRouteCensus {
    /// Position in the whole chain, counting the spliced bridge window.
    pub window: u32,
    /// Is this the `(pre-wrap, post-wrap)` window spliced in by the carry?
    pub is_bridge: bool,
    pub from_nodes: usize,
    pub to_nodes: usize,
    /// NODE matches by route, indexed by [`Route::index`]. Donation slots are
    /// always 0 here — a donation is not a node match.
    pub node_matches: [usize; 6],
    /// Nodes of `from` that nothing in `to` matched.
    pub removed: usize,
    /// Nodes of `to` that nothing in `from` matched.
    pub added: usize,
    /// Removed nodes that OWNED lineage and were therefore donated, by route.
    /// Match slots are always 0 here.
    pub donations: [usize; 6],
    /// (mid, transfer) events by route — the quantity `worst_route` is a max
    /// over.
    pub mid_transfers: [usize; 6],
    /// What each match did to its parent relationship, and whether this
    /// window's own edits explain it. Populated by
    /// [`parent_consistency_census`] from the SAME `matches` vector the
    /// transfers above were read off, by a function that only reads it.
    pub parent: ParentConsistencyCensus,
}

// Reporting accessors for span-provenance instruments. Nothing in
// this tree reads them; the routes themselves are still recorded.
#[allow(dead_code)]
impl WindowRouteCensus {
    /// `removed + added`: the number of subtree ROOTS this pass could have
    /// legitimately relocated. A hoist re-parents only the root of the moved
    /// subtree — its descendants keep matched parents and cost the budget
    /// nothing — so this is the natural denominator for a relocation count.
    pub(crate) fn structural_edits(&self) -> usize {
        self.removed + self.added
    }

    /// Share of this window's matches that came from the anchor pass, in
    /// percent.
    ///
    /// `0.0` when nothing matched at all, which deliberately admits the window
    /// to the `< 5%` low-anchor stratum rather than being an accident of the
    /// empty ratio: a window that matched nothing is a full rewrite, and a full
    /// rewrite is precisely a window where the identity pass did none of the
    /// work. Returning `100.0` instead would hide exactly those windows from
    /// the stratum they belong to.
    pub(crate) fn anchor_share_of_matches(&self) -> f64 {
        let matched: usize = self.node_matches.iter().sum();
        if matched == 0 {
            return 0.0;
        }
        100.0 * self.node_matches[Route::Anchor.index()] as f64 / matched as f64
    }
}

/// Optional, OFF-in-production recorder of [`Route`] provenance.
///
/// Threaded as `Option<&mut RouteRecorder>` — never ambient, for the same
/// reason [`LineageCarry`] is passed by value: the web render path projects on
/// a REUSED `spawn_blocking` thread, so anything left behind on a thread is
/// reachable by the next request.
///
/// Cost when ABSENT is one `Option` test per window and per donated node; the
/// off path does no work proportional to anything, because an
/// `O(depth x nodes)` scan in this layer regresses debugger startup.
///
/// Cost when PRESENT is more than the hash update per mid per transfer.
/// [`parent_consistency_census`] runs per recorded window and builds two
/// parent maps, a match map and a depth table, then walks ancestry, roughly
/// doubling this layer's parent-map work. The recorder is output-inert, not
/// cost-inert.
#[derive(Debug, Clone, Default)]
pub(crate) struct RouteRecorder {
    mids: HashMap<MidExprId, MidRouteProvenance>,
    windows: Vec<WindowRouteCensus>,
    next_window: u32,
}

// Reporting accessors for span-provenance instruments. Nothing in
// this tree reads them; the routes themselves are still recorded.
#[allow(dead_code)]
impl RouteRecorder {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Route provenance per mid, over every window the recorder saw.
    pub(crate) fn mids(&self) -> &HashMap<MidExprId, MidRouteProvenance> {
        &self.mids
    }

    /// One row per window, in chain order.
    pub(crate) fn windows(&self) -> &[WindowRouteCensus] {
        &self.windows
    }

    /// Open a window's row and return its index. Called once per window, before
    /// any transfer is noted against it.
    fn open_window(
        &mut self,
        is_bridge: bool,
        from_nodes: usize,
        to_nodes: usize,
        removed: usize,
        added: usize,
        parent: ParentConsistencyCensus,
    ) -> u32 {
        let window = self.next_window;
        self.next_window += 1;
        self.windows.push(WindowRouteCensus {
            window,
            is_bridge,
            from_nodes,
            to_nodes,
            node_matches: [0; 6],
            removed,
            added,
            donations: [0; 6],
            mid_transfers: [0; 6],
            parent,
        });
        window
    }

    fn note_node_match(&mut self, route: Route) {
        if let Some(row) = self.windows.last_mut() {
            row.node_matches[route.index()] += 1;
        }
    }

    fn note_donation(&mut self, route: Route) {
        if let Some(row) = self.windows.last_mut() {
            row.donations[route.index()] += 1;
        }
    }

    /// Record that `mids` moved by `route` in the window opened last.
    fn note_transfer(&mut self, mids: &[MidExprId], route: Route, window: u32, is_bridge: bool) {
        if let Some(row) = self.windows.last_mut() {
            row.mid_transfers[route.index()] += mids.len();
        }
        for mid in mids {
            self.mids
                .entry(*mid)
                .and_modify(|provenance| provenance.absorb(route, window, is_bridge))
                .or_insert_with(|| MidRouteProvenance::seed(route, window, is_bridge));
        }
    }
}

/// Mids that still have an HEIR at the end of a projection: some node of the
/// last snapshot owns them through an unbroken chain of 1:1 structural matches
/// back to the node that lowered them.
///
/// Its complement over the mids the source map knows is the ABSTAIN
/// population: every lowering node of such a mid was deleted, so it still
/// carries a span only because `propagate_removed_wrapper_lineage` donated it
/// to a surviving ancestor. That donation is a COVERAGE guarantee — the mid
/// keeps *a* span, so nothing downstream has to cope with a hole — and never a
/// POSITION claim: the receiving node is chosen for having survived, not for
/// rendering the construct the mid describes.
pub(crate) struct LineageHeirs {
    /// Sorted and deduplicated, so membership is a binary search.
    pub heir_mids: Vec<MidExprId>,
}

#[derive(Debug, Clone)]
pub(crate) struct PseudoSnapshot {
    pub nodes: Vec<PseudoSnapshotNode>,
}

#[derive(Debug, Clone)]
pub(crate) struct PseudoSnapshotNode {
    pub id: u32,
    pub pseudo_node_id: PseudoNodeId,
    pub kind: String,
    pub summary: String,
    pub children: Vec<u32>,
}

pub(crate) fn snapshot_expr(expr: &PseudoExpr) -> PseudoSnapshot {
    snapshot_expr_at_path(expr, &[])
}

pub(crate) fn snapshot_expr_at_path(expr: &PseudoExpr, path: &[u32]) -> PseudoSnapshot {
    let mut nodes = Vec::<PseudoSnapshotNode>::new();
    let mut next_id = 1u32;
    flatten_pseudo(
        expr,
        &mut next_id,
        &mut nodes,
        PseudoExpr::provenance_path_hash(path),
    );
    PseudoSnapshot { nodes }
}

/// Project the initial pseudo→mid lineage through every pipeline snapshot.
///
/// Each node carries only the mids it OWNS: those its origin node was seeded
/// with, plus mids donated to it when their origin node was removed. Owned
/// lineage crosses snapshots only through 1:1 node matches and removed-node
/// donations — parents never absorb their descendants' lineage during the
/// loop, which would make every accumulated union transitive once per pass
/// until nearly every node carries every mid.
///
/// The returned map restores the containment view consumers expect (a node's
/// lineage includes its subtree's) by unioning owned lineage bottom-up over
/// the FINAL snapshot only — see `emit_containment_lineage`.
///
/// Standalone form: nothing is carried in and nothing is carried out; used by
/// the lowering-time local subtree projections.
pub(crate) fn project_final_pseudo_to_mid(
    snapshots: &[PseudoSnapshot],
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
) -> HashMap<PseudoNodeId, Vec<MidExprId>> {
    project_lineage(snapshots, initial_pseudo_to_mid, None, false, None).0
}

/// Projection seeded from the [`LineageCarry`] of the projection that ran
/// immediately before it, plus the heir set of the whole chain.
///
/// With a carry, `initial_pseudo_to_mid` is unused: ownership arrives through
/// the carry's owned map and flows over the spliced bridge window. Without one
/// (snapshot collection off, so there was no producing projection) this
/// degrades to the exact-id seeding of [`project_final_pseudo_to_mid`].
///
/// Heirs are emitted here because this projection's last snapshot IS the tree
/// the printer walks, so its heirs are the only ones that describe what
/// actually got rendered.
pub(crate) fn project_chained_pseudo_to_mid_with_heirs(
    snapshots: &[PseudoSnapshot],
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
    carry: Option<LineageCarry>,
    recorder: Option<&mut RouteRecorder>,
) -> (HashMap<PseudoNodeId, Vec<MidExprId>>, LineageHeirs) {
    let (emitted, _, heirs) =
        project_lineage(snapshots, initial_pseudo_to_mid, carry, false, recorder);
    (emitted, heirs)
}

/// Projection that also returns the [`LineageCarry`] a directly chained
/// projection needs to keep fine-grained ownership across a tree rewrite that
/// shifts node-id path hashes.
///
/// The pipeline's pass projection is the only producer; the carry it returns
/// must be handed straight to [`project_chained_pseudo_to_mid_with_heirs`].
pub(crate) fn project_pseudo_to_mid_carrying(
    snapshots: &[PseudoSnapshot],
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
    recorder: Option<&mut RouteRecorder>,
) -> (HashMap<PseudoNodeId, Vec<MidExprId>>, Option<LineageCarry>) {
    let (emitted, carry, _) =
        project_lineage(snapshots, initial_pseudo_to_mid, None, true, recorder);
    (emitted, carry)
}

/// Shared projection core. `carry_in` replaces exact-id seeding with a spliced
/// bridge window; `carry_out` requests the state a chained projection would
/// need. Neither is implicit and nothing outlives the call.
///
/// Alongside the owned map it maintains a MATCH-ONLY mirror: the identical
/// transfer with [`propagate_removed_wrapper_lineage`] left out, so a mid
/// survives in it exactly while some node that lowered it is still standing —
/// the fact `LineageHeirs` reports. It rides the `matches` the window already
/// computed, adding one hash-map merge per matched node and no tree walk.
fn project_lineage(
    snapshots: &[PseudoSnapshot],
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
    carry_in: Option<LineageCarry>,
    carry_out: bool,
    mut recorder: Option<&mut RouteRecorder>,
) -> (
    HashMap<PseudoNodeId, Vec<MidExprId>>,
    Option<LineageCarry>,
    LineageHeirs,
) {
    let Some(first) = snapshots.first() else {
        return (
            HashMap::new(),
            None,
            LineageHeirs {
                heir_mids: Vec::new(),
            },
        );
    };
    // `first` exists, so the last element does too.
    let last = &snapshots[snapshots.len() - 1];

    let (mut owned_by_node, mut heir_owned_by_node, bridge_snapshot) = match carry_in {
        Some(carry) => (
            carry.owned_by_node,
            carry.heir_owned_by_node,
            Some(carry.last_snapshot),
        ),
        None => {
            let seeded = seed_owned_lineage(first, initial_pseudo_to_mid);
            (seeded.clone(), seeded, None)
        }
    };

    // `is_bridge` is true for exactly the spliced leading window and is decided
    // BY CONSTRUCTION, not by inspecting the snapshots: it exists iff a carry
    // came in, and a carry only ever crosses `wrap_validator_entry_for_render`,
    // where the pipeline takes it from the PRE-wrap pass snapshots and projects
    // it over the POST-wrap expr. Nothing else can produce one, so the bridge
    // row can never be confused with a pass window.
    let bridge_windows = bridge_snapshot
        .as_ref()
        .map(|bridge| (bridge, first, true))
        .into_iter();
    let regular_windows = snapshots
        .windows(2)
        .map(|window| (&window[0], &window[1], false));
    for (from, to, is_bridge) in bridge_windows.chain(regular_windows) {
        let (matches, removed, added) = build_node_matches(from, to);

        // Opened before any transfer is noted, so a window that moved nothing
        // still gets a row rather than dropping out of the census.
        let window = match recorder.as_deref_mut() {
            Some(recorder) => {
                // Computed here from the `matches` the window already has,
                // and not inside `build_node_matches`, so the classification
                // cannot be read by the matching it classifies. It is also
                // why the whole cost sits behind `recorder.is_some()` —
                // production never builds a parent map for this.
                let parent = parent_consistency_census(from, to, &matches);
                recorder.open_window(
                    is_bridge,
                    from.nodes.len(),
                    to.nodes.len(),
                    removed.len(),
                    added.len(),
                    parent,
                )
            }
            None => 0,
        };

        let prev_owned = owned_by_node;
        let mut next_owned = HashMap::<u32, MidLineage>::new();
        let prev_heir = heir_owned_by_node;
        let mut next_heir = HashMap::<u32, MidLineage>::new();
        for &(from_id, to_id, route) in &matches {
            if let Some(recorder) = recorder.as_deref_mut() {
                recorder.note_node_match(route);
            }
            if let Some(owned) = prev_owned.get(&from_id) {
                lineage_merge(next_owned.entry(to_id).or_default(), owned);
                if let Some(recorder) = recorder.as_deref_mut() {
                    recorder.note_transfer(owned, route, window, is_bridge);
                }
            }
            if let Some(owned) = prev_heir.get(&from_id) {
                lineage_merge(next_heir.entry(to_id).or_default(), owned);
            }
        }
        propagate_removed_wrapper_lineage(
            from,
            to,
            &matches,
            &removed,
            &prev_owned,
            &mut next_owned,
            recorder.as_deref_mut(),
            window,
            is_bridge,
        );
        owned_by_node = next_owned;
        // Deliberately NOT donated to. That omission is the entire mirror.
        heir_owned_by_node = next_heir;
    }

    let mut heir_mids: Vec<MidExprId> = heir_owned_by_node
        .values()
        .flat_map(|lineage| lineage.iter().copied())
        .collect();
    heir_mids.sort_unstable();
    heir_mids.dedup();

    let emitted = emit_containment_lineage(last, &owned_by_node);
    let carry = carry_out.then(|| LineageCarry {
        last_snapshot: last.clone(),
        owned_by_node,
        heir_owned_by_node,
    });
    (emitted, carry, LineageHeirs { heir_mids })
}

/// Seed each first-snapshot node with the mids its pseudo node lowered from.
fn seed_owned_lineage(
    first: &PseudoSnapshot,
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
) -> HashMap<u32, MidLineage> {
    let mut owned_by_node = HashMap::<u32, MidLineage>::new();
    for node in &first.nodes {
        if let Some(mids) = initial_pseudo_to_mid.get(&node.pseudo_node_id) {
            lineage_merge_slice(owned_by_node.entry(node.id).or_default(), mids);
        }
    }
    owned_by_node
}

/// Produce the final lineage map: every node's entry is its owned lineage
/// unioned with its children's entries. Snapshot nodes are stored in
/// post-order, so a single forward pass sees children before parents. Owned
/// mids stay attached to the most specific node that carries them while
/// ancestors still cover their whole subtree, so claim-time ranking by
/// lineage cardinality picks the deepest carrier first.
fn emit_containment_lineage(
    snapshot: &PseudoSnapshot,
    owned_by_node: &HashMap<u32, MidLineage>,
) -> HashMap<PseudoNodeId, Vec<MidExprId>> {
    let mut subtree = HashMap::<u32, MidLineage>::with_capacity(snapshot.nodes.len());
    let mut final_pseudo_to_mid = HashMap::new();
    for node in &snapshot.nodes {
        let mut merged = owned_by_node.get(&node.id).cloned().unwrap_or_default();
        for child_id in &node.children {
            if let Some(child_lineage) = subtree.get(child_id) {
                lineage_merge(&mut merged, child_lineage);
            }
        }
        if !merged.is_empty() {
            final_pseudo_to_mid.insert(node.pseudo_node_id, merged.clone());
        }
        subtree.insert(node.id, merged);
    }
    final_pseudo_to_mid
}

#[cfg(test)]
pub(crate) fn trace_projected_mid_id_unions(
    snapshots: &[PseudoSnapshot],
    initial_pseudo_to_mid: &HashMap<PseudoNodeId, Vec<MidExprId>>,
) -> Vec<BTreeSet<MidExprId>> {
    let Some(first) = snapshots.first() else {
        return Vec::new();
    };

    let mut owned_by_node = seed_owned_lineage(first, initial_pseudo_to_mid);

    let mut unions = vec![collect_lineage_mid_union(&owned_by_node)];

    for window in snapshots.windows(2) {
        let from = &window[0];
        let to = &window[1];
        let (matches, removed, _) = build_node_matches(from, to);

        let prev_owned = owned_by_node;
        let mut next_owned = HashMap::<u32, MidLineage>::new();
        for &(from_id, to_id, _) in &matches {
            if let Some(owned) = prev_owned.get(&from_id) {
                lineage_merge(next_owned.entry(to_id).or_default(), owned);
            }
        }
        propagate_removed_wrapper_lineage(
            from,
            to,
            &matches,
            &removed,
            &prev_owned,
            &mut next_owned,
            None,
            0,
            false,
        );
        owned_by_node = next_owned;
        unions.push(collect_lineage_mid_union(&owned_by_node));
    }

    unions
}

#[cfg(test)]
fn collect_lineage_mid_union(lineage_by_node: &HashMap<u32, MidLineage>) -> BTreeSet<MidExprId> {
    lineage_by_node
        .values()
        .flat_map(|lineage| lineage.iter().copied())
        .collect()
}

fn sorted_unique_mid_lineage(mut mids: MidLineage) -> MidLineage {
    mids.sort_unstable();
    mids.dedup();
    mids
}

fn merge_sorted_unique_mid_lineages(left: &[MidExprId], right: &[MidExprId]) -> MidLineage {
    let mut merged = Vec::with_capacity(left.len() + right.len());
    let mut left_index = 0usize;
    let mut right_index = 0usize;

    while left_index < left.len() && right_index < right.len() {
        match left[left_index].cmp(&right[right_index]) {
            std::cmp::Ordering::Less => {
                merged.push(left[left_index]);
                left_index += 1;
            }
            std::cmp::Ordering::Greater => {
                merged.push(right[right_index]);
                right_index += 1;
            }
            std::cmp::Ordering::Equal => {
                merged.push(left[left_index]);
                left_index += 1;
                right_index += 1;
            }
        }
    }

    merged.extend_from_slice(&left[left_index..]);
    merged.extend_from_slice(&right[right_index..]);
    merged
}

fn lineage_merge(dst: &mut MidLineage, src: &[MidExprId]) {
    if src.is_empty() {
        return;
    }
    if dst.is_empty() {
        dst.extend_from_slice(src);
        return;
    }

    let merged = merge_sorted_unique_mid_lineages(dst, src);
    if merged.len() != dst.len() || merged != *dst {
        *dst = merged;
    }
}

fn lineage_merge_slice(dst: &mut MidLineage, src: &[MidExprId]) {
    let sorted = sorted_unique_mid_lineage(src.to_vec());
    lineage_merge(dst, &sorted);
}

fn flatten_child_pseudo(
    expr: &PseudoExpr,
    next_id: &mut u32,
    out: &mut Vec<PseudoSnapshotNode>,
    path_hash: u64,
    child_index: u32,
) -> u32 {
    flatten_pseudo(
        expr,
        next_id,
        out,
        PseudoExpr::provenance_child_path_hash(path_hash, child_index),
    )
}

fn flatten_pseudo(
    expr: &PseudoExpr,
    next_id: &mut u32,
    out: &mut Vec<PseudoSnapshotNode>,
    path_hash: u64,
) -> u32 {
    let id = *next_id;
    *next_id += 1;
    let pseudo_node_id = expr.provenance_node_id_from_path_hash(path_hash);

    let (kind, summary, children): (String, String, Vec<u32>) = match expr {
        PseudoExpr::Int(n) => ("int".to_string(), n.to_string(), vec![]),
        PseudoExpr::ByteArray(bs) => ("bytes".to_string(), format!("len={}", bs.len()), vec![]),
        PseudoExpr::String(s) => ("string".to_string(), s.clone(), vec![]),
        PseudoExpr::Bool(b) => ("bool".to_string(), b.to_string(), vec![]),
        PseudoExpr::Unit => ("unit".to_string(), "Void".to_string(), vec![]),
        PseudoExpr::Var { name, .. } => ("var".to_string(), name.clone(), vec![]),
        PseudoExpr::Lambda { params, body } => {
            let body_id = flatten_child_pseudo(body, next_id, out, path_hash, 0);
            (
                "lambda".to_string(),
                params
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
                vec![body_id],
            )
        }
        PseudoExpr::RecFn { name, params, body } => {
            let body_id = flatten_child_pseudo(body, next_id, out, path_hash, 0);
            let params = params.iter().map(ToString::to_string).collect::<Vec<_>>();
            (
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
                vec![body_id],
            )
        }
        PseudoExpr::Apply { function, args } => {
            let mut children = vec![flatten_child_pseudo(function, next_id, out, path_hash, 0)];
            for (index, arg) in args.iter().enumerate() {
                children.push(flatten_child_pseudo(
                    arg,
                    next_id,
                    out,
                    path_hash,
                    index as u32 + 1,
                ));
            }
            (
                "apply".to_string(),
                format!("argc={}", args.len()),
                children,
            )
        }
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            let value_id = flatten_child_pseudo(value, next_id, out, path_hash, 0);
            let body_id = flatten_child_pseudo(body, next_id, out, path_hash, 1);
            ("let".to_string(), name.clone(), vec![value_id, body_id])
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition_id = flatten_child_pseudo(condition, next_id, out, path_hash, 0);
            let then_id = flatten_child_pseudo(then_branch, next_id, out, path_hash, 1);
            let else_id = flatten_child_pseudo(else_branch, next_id, out, path_hash, 2);
            (
                "if".to_string(),
                "if".to_string(),
                vec![condition_id, then_id, else_id],
            )
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            let mut next_child_index = 0u32;
            let mut children = vec![flatten_child_pseudo(
                subject,
                next_id,
                out,
                path_hash,
                next_child_index,
            )];
            next_child_index += 1;
            for clause in clauses {
                if matches!(clause.pattern, WhenPattern::Literal(_)) {
                    next_child_index += 1;
                }
                if clause.guard.is_some() {
                    next_child_index += 1;
                }
                children.push(flatten_child_pseudo(
                    &clause.body,
                    next_id,
                    out,
                    path_hash,
                    next_child_index,
                ));
                next_child_index += 1;
            }
            (
                "when".to_string(),
                format!("clauses={}", clauses.len()),
                children,
            )
        }
        PseudoExpr::List { elements, tail } => {
            let mut children = Vec::new();
            for (index, element) in elements.iter().enumerate() {
                children.push(flatten_child_pseudo(
                    element,
                    next_id,
                    out,
                    path_hash,
                    index as u32,
                ));
            }
            if let Some(tail) = tail {
                children.push(flatten_child_pseudo(
                    tail,
                    next_id,
                    out,
                    path_hash,
                    elements.len() as u32,
                ));
            }
            (
                "list".to_string(),
                format!("len={}", elements.len()),
                children,
            )
        }
        PseudoExpr::Tuple(elements) => {
            let mut children = Vec::new();
            for (index, element) in elements.iter().enumerate() {
                children.push(flatten_child_pseudo(
                    element,
                    next_id,
                    out,
                    path_hash,
                    index as u32,
                ));
            }
            (
                "tuple".to_string(),
                format!("len={}", elements.len()),
                children,
            )
        }
        PseudoExpr::Pair(a, b) => {
            let a_id = flatten_child_pseudo(a, next_id, out, path_hash, 0);
            let b_id = flatten_child_pseudo(b, next_id, out, path_hash, 1);
            ("pair".to_string(), "pair".to_string(), vec![a_id, b_id])
        }
        PseudoExpr::Constr {
            shape, tag, fields, ..
        } => {
            let mut children = Vec::new();
            for (index, field) in fields.iter().enumerate() {
                children.push(flatten_child_pseudo(
                    field,
                    next_id,
                    out,
                    path_hash,
                    index as u32,
                ));
            }
            (
                "constr".to_string(),
                format!("{}#{}", shape.pretty_name().unwrap_or("?"), tag),
                children,
            )
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } => {
            let record_id = flatten_child_pseudo(record, next_id, out, path_hash, 0);
            (
                "field".to_string(),
                selector.as_pretty_name().to_string(),
                vec![record_id],
            )
        }
        PseudoExpr::IndexAccess { collection, index } => {
            let collection_id = flatten_child_pseudo(collection, next_id, out, path_hash, 0);
            ("index".to_string(), index.to_string(), vec![collection_id])
        }
        PseudoExpr::BinOp { op, left, right } => {
            let left_id = flatten_child_pseudo(left, next_id, out, path_hash, 0);
            let right_id = flatten_child_pseudo(right, next_id, out, path_hash, 1);
            (
                "binop".to_string(),
                op.symbol().to_string(),
                vec![left_id, right_id],
            )
        }
        PseudoExpr::UnOp { op, operand } => {
            let operand_id = flatten_child_pseudo(operand, next_id, out, path_hash, 0);
            (
                "unop".to_string(),
                op.symbol().to_string(),
                vec![operand_id],
            )
        }
        PseudoExpr::BuiltinCall { name, args } => {
            let mut children = Vec::new();
            for (index, arg) in args.iter().enumerate() {
                children.push(flatten_child_pseudo(
                    arg,
                    next_id,
                    out,
                    path_hash,
                    index as u32,
                ));
            }
            (
                "builtin".to_string(),
                format!("{}({})", name, args.len()),
                children,
            )
        }
        PseudoExpr::Error { message } => (
            "error".to_string(),
            message.clone().unwrap_or_default(),
            vec![],
        ),
        PseudoExpr::Delay(inner) => {
            let child_id = flatten_child_pseudo(inner, next_id, out, path_hash, 0);
            ("delay".to_string(), "delay".to_string(), vec![child_id])
        }
        PseudoExpr::Force(inner) => {
            let child_id = flatten_child_pseudo(inner, next_id, out, path_hash, 0);
            ("force".to_string(), "force".to_string(), vec![child_id])
        }
        PseudoExpr::Trace { message, value } => {
            let message_id = flatten_child_pseudo(message, next_id, out, path_hash, 0);
            let value_id = flatten_child_pseudo(value, next_id, out, path_hash, 1);
            (
                "trace".to_string(),
                "trace".to_string(),
                vec![message_id, value_id],
            )
        }
        PseudoExpr::Raw { reason, .. } => ("raw".to_string(), reason.clone(), vec![]),
        PseudoExpr::Data(_) => ("data".to_string(), "data".to_string(), vec![]),
        // distinct kind, matches debug-bundle `helper_symbol`/`Fix` formatting.
        PseudoExpr::HelperSymbol(intrinsic) => (
            "helper_symbol".to_string(),
            format!("{:?}", intrinsic),
            vec![],
        ),
    };

    out.push(PseudoSnapshotNode {
        id,
        pseudo_node_id,
        kind,
        summary,
        children,
    });
    id
}

/// Match every node of `from` to at most one node of `to`, and say by WHICH of
/// the three match routes.
///
/// The route tag is a pure widening of the returned tuple: each pass stamps
/// its own constant, no pass reads a route, and no route participates in
/// `used_from`/`used_to`, so the tag cannot change which nodes pair up.
fn build_node_matches(
    from: &PseudoSnapshot,
    to: &PseudoSnapshot,
) -> (Vec<(u32, u32, Route)>, Vec<u32>, Vec<u32>) {
    let mut from_map: HashMap<String, Vec<u32>> = HashMap::new();
    let mut to_map: HashMap<String, Vec<u32>> = HashMap::new();
    let mut from_by_id = vec![None; from.nodes.len() + 1];
    let mut to_by_id = vec![None; to.nodes.len() + 1];
    let mut from_normalized_summaries = vec![String::new(); from.nodes.len() + 1];
    let mut to_normalized_summaries = vec![String::new(); to.nodes.len() + 1];

    for node in &from.nodes {
        let node_index = node.id as usize;
        from_by_id[node_index] = Some(node);
        from_normalized_summaries[node_index] = normalize_summary(&node.summary);
        from_map.entry(node_sig(node)).or_default().push(node.id);
    }
    for node in &to.nodes {
        let node_index = node.id as usize;
        to_by_id[node_index] = Some(node);
        to_normalized_summaries[node_index] = normalize_summary(&node.summary);
        to_map.entry(node_sig(node)).or_default().push(node.id);
    }

    let mut matches = Vec::new();
    let mut used_from = vec![false; from.nodes.len() + 1];
    let mut used_to = vec![false; to.nodes.len() + 1];

    // Anchor pass: `pseudo_node_id` is a pure (tree-path, kind) hash, so a
    // node whose position and kind survive a pass keeps its id verbatim.
    // Matching those first pins every untouched region exactly and leaves
    // only genuinely rewritten nodes to the coarser signature/fuzzy passes —
    // which otherwise scramble same-signature leaves (`var|x_#|0` etc.) by
    // list position and bleed owned lineage onto unrelated nodes.
    let mut to_by_pseudo_id = HashMap::<PseudoNodeId, u32>::with_capacity(to.nodes.len());
    for node in &to.nodes {
        to_by_pseudo_id.insert(node.pseudo_node_id, node.id);
    }
    for node in &from.nodes {
        let Some(&to_id) = to_by_pseudo_id.get(&node.pseudo_node_id) else {
            continue;
        };
        if used_to[to_id as usize] {
            continue;
        }
        used_from[node.id as usize] = true;
        used_to[to_id as usize] = true;
        matches.push((node.id, to_id, Route::Anchor));
    }

    for (sig, left_ids) in &from_map {
        if let Some(right_ids) = to_map.get(sig) {
            let left_free: Vec<u32> = left_ids
                .iter()
                .copied()
                .filter(|id| !used_from[*id as usize])
                .collect();
            let right_free: Vec<u32> = right_ids
                .iter()
                .copied()
                .filter(|id| !used_to[*id as usize])
                .collect();
            let pair_count = left_free.len().min(right_free.len());
            for i in 0..pair_count {
                let left_id = left_free[i];
                let right_id = right_free[i];
                used_from[left_id as usize] = true;
                used_to[right_id as usize] = true;
                matches.push((left_id, right_id, Route::SigPosition));
            }
        }
    }

    let mut fuzzy_candidates: Vec<(f32, u32, u32)> = Vec::new();
    for left in &from.nodes {
        if used_from[left.id as usize] {
            continue;
        }
        for right in &to.nodes {
            if used_to[right.id as usize] {
                continue;
            }
            if left.kind != right.kind || left.children.len() != right.children.len() {
                continue;
            }

            let score = fuzzy_similarity(
                left,
                right,
                &from_by_id,
                &to_by_id,
                &from_normalized_summaries,
                &to_normalized_summaries,
            );
            if score >= 0.55 {
                fuzzy_candidates.push((score, left.id, right.id));
            }
        }
    }

    fuzzy_candidates.sort_by(|a, b| {
        b.0.total_cmp(&a.0)
            .then_with(|| a.1.cmp(&b.1))
            .then_with(|| a.2.cmp(&b.2))
    });

    for (_, left_id, right_id) in fuzzy_candidates {
        if used_from[left_id as usize] || used_to[right_id as usize] {
            continue;
        }
        used_from[left_id as usize] = true;
        used_to[right_id as usize] = true;
        matches.push((left_id, right_id, Route::Fuzzy));
    }

    let removed = from
        .nodes
        .iter()
        .filter(|node| !used_from[node.id as usize])
        .map(|node| node.id)
        .collect();
    let added = to
        .nodes
        .iter()
        .filter(|node| !used_to[node.id as usize])
        .map(|node| node.id)
        .collect();

    (matches, removed, added)
}

/// Classify every match of one window by what it did to the parent
/// relationship — see [`ParentVerdict`] for what each arm means and why two of
/// them are benign.
///
/// PURE and READ-ONLY: it reads the `matches` vector [`build_node_matches`]
/// produced and touches nothing else, so it cannot move a match. Called only
/// when the opt-in recorder is present.
///
/// Cost is one parent map per side plus one depth vector, all O(nodes), and an
/// ancestry walk only on the pairs whose parents disagree.
pub(crate) fn parent_consistency_census(
    from: &PseudoSnapshot,
    to: &PseudoSnapshot,
    matches: &[(u32, u32, Route)],
) -> ParentConsistencyCensus {
    let from_parent = build_parent_map(from);
    let to_parent = build_parent_map(to);
    let match_map: HashMap<u32, u32> = matches
        .iter()
        .map(|&(from_id, to_id, _)| (from_id, to_id))
        .collect();
    let to_depth = build_depth_table(to);

    let mut census = ParentConsistencyCensus::default();
    for &(left, right, route) in matches {
        let verdict = match (from_parent.get(&left), to_parent.get(&right)) {
            // Both roots: the relationship they arrived with is "none", and it
            // survived.
            (None, None) => ParentVerdict::Consistent,
            (None, Some(_)) | (Some(_), None) => ParentVerdict::RootAsymmetric,
            (Some(&left_parent), Some(&right_parent)) => match match_map.get(&left_parent) {
                // A `from` node absent from `match_map` is precisely a removed
                // node — `build_node_matches` derives `removed` from the same
                // `used_from` the matches were pushed under.
                None => ParentVerdict::ParentRemoved,
                Some(&image) if image == right_parent => ParentVerdict::Consistent,
                Some(&image) => {
                    if related_in_ancestry(image, right_parent, &to_parent, &to_depth) {
                        ParentVerdict::WithinAncestry
                    } else {
                        ParentVerdict::UnrelatedParent
                    }
                }
            },
        };
        census.note(verdict, route);
    }
    census
}

/// Depth of every node of `snapshot`, indexed by node id, with `u32::MAX` for
/// ids the snapshot does not use.
///
/// Snapshot nodes are stored POST-ORDER, so a parent always sits after its
/// descendants and the REVERSED order is a valid top-down order: one
/// backwards pass assigns every depth. The obvious per-node walk up the
/// parent map is `O(depth x nodes)`, which is enough to regress debugger
/// startup.
fn build_depth_table(snapshot: &PseudoSnapshot) -> Vec<u32> {
    let mut depth = vec![u32::MAX; snapshot.nodes.len() + 1];
    // The root is stored last, and it is the only node with no parent.
    if let Some(root) = snapshot.nodes.last() {
        depth[root.id as usize] = 0;
    }
    for node in snapshot.nodes.iter().rev() {
        let own = depth[node.id as usize];
        if own == u32::MAX {
            continue;
        }
        for &child in &node.children {
            depth[child as usize] = own.saturating_add(1);
        }
    }
    depth
}

/// Is one of `left`/`right` an ancestor of the other in the tree `parents` and
/// `depth` describe? Reflexive — a node is related to itself — though the one
/// caller has already handled equality.
///
/// Walks the DEEPER node up to the shallower one's depth and compares, so the
/// cost is the depth difference and not the depth.
fn related_in_ancestry(left: u32, right: u32, parents: &HashMap<u32, u32>, depth: &[u32]) -> bool {
    let (Some(&left_depth), Some(&right_depth)) =
        (depth.get(left as usize), depth.get(right as usize))
    else {
        return false;
    };
    if left_depth == u32::MAX || right_depth == u32::MAX {
        return false;
    }
    let (mut deeper, shallower, mut to_climb) = if left_depth >= right_depth {
        (left, right, left_depth - right_depth)
    } else {
        (right, left, right_depth - left_depth)
    };
    while to_climb > 0 {
        let Some(&parent) = parents.get(&deeper) else {
            return false;
        };
        deeper = parent;
        to_climb -= 1;
    }
    deeper == shallower
}

fn propagate_removed_wrapper_lineage(
    from: &PseudoSnapshot,
    to: &PseudoSnapshot,
    matches: &[(u32, u32, Route)],
    removed: &[u32],
    prev_lineage: &HashMap<u32, MidLineage>,
    next_lineage: &mut HashMap<u32, MidLineage>,
    mut recorder: Option<&mut RouteRecorder>,
    window: u32,
    is_bridge: bool,
) {
    // The route a match arrived by is irrelevant to a donation — a donation
    // targets a node that survived, however it survived — so the tag is
    // dropped here rather than threaded on.
    let match_map: HashMap<u32, u32> = matches
        .iter()
        .map(|&(from_id, to_id, _)| (from_id, to_id))
        .collect();
    let by_id: HashMap<u32, &PseudoSnapshotNode> =
        from.nodes.iter().map(|node| (node.id, node)).collect();
    let from_parent_map = build_parent_map(from);
    let to_parent_map = build_parent_map(to);
    // Snapshot nodes are post-order, so the root is stored last. Used as a
    // no-loss fallback donation target when a removed node has no matched
    // context at all (nothing matched between the snapshots): owned lineage
    // must land SOMEWHERE or its mids lose source coverage permanently.
    let to_root_id = to.nodes.last().map(|node| node.id);
    // Removed nodes overwhelmingly share ancestors, and the subtree search is a
    // pure function of data that is fixed for this call.
    let mut descendant_cache: HashMap<u32, Option<u32>> = HashMap::new();

    for &removed_id in removed {
        let Some(lineage) = prev_lineage.get(&removed_id) else {
            continue;
        };
        // Descendant-first: a removed node's own mids describe the construct
        // at its position, and the surviving image of its subtree (single
        // match, or LCA of several) is the tightest such position in `to`.
        // The ancestor walk is the fallback for nodes whose whole subtree
        // vanished; the `to`-root catches full-rewrite windows so owned
        // lineage is never dropped.
        let descendant_target = match descendant_cache.get(&removed_id) {
            Some(cached) => *cached,
            None => {
                let computed =
                    descendant_transfer_target(removed_id, &by_id, &match_map, &to_parent_map);
                descendant_cache.insert(removed_id, computed);
                computed
            }
        };
        let ancestor_target = ancestor_transfer_target(
            removed_id,
            &by_id,
            &from_parent_map,
            &match_map,
            &to_parent_map,
            &mut descendant_cache,
        );
        // Which donation branch fired is read off the SAME `or` chain that
        // picks the target rather than recomputed from a second set of
        // conditions, which could report a branch the donation did not take.
        let (target_to_id, route) = match (descendant_target, ancestor_target, to_root_id) {
            (Some(target), _, _) => (target, Route::DonateDescLca),
            (None, Some(target), _) => (target, Route::DonateAncestor),
            (None, None, Some(target)) => (target, Route::DonateToRoot),
            (None, None, None) => continue,
        };
        lineage_merge(next_lineage.entry(target_to_id).or_default(), lineage);
        if let Some(recorder) = recorder.as_deref_mut() {
            recorder.note_donation(route);
            recorder.note_transfer(lineage, route, window, is_bridge);
        }
    }
}

fn descendant_transfer_target(
    root_id: u32,
    by_id: &HashMap<u32, &PseudoSnapshotNode>,
    match_map: &HashMap<u32, u32>,
    to_parent_map: &HashMap<u32, u32>,
) -> Option<u32> {
    let mut stack = Vec::new();
    {
        let root = by_id.get(&root_id)?;
        stack.extend(root.children.iter().copied());
    }

    let mut matched_targets = BTreeSet::new();

    while let Some(node_id) = stack.pop() {
        if let Some(&to_id) = match_map.get(&node_id) {
            matched_targets.insert(to_id);
        }

        if let Some(node) = by_id.get(&node_id) {
            stack.extend(node.children.iter().copied());
        }
    }

    if matched_targets.is_empty() {
        return None;
    }
    if matched_targets.len() == 1 {
        return matched_targets.iter().next().copied();
    }

    lowest_common_ancestor(&matched_targets, to_parent_map)
}

fn build_parent_map(snapshot: &PseudoSnapshot) -> HashMap<u32, u32> {
    let mut parents = HashMap::new();
    for node in &snapshot.nodes {
        for &child_id in &node.children {
            parents.insert(child_id, node.id);
        }
    }
    parents
}

fn ancestor_transfer_target(
    node_id: u32,
    by_id: &HashMap<u32, &PseudoSnapshotNode>,
    from_parent_map: &HashMap<u32, u32>,
    match_map: &HashMap<u32, u32>,
    to_parent_map: &HashMap<u32, u32>,
    descendant_cache: &mut HashMap<u32, Option<u32>>,
) -> Option<u32> {
    // Walk up looking for a matched ancestor. That answer wins outright, so no
    // subtree work is needed while it is still possible.
    let mut chain = Vec::new();
    let mut current = node_id;
    while let Some(&parent_id) = from_parent_map.get(&current) {
        if let Some(&matched_target) = match_map.get(&parent_id) {
            return Some(matched_target);
        }
        chain.push(parent_id);
        // A parent map derived from a tree cannot produce a chain longer than
        // the tree; this only stops a malformed map being walked forever.
        if chain.len() > by_id.len() {
            break;
        }
        current = parent_id;
    }

    // No ancestor matched. Scanning every ancestor's subtree on the way up and
    // keeping the highest one's result costs O(depth x nodes) per removed node,
    // enough to dominate debugger startup. Searching from the top and stopping
    // at the first hit yields the same answer, and the cache collapses the
    // ancestors removed nodes share.
    for &ancestor in chain.iter().rev() {
        let target = match descendant_cache.get(&ancestor) {
            Some(cached) => *cached,
            None => {
                let computed =
                    descendant_transfer_target(ancestor, by_id, match_map, to_parent_map);
                descendant_cache.insert(ancestor, computed);
                computed
            }
        };
        if target.is_some() {
            return target;
        }
    }

    None
}

fn lowest_common_ancestor(node_ids: &BTreeSet<u32>, parent_map: &HashMap<u32, u32>) -> Option<u32> {
    let mut iter = node_ids.iter().copied();
    let first = iter.next()?;
    let mut candidate_chain = ancestor_chain(first, parent_map);

    for node_id in iter {
        let current_chain = ancestor_chain(node_id, parent_map);
        candidate_chain.retain(|ancestor| current_chain.contains(ancestor));
        if candidate_chain.is_empty() {
            return None;
        }
    }

    candidate_chain.first().copied()
}

fn ancestor_chain(node_id: u32, parent_map: &HashMap<u32, u32>) -> Vec<u32> {
    let mut chain = vec![node_id];
    let mut current = node_id;
    while let Some(&parent_id) = parent_map.get(&current) {
        chain.push(parent_id);
        current = parent_id;
    }
    chain
}

/// Union child lineage into parents in one post-order pass.
///
/// Test-only: the projection loop never bubbles owned lineage up (see
/// `project_final_pseudo_to_mid`); containment is applied once, at
/// emission, by `emit_containment_lineage`. Kept as an executable
/// description of that behavior.
#[cfg(test)]
fn inherit_child_lineage(
    snapshot: &PseudoSnapshot,
    lineage_by_node: &mut HashMap<u32, MidLineage>,
) {
    for node in &snapshot.nodes {
        if node.children.is_empty() {
            continue;
        }

        let inherited = if node.children.len() == 1 {
            lineage_by_node.get(&node.children[0]).cloned()
        } else if node
            .children
            .iter()
            .all(|child_id| lineage_by_node.contains_key(child_id))
        {
            let mut merged = MidLineage::new();
            for child_id in &node.children {
                if let Some(lineage) = lineage_by_node.get(child_id) {
                    lineage_merge(&mut merged, lineage);
                }
            }
            Some(merged)
        } else {
            None
        };

        if let Some(inherited) = inherited {
            lineage_merge(lineage_by_node.entry(node.id).or_default(), &inherited);
        }
    }
}

fn node_sig(node: &PseudoSnapshotNode) -> String {
    format!("{}|{}|{}", node.kind, node.summary, node.children.len())
}

fn fuzzy_similarity(
    left: &PseudoSnapshotNode,
    right: &PseudoSnapshotNode,
    from_by_id: &[Option<&PseudoSnapshotNode>],
    to_by_id: &[Option<&PseudoSnapshotNode>],
    from_normalized_summaries: &[String],
    to_normalized_summaries: &[String],
) -> f32 {
    if left.summary == right.summary {
        return 0.92;
    }

    let left_norm = &from_normalized_summaries[left.id as usize];
    let right_norm = &to_normalized_summaries[right.id as usize];
    let summary_score = if left_norm == right_norm {
        0.82
    } else if left_norm.starts_with(right_norm.as_str())
        || right_norm.starts_with(left_norm.as_str())
    {
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
        .filter(|(left_id, right_id)| {
            let left_kind = from_by_id
                .get(**left_id as usize)
                .copied()
                .flatten()
                .map(|node| node.kind.as_str())
                .unwrap_or_default();
            let right_kind = to_by_id
                .get(**right_id as usize)
                .copied()
                .flatten()
                .map(|node| node.kind.as_str())
                .unwrap_or_default();
            left_kind == right_kind
        })
        .count();

    let arity = left.children.len().max(1) as f32;
    let child_bonus = (child_kind_match as f32 / arity) * 0.08;
    (summary_score + child_bonus).min(0.95)
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

#[cfg(test)]
mod tests;
