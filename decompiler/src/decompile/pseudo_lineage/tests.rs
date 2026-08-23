use super::*;
use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::mid::expr_id::MidExprId;
use crate::pseudo::var_id::VarId;

// ===== ROUTE PROVENANCE =====
//
// Each test below forces ONE of the six routes with a snapshot pair whose
// matching outcome is decided by construction, and asserts on the RECORDER
// only — never on the emitted map. `emit_containment_lineage` runs after the
// window loop, so mutating its child union moves the emitted map and cannot
// move a single route; the neighbour that DOES read the emitted map
// (`project_chained_pseudo_to_mid_carries_owned_lineage_across_a_path_hash_
// shifting_wrap`) is what keeps that layer pinned.
//
// `pseudo_node_id` is `hash(path, kind_tag)` and reads NO summary, so the
// anchor pass matches on position and kind alone. Every construction below
// turns on that fact:
//   * same tree twice           -> every node anchors                     (R1)
//   * a node whose path shifts but whose `kind|summary|arity` survives     (R2)
//   * a node whose summary also changed, leaving only kind+arity+fuzz      (R3)
//   * a removed wrapper whose subtree survived                            (R4)
//   * a removed node whose whole subtree vanished, under a matched parent  (R5)
//   * a window in which nothing matches at all                            (R6)

/// Seed one distinct mid per node of `expr`, keyed by node id.
///
/// Paths are walked here rather than written out per node, so a path that
/// does not exist panics in `descend` rather than seeding nothing and
/// leaving the assertion below to report a missing route.
fn seed_by_path(
    expr: &PseudoExpr,
    paths: &[(&[u32], u32)],
) -> HashMap<PseudoNodeId, Vec<MidExprId>> {
    let mut initial = HashMap::new();
    for (path, mid) in paths {
        let node = descend(expr, path);
        initial.insert(
            node.provenance_node_id_for_path(path),
            vec![MidExprId::new(*mid)],
        );
    }
    initial
}

/// The sub-expression at `path`, over the SAME child order `flatten_pseudo`
/// uses. Only the shapes the route tests build are supported; anything else
/// panics rather than silently descending elsewhere.
fn descend<'a>(expr: &'a PseudoExpr, path: &[u32]) -> &'a PseudoExpr {
    let Some((head, rest)) = path.split_first() else {
        return expr;
    };
    let child = match (expr, head) {
        (PseudoExpr::Let { value, .. }, 0) => value.as_ref(),
        (PseudoExpr::Let { body, .. }, 1) => body.as_ref(),
        (PseudoExpr::Delay(inner), 0) | (PseudoExpr::Force(inner), 0) => inner.as_ref(),
        (PseudoExpr::Lambda { body, .. }, 0) => body.as_ref(),
        other => panic!("route-test fixture has no child at {head} of {:?}", other.0),
    };
    descend(child, rest)
}

/// Run a projection with the recorder ON, so one test can pin a route AND
/// check that recording it changed nothing.
fn record(
    snapshots: &[PseudoSnapshot],
    initial: &HashMap<PseudoNodeId, Vec<MidExprId>>,
) -> (
    RouteRecorder,
    HashMap<PseudoNodeId, Vec<MidExprId>>,
    Vec<MidExprId>,
) {
    let mut recorder = RouteRecorder::new();
    let (emitted, _, heirs) = project_lineage(snapshots, initial, None, false, Some(&mut recorder));
    (recorder, emitted, heirs.heir_mids)
}

fn worst(recorder: &RouteRecorder, mid: u32) -> Option<Route> {
    recorder
        .mids()
        .get(&MidExprId::new(mid))
        .map(|provenance| provenance.worst_route)
}

/// `let k = delay(a) { b }` — the shape three of the six routes are read off.
fn let_over_delay() -> PseudoExpr {
    PseudoExpr::let_bind_with_id(
        "k",
        VarId::fresh_binding(),
        PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
            "a",
            VarId::fresh_binding(),
        ))),
        PseudoExpr::var_with_id("b", VarId::fresh_binding()),
    )
}

/// The same `let`, with the delay stripped: `let k = a { b }`.
fn let_over_var() -> PseudoExpr {
    PseudoExpr::let_bind_with_id(
        "k",
        VarId::fresh_binding(),
        PseudoExpr::var_with_id("a", VarId::fresh_binding()),
        PseudoExpr::var_with_id("b", VarId::fresh_binding()),
    )
}

/// R1. Both snapshots are the same tree, so every node's (path, kind) survives
/// and the anchor pass claims all of them before any heuristic runs.
///
/// MUTATION: delete the anchor pass and these become `SigPosition` with the
/// EMITTED MAP unchanged — identical trees fall in identical signature buckets
/// — which is why the route is recorded rather than inferred from the map.
#[test]
fn the_anchor_route_is_recorded_when_a_node_keeps_its_exact_path_and_kind() {
    let expr = let_over_delay();
    let initial = seed_by_path(&expr, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);
    let snapshots = [snapshot_expr(&expr), snapshot_expr(&expr)];

    let (recorder, _, _) = record(&snapshots, &initial);

    for mid in 1..=4 {
        assert_eq!(
            worst(&recorder, mid),
            Some(Route::Anchor),
            "mid {mid} moved between two identical trees by something other than exact identity"
        );
    }
    assert_eq!(recorder.windows().len(), 1);
    assert_eq!(recorder.windows()[0].node_matches[Route::Anchor.index()], 4);
    assert_eq!(recorder.windows()[0].removed, 0);
}

/// R2. Stripping the `Delay` moves `a` from `[0,0]` to `[0]`: its node id
/// changes and the anchor pass cannot see it — its signature (`var|a|0`)
/// is unique in both buckets, so the coarse pass pairs it BY LIST INDEX.
///
/// MUTATION: delete the signature pass and `a` falls through to `Fuzzy`
/// (same kind, same arity, identical summary scores 0.92).
#[test]
fn the_sig_position_route_is_recorded_when_a_path_shifts_but_the_signature_survives() {
    let from = let_over_delay();
    let to = let_over_var();
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    assert_eq!(worst(&recorder, 3), Some(Route::SigPosition));
    // The two nodes whose path did not move are still anchors, so the test
    // pins the DISTINCTION and not merely "some route was recorded".
    assert_eq!(worst(&recorder, 1), Some(Route::Anchor));
    assert_eq!(worst(&recorder, 4), Some(Route::Anchor));
    assert_eq!(
        recorder.windows()[0].node_matches[Route::SigPosition.index()],
        1
    );
}

/// R3. `delay(x)` collapses to `y`: path AND summary both changed, so neither
/// the anchor pass nor the signature bucket can reach it. Only kind and arity
/// survive, and `fuzzy_similarity` scores the pair 0.56, over the 0.55 floor.
///
/// MUTATION: raise the floor to 0.95 and nothing in the window matches at all
/// — the mid falls all the way to `DonateToRoot`.
#[test]
fn the_fuzzy_route_is_recorded_when_only_kind_arity_and_a_similar_summary_survive() {
    let from = PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
        "x",
        VarId::fresh_binding(),
    )));
    let to = PseudoExpr::var_with_id("y", VarId::fresh_binding());
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    assert_eq!(worst(&recorder, 2), Some(Route::Fuzzy));
    assert_eq!(recorder.windows()[0].node_matches[Route::Fuzzy.index()], 1);
}

/// R4. The removed `Delay` wrapper's own mid is donated to the surviving image
/// of its SUBTREE — here a single matched survivor, the `a` that moved up.
///
/// MUTATION: swap descendant-first for ancestor-first in the `or` chain and
/// the route becomes `DonateAncestor`, since the `Delay`'s parent `Let` is
/// matched too. This is the test that pins the ORDER of those two branches.
#[test]
fn the_donate_desc_lca_route_is_recorded_for_a_removed_wrapper_whose_subtree_survived() {
    let from = let_over_delay();
    let to = let_over_var();
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    assert_eq!(worst(&recorder, 2), Some(Route::DonateDescLca));
    assert_eq!(
        recorder.windows()[0].donations[Route::DonateDescLca.index()],
        1
    );
    assert_eq!(
        recorder.windows()[0].donations[Route::DonateAncestor.index()],
        0,
        "ancestor-first would have claimed this donation"
    );
    assert_eq!(recorder.windows()[0].removed, 1);
}

/// R5. `let k = delay(a) { b }` becomes `let k = 0 { b }`: the whole `delay(a)`
/// subtree vanishes, so no descendant of either removed node survives and the
/// donation falls to the nearest MATCHED ANCESTOR, the `Let`.
///
/// MUTATION: remove the ancestor branch and both mids land on the `to` root as
/// `DonateToRoot`. The branch ORDER is pinned by R4 instead — descendant-first
/// has no answer here, so swapping the two changes nothing.
#[test]
fn the_donate_ancestor_route_is_recorded_when_a_whole_subtree_vanished() {
    let from = let_over_delay();
    let to = PseudoExpr::let_bind_with_id(
        "k",
        VarId::fresh_binding(),
        PseudoExpr::Int(0.into()),
        PseudoExpr::var_with_id("b", VarId::fresh_binding()),
    );
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    assert_eq!(worst(&recorder, 2), Some(Route::DonateAncestor));
    assert_eq!(worst(&recorder, 3), Some(Route::DonateAncestor));
    assert_eq!(
        recorder.windows()[0].donations[Route::DonateAncestor.index()],
        2
    );
    assert_eq!(
        recorder.windows()[0].donations[Route::DonateToRoot.index()],
        0
    );
}

/// R6. `delay(x)` becomes `7`: no node matches by any of the three passes, so
/// there is neither a surviving descendant nor a matched ancestor and the
/// no-loss fallback puts every mid on the `to` root — the one route that is
/// not a position claim in any sense.
#[test]
fn the_donate_to_root_route_is_recorded_when_a_window_matches_nothing() {
    let from = PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
        "x",
        VarId::fresh_binding(),
    )));
    let to = PseudoExpr::Int(7.into());
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    assert_eq!(worst(&recorder, 1), Some(Route::DonateToRoot));
    assert_eq!(worst(&recorder, 2), Some(Route::DonateToRoot));
    assert_eq!(recorder.windows()[0].node_matches.iter().sum::<usize>(), 0);
    assert_eq!(
        recorder.windows()[0].donations[Route::DonateToRoot.index()],
        2
    );
}

/// `worst_route` is a MAX over the chain, not the last hop.
///
/// The window that degrades `a` runs FIRST and an anchor window runs after it,
/// so an implementation that overwrote instead of maxing would report `Anchor`
/// — a mid's best hop in place of its worst.
#[test]
fn worst_route_is_the_max_over_the_whole_chain_and_not_the_last_hop() {
    let from = let_over_delay();
    let to = let_over_var();
    let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &initial);

    let provenance = recorder
        .mids()
        .get(&MidExprId::new(3))
        .copied()
        .expect("mid 3 moved in both windows");
    assert_eq!(provenance.worst_route, Route::SigPosition);
    assert_eq!(provenance.first_non_anchor_window, Some(0));
    assert_eq!(provenance.hops, 2);
    // The second window really did re-anchor it, so the max above is a max over
    // two DIFFERENT routes and not a chain that never improved.
    assert_eq!(recorder.windows()[1].node_matches[Route::Anchor.index()], 3);
}

/// Exactly one window is the bridge, it leads the chained projection, and it is
/// the one the wrap made unreachable by exact id.
///
/// A bridge window exists iff a carry came in, so this pins that the carry path
/// and only the carry path produces one, and that the wrap denies the anchor
/// pass at that boundary.
#[test]
fn the_spliced_bridge_window_is_the_only_window_flagged_as_one() {
    // The PRODUCTION shape: `wrap_validator_entry_for_render` puts a
    // `Let { name: "decompiled", .. }` over the validator entry LAMBDA, so the
    // two roots differ in kind as well as the interior differing in path.
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("p", VarId::fresh_binding())],
        body: PBox::new(let_over_delay()),
    };
    let initial = seed_by_path(
        &inner,
        &[
            (&[], 1),
            (&[0], 2),
            (&[0, 0], 3),
            (&[0, 0, 0], 4),
            (&[0, 1], 5),
        ],
    );

    let mut recorder = RouteRecorder::new();
    let pass_snapshots = vec![snapshot_expr(&inner), snapshot_expr(&inner)];
    let (emitted, carry) =
        project_pseudo_to_mid_carrying(&pass_snapshots, &initial, Some(&mut recorder));
    let carry = carry.expect("a carrying projection must produce a carry");

    let wrapped = PseudoExpr::let_bind_with_id(
        "decompiled",
        VarId::fresh_binding(),
        inner.clone(),
        PseudoExpr::Unit,
    );
    let chained = [snapshot_expr(&wrapped), snapshot_expr(&wrapped)];
    let (_, _) = project_chained_pseudo_to_mid_with_heirs(
        &chained,
        &emitted,
        Some(carry),
        Some(&mut recorder),
    );

    let bridges: Vec<&WindowRouteCensus> = recorder
        .windows()
        .iter()
        .filter(|window| window.is_bridge)
        .collect();
    assert_eq!(bridges.len(), 1, "exactly one window crosses the wrap");
    // Window indices are continuous across the two chained calls: the pass
    // projection's window is 0, the bridge is spliced in as 1, and the chained
    // call's own window is 2. A recorder created inside the second call would
    // restart at 0, making the bridge indistinguishable from a pass window.
    assert_eq!(bridges[0].window, 1);
    assert_eq!(recorder.windows().len(), 3);
    // The wrap put the whole program one level down, so every node's path hash
    // shifted and NOTHING can anchor across it. That is the structural claim
    // the bridge row exists to report.
    assert_eq!(
        bridges[0].node_matches[Route::Anchor.index()],
        0,
        "a wrap that shifts every path hash cannot leave an exact-id match"
    );
    assert!(bridges[0].node_matches.iter().sum::<usize>() > 0);
}

/// The anchor pass matches on `(path, kind)` and reads NO summary, so two nodes
/// that are not the same node anchor to each other whenever a rewrite leaves
/// the same kind at the same path.
///
/// The wrap boundary is where that is guaranteed: the pre-wrap root and the
/// `Let` the wrapper introduces are both at path `[]`, so they anchor although
/// the wrapper is a NEW node that lowered nothing. Any reading of the census
/// that treats an anchor as proof of identity has to survive this.
#[test]
fn the_anchor_pass_matches_a_same_kind_root_across_a_wrap_that_replaced_it() {
    let inner = let_over_delay();
    let initial = seed_by_path(&inner, &[(&[], 1), (&[0], 2), (&[0, 0], 3), (&[1], 4)]);

    let mut recorder = RouteRecorder::new();
    let pass_snapshots = vec![snapshot_expr(&inner), snapshot_expr(&inner)];
    let (emitted, carry) =
        project_pseudo_to_mid_carrying(&pass_snapshots, &initial, Some(&mut recorder));
    let wrapped = PseudoExpr::let_bind_with_id(
        "decompiled",
        VarId::fresh_binding(),
        inner.clone(),
        PseudoExpr::Unit,
    );
    let chained = [snapshot_expr(&wrapped), snapshot_expr(&wrapped)];
    let (_, _) =
        project_chained_pseudo_to_mid_with_heirs(&chained, &emitted, carry, Some(&mut recorder));

    let bridge = recorder
        .windows()
        .iter()
        .find(|window| window.is_bridge)
        .expect("bridge window");
    assert_eq!(
        bridge.node_matches[Route::Anchor.index()],
        1,
        "the two roots share (path, kind) and so anchor to one another"
    );
    // …and only the roots anchor: the interior re-matches by signature.
    assert!(bridge.node_matches[Route::SigPosition.index()] > 0);
}

/// THE INSTRUMENT DOES NOT CONTAMINATE WHAT IT MEASURES.
///
/// Same snapshots, same seeds, recorder off and on: the emitted map and the
/// heir set must be identical, over a chain exercising all three donation
/// branches.
#[test]
fn the_route_recorder_changes_neither_the_emitted_map_nor_the_heir_set() {
    for (from, to) in [
        (let_over_delay(), let_over_var()),
        (
            let_over_delay(),
            PseudoExpr::let_bind_with_id(
                "k",
                VarId::fresh_binding(),
                PseudoExpr::Int(0.into()),
                PseudoExpr::var_with_id("b", VarId::fresh_binding()),
            ),
        ),
        (
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
                "x",
                VarId::fresh_binding(),
            ))),
            PseudoExpr::Int(7.into()),
        ),
    ] {
        let initial = seed_by_path(&from, &[(&[], 1), (&[0], 2)]);
        let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

        let (recorder, emitted_on, heirs_on) = record(&snapshots, &initial);
        let (emitted_off, _, heirs_off) = project_lineage(&snapshots, &initial, None, false, None);

        assert_eq!(emitted_on, emitted_off);
        assert_eq!(heirs_on, heirs_off.heir_mids);
        // A recorder that recorded nothing would pass the two assertions above
        // for free.
        assert!(!recorder.mids().is_empty());
        assert_eq!(recorder.windows().len(), 1);
    }
}

#[test]
fn project_final_pseudo_to_mid_transfers_removed_delay_lineage_to_surviving_child() {
    let from = PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
        "x",
        VarId::fresh_binding(),
    )));
    let to = match from.clone() {
        PseudoExpr::Delay(inner) => inner.into_inner(),
        other => panic!("expected delay, got {other:?}"),
    };

    let from_snapshot = snapshot_expr(&from);
    let to_snapshot = snapshot_expr(&to);

    let mut initial = HashMap::new();
    initial.insert(
        from.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(
        match &from {
            PseudoExpr::Delay(inner) => inner.provenance_node_id_for_path(&[0]),
            other => panic!("expected delay, got {other:?}"),
        },
        vec![MidExprId::new(2)],
    );

    let projected = project_final_pseudo_to_mid(&[from_snapshot, to_snapshot], &initial);
    let final_lineage = projected
        .get(&to.provenance_node_id_for_path(&[]))
        .expect("final var should keep lineage");

    assert!(final_lineage.contains(&MidExprId::new(1)));
    assert!(final_lineage.contains(&MidExprId::new(2)));
}

#[test]
fn project_final_pseudo_to_mid_transfers_removed_force_delay_chain_lineage_to_surviving_child() {
    let from = PseudoExpr::Force(PBox::new(PseudoExpr::Delay(PBox::new(
        PseudoExpr::var_with_id("x", VarId::fresh_binding()),
    ))));
    let to = PseudoExpr::var_with_id("x", VarId::fresh_binding());

    let from_snapshot = snapshot_expr(&from);
    let to_snapshot = snapshot_expr(&to);

    let mut initial = HashMap::new();
    initial.insert(
        from.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("tmp"))).provenance_node_id_for_path(&[0]),
        vec![MidExprId::new(2)],
    );
    initial.insert(
        PseudoExpr::var("tmp").provenance_node_id_for_path(&[0, 0]),
        vec![MidExprId::new(3)],
    );

    let projected = project_final_pseudo_to_mid(&[from_snapshot, to_snapshot.clone()], &initial);
    let final_lineage = projected
        .get(&to.provenance_node_id_for_path(&[]))
        .expect("final var should keep lineage");

    assert!(final_lineage.contains(&MidExprId::new(1)));
    assert!(final_lineage.contains(&MidExprId::new(2)));
    assert!(final_lineage.contains(&MidExprId::new(3)));
}

#[test]
fn project_final_pseudo_to_mid_merges_parent_and_child_lineage_in_single_snapshot() {
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        VarId::fresh_binding(),
        PseudoExpr::Int(1.into()),
        PseudoExpr::var_with_id("x", VarId::fresh_binding()),
    );
    let (value_node_id, body_node_id) = match &expr {
        PseudoExpr::Let { value, body, .. } => (
            value.provenance_node_id_for_path(&[0]),
            body.provenance_node_id_for_path(&[1]),
        ),
        other => panic!("expected let, got {other:?}"),
    };

    let snapshot = snapshot_expr(&expr);
    let mut initial = HashMap::new();
    initial.insert(
        expr.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(value_node_id, vec![MidExprId::new(2)]);
    initial.insert(body_node_id, vec![MidExprId::new(3)]);

    let projected = project_final_pseudo_to_mid(&[snapshot], &initial);
    let final_lineage = projected
        .get(&expr.provenance_node_id_for_path(&[]))
        .expect("let root should keep lineage");

    assert!(final_lineage.contains(&MidExprId::new(1)));
    assert!(final_lineage.contains(&MidExprId::new(2)));
    assert!(final_lineage.contains(&MidExprId::new(3)));
}

/// `wrap_validator_entry_for_render` separates the pipeline's two projections
/// and moves the whole tree one level down, shifting the (path, kind) node-id
/// hash of every node under it. Both halves of that boundary are pinned here:
/// exact-id seeding collapses the program onto the wrapper root, an explicitly
/// passed [`LineageCarry`] preserves per-node ownership instead.
#[test]
fn project_chained_pseudo_to_mid_carries_owned_lineage_across_a_path_hash_shifting_wrap() {
    // `let y = 7 { y + 9 }` — five nodes with pairwise-distinct signatures, so
    // the bridge window can re-match them by structure alone.
    let value = PseudoExpr::Int(7.into());
    let left = PseudoExpr::var_with_id("y", VarId::fresh_binding());
    let right = PseudoExpr::Int(9.into());
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(left.clone()),
        right: PBox::new(right.clone()),
    };
    let inner =
        PseudoExpr::let_bind_with_id("y", VarId::fresh_binding(), value.clone(), body.clone());

    // One distinct mid per node, keyed by pre-wrap node id.
    let mut initial = HashMap::new();
    initial.insert(
        inner.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(
        value.provenance_node_id_for_path(&[0]),
        vec![MidExprId::new(2)],
    );
    initial.insert(
        body.provenance_node_id_for_path(&[1]),
        vec![MidExprId::new(3)],
    );
    initial.insert(
        left.provenance_node_id_for_path(&[1, 0]),
        vec![MidExprId::new(4)],
    );
    initial.insert(
        right.provenance_node_id_for_path(&[1, 1]),
        vec![MidExprId::new(5)],
    );

    // Stands in for the executor's multi-window pass projection.
    let pass_snapshots = vec![
        snapshot_expr(&inner),
        snapshot_expr(&inner),
        snapshot_expr(&inner),
    ];
    let (emitted, carry) = project_pseudo_to_mid_carrying(&pass_snapshots, &initial, None);
    let carry = carry.expect("a carrying projection must produce a carry");

    let wrapped = PseudoExpr::let_bind_with_id(
        "decompiled",
        VarId::fresh_binding(),
        inner.clone(),
        PseudoExpr::Unit,
    );
    let chained = [snapshot_expr(&wrapped), snapshot_expr(&wrapped)];

    let (with_carry, _) =
        project_chained_pseudo_to_mid_with_heirs(&chained, &emitted, Some(carry), None);
    let (without_carry, _) =
        project_chained_pseudo_to_mid_with_heirs(&chained, &emitted, None, None);

    let all_mids = vec![
        MidExprId::new(1),
        MidExprId::new(2),
        MidExprId::new(3),
        MidExprId::new(4),
        MidExprId::new(5),
    ];

    // Without the carry only the wrapper root's id survives the shift (both
    // roots are a `Let` at path `[]`), so it claims the entire program and
    // every interior node is left with nothing — the pooling the carry exists
    // to prevent.
    assert_eq!(
        without_carry.len(),
        1,
        "exact-id seeding should reach exactly the wrapper root, got {:?}",
        without_carry
    );
    assert_eq!(
        without_carry.get(&wrapped.provenance_node_id_for_path(&[])),
        Some(&all_mids)
    );

    // With the carry each node keeps exactly the mid it owned, at its new id.
    assert_eq!(
        with_carry.get(&value.provenance_node_id_for_path(&[0, 0])),
        Some(&vec![MidExprId::new(2)])
    );
    assert_eq!(
        with_carry.get(&left.provenance_node_id_for_path(&[0, 1, 0])),
        Some(&vec![MidExprId::new(4)])
    );
    assert_eq!(
        with_carry.get(&right.provenance_node_id_for_path(&[0, 1, 1])),
        Some(&vec![MidExprId::new(5)])
    );
    assert_eq!(
        with_carry.get(&body.provenance_node_id_for_path(&[0, 1])),
        Some(&vec![
            MidExprId::new(3),
            MidExprId::new(4),
            MidExprId::new(5)
        ])
    );
    // The containment view still holds at the root.
    assert_eq!(
        with_carry.get(&wrapped.provenance_node_id_for_path(&[])),
        Some(&all_mids)
    );
}

/// A carrying projection hands its state back to the caller and keeps nothing:
/// a following projection that is not given the carry must behave exactly as if
/// the carrying projection had never run. There is no implicit channel for it
/// to pick the carry up from.
#[test]
fn project_pseudo_to_mid_carrying_leaves_no_state_for_a_later_call() {
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        VarId::fresh_binding(),
        PseudoExpr::Int(1.into()),
        PseudoExpr::var_with_id("x", VarId::fresh_binding()),
    );
    let mut initial = HashMap::new();
    initial.insert(
        expr.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );

    let snapshots = vec![
        snapshot_expr(&expr),
        snapshot_expr(&expr),
        snapshot_expr(&expr),
    ];
    let (emitted, carry) = project_pseudo_to_mid_carrying(&snapshots, &initial, None);
    assert!(carry.is_some());
    drop(carry);

    let wrapped = PseudoExpr::let_bind_with_id(
        "decompiled",
        VarId::fresh_binding(),
        expr.clone(),
        PseudoExpr::Unit,
    );
    let chained = [snapshot_expr(&wrapped), snapshot_expr(&wrapped)];

    let (uncarried, _) = project_chained_pseudo_to_mid_with_heirs(&chained, &emitted, None, None);
    let standalone = project_final_pseudo_to_mid(&chained, &emitted);
    assert_eq!(uncarried, standalone);
}

#[test]
fn inherit_child_lineage_propagates_through_nested_unary_chain_in_single_pass() {
    let snapshot = snapshot_expr(&PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(
        PseudoExpr::var_with_id("x", VarId::new(1)),
    )))));

    let leaf_node_id = snapshot
        .nodes
        .iter()
        .find(|node| node.kind == "var")
        .map(|node| node.id)
        .expect("var node");
    let root_node_id = snapshot
        .nodes
        .last()
        .map(|node| node.id)
        .expect("root node");

    let mut lineage_by_node = HashMap::<u32, MidLineage>::new();
    lineage_by_node.insert(leaf_node_id, vec![MidExprId::new(7)]);

    inherit_child_lineage(&snapshot, &mut lineage_by_node);

    let root_lineage = lineage_by_node.get(&root_node_id).expect("root lineage");
    assert_eq!(root_lineage, &vec![MidExprId::new(7)]);
}

#[test]
fn project_final_pseudo_to_mid_transfers_removed_apply_to_lca_of_surviving_children() {
    let from = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", VarId::fresh_binding())),
        args: vec![PseudoExpr::Int(1.into())].into(),
    };
    let to = PseudoExpr::BuiltinCall {
        name: BuiltinId::IntAdd,
        args: vec![
            PseudoExpr::var_with_id("f", VarId::fresh_binding()),
            PseudoExpr::Int(1.into()),
        ]
        .into(),
    };

    let from_snapshot = snapshot_expr(&from);
    let to_snapshot = snapshot_expr(&to);

    let mut initial = HashMap::new();
    initial.insert(
        from.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(
        match &from {
            PseudoExpr::Apply { function, .. } => function.provenance_node_id_for_path(&[0]),
            other => panic!("expected apply, got {other:?}"),
        },
        vec![MidExprId::new(2)],
    );
    initial.insert(
        match &from {
            PseudoExpr::Apply { args, .. } => args[0].provenance_node_id_for_path(&[1]),
            other => panic!("expected apply, got {other:?}"),
        },
        vec![MidExprId::new(3)],
    );

    let projected = project_final_pseudo_to_mid(&[from_snapshot, to_snapshot], &initial);
    let final_lineage = projected
        .get(&to.provenance_node_id_for_path(&[]))
        .expect("builtin root should keep lineage");

    assert!(final_lineage.contains(&MidExprId::new(1)));
    assert!(final_lineage.contains(&MidExprId::new(2)));
    assert!(final_lineage.contains(&MidExprId::new(3)));
}

#[test]
fn project_final_pseudo_to_mid_transfers_removed_leaf_and_apply_lineage_via_ancestor_target() {
    let from = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("eq", VarId::fresh_binding())),
            args: vec![PseudoExpr::var_with_id("x", VarId::fresh_binding())].into(),
        }),
        args: vec![PseudoExpr::var_with_id("y", VarId::fresh_binding())].into(),
    };
    let to = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var_with_id("x", VarId::fresh_binding())),
        right: PBox::new(PseudoExpr::var_with_id("y", VarId::fresh_binding())),
    };

    let from_snapshot = snapshot_expr(&from);
    let to_snapshot = snapshot_expr(&to);

    let mut initial = HashMap::new();
    initial.insert(
        from.provenance_node_id_for_path(&[]),
        vec![MidExprId::new(1)],
    );
    initial.insert(
        match &from {
            PseudoExpr::Apply { function, .. } => function.provenance_node_id_for_path(&[0]),
            other => panic!("expected outer apply, got {other:?}"),
        },
        vec![MidExprId::new(2)],
    );
    initial.insert(
        match &from {
            PseudoExpr::Apply { function, .. } => match function.as_ref() {
                PseudoExpr::Apply { function, .. } => function.provenance_node_id_for_path(&[0, 0]),
                other => panic!("expected inner apply, got {other:?}"),
            },
            other => panic!("expected outer apply, got {other:?}"),
        },
        vec![MidExprId::new(3)],
    );

    let projected = project_final_pseudo_to_mid(&[from_snapshot, to_snapshot], &initial);
    let final_lineage = projected
        .get(&to.provenance_node_id_for_path(&[]))
        .expect("binop root should keep lineage");

    assert!(final_lineage.contains(&MidExprId::new(1)));
    assert!(final_lineage.contains(&MidExprId::new(2)));
    assert!(final_lineage.contains(&MidExprId::new(3)));
}

#[test]
fn project_final_pseudo_to_mid_preserves_full_constr_data_list_spine_lineage() {
    let field_x_id = VarId::fresh_binding();
    let field_y_id = VarId::fresh_binding();
    let field_y_binder = Binder::new("field_y", field_y_id);

    let from = PseudoExpr::BuiltinCall {
        name: BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::BuiltinCall {
                name: BuiltinId::expect_known("List.cons"),
                args: vec![
                    PseudoExpr::var_with_id("field_x", field_x_id),
                    PseudoExpr::BuiltinCall {
                        name: BuiltinId::expect_known("List.cons"),
                        args: vec![
                            PseudoExpr::Lambda {
                                params: vec![field_y_binder.clone()],
                                body: PBox::new(PseudoExpr::var_with_id("field_y", field_y_id)),
                            },
                            PseudoExpr::List {
                                elements: vec![].into(),
                                tail: None,
                            },
                        ]
                        .into(),
                    },
                ]
                .into(),
            },
        ]
        .into(),
    };
    let to = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 2),
        vec![
            PseudoExpr::var_with_id("field_x", field_x_id),
            PseudoExpr::Lambda {
                params: vec![field_y_binder],
                body: PBox::new(PseudoExpr::var_with_id("field_y", field_y_id)),
            },
        ],
    );

    let from_snapshot = snapshot_expr(&from);
    let to_snapshot = snapshot_expr(&to);

    let initial = match &from {
        PseudoExpr::BuiltinCall { args, .. } => match &args[1] {
            PseudoExpr::BuiltinCall {
                args: outer_cons_args,
                ..
            } => match &outer_cons_args[1] {
                PseudoExpr::BuiltinCall {
                    args: inner_cons_args,
                    ..
                } => match &inner_cons_args[0] {
                    PseudoExpr::Lambda { body, .. } => HashMap::from([
                        (
                            from.provenance_node_id_for_path(&[]),
                            vec![MidExprId::new(1)],
                        ),
                        (
                            args[0].provenance_node_id_for_path(&[0]),
                            vec![MidExprId::new(2)],
                        ),
                        (
                            args[1].provenance_node_id_for_path(&[1]),
                            vec![MidExprId::new(3)],
                        ),
                        (
                            outer_cons_args[0].provenance_node_id_for_path(&[1, 0]),
                            vec![MidExprId::new(4)],
                        ),
                        (
                            outer_cons_args[1].provenance_node_id_for_path(&[1, 1]),
                            vec![MidExprId::new(5)],
                        ),
                        (
                            inner_cons_args[0].provenance_node_id_for_path(&[1, 1, 0]),
                            vec![MidExprId::new(6)],
                        ),
                        (
                            body.provenance_node_id_for_path(&[1, 1, 0, 0]),
                            vec![MidExprId::new(7)],
                        ),
                        (
                            inner_cons_args[1].provenance_node_id_for_path(&[1, 1, 1]),
                            vec![MidExprId::new(8)],
                        ),
                    ]),
                    other => panic!("expected lambda field, got {other:?}"),
                },
                other => panic!("expected inner cons spine, got {other:?}"),
            },
            other => panic!("expected outer cons spine, got {other:?}"),
        },
        other => panic!("expected Data.Constr builtin root, got {other:?}"),
    };

    let projected = project_final_pseudo_to_mid(&[from_snapshot, to_snapshot.clone()], &initial);
    let final_union = projected
        .values()
        .flat_map(|mid_ids| mid_ids.iter().copied())
        .collect::<std::collections::BTreeSet<_>>();
    let expected_union = (1..=8)
        .map(MidExprId::new)
        .collect::<std::collections::BTreeSet<_>>();

    assert_eq!(
        final_union, expected_union,
        "normalizing Data.Constr(List.cons(...)) should preserve all removed spine lineage"
    );
    assert!(
        projected.contains_key(&to.provenance_node_id_for_path(&[])),
        "normalized constr root should retain projected lineage"
    );
}

// ===== PARENT CONSISTENCY =====
//
// Five arms, one fixture each, every fixture forcing its arm by SHAPE rather
// than by summary. The anchor pass reads (path, kind) and NO summary, so two
// structurally identical trees anchor everywhere however their contents
// differ — which is why no fixture below moves a node between two positions
// of the same kind. Each puts a different KIND at the path the node moved to,
// denying the anchor and handing the pair to the signature pass, which is the
// route the claim is about.
//
// `parent_consistency_census` reads `matches`, `from` and `to` and nothing
// else, so `propagate_removed_wrapper_lineage`, `emit_containment_lineage`
// and the whole donation half of the projection can be mutated freely without
// moving one of these counts.

/// `let k = <value> { <body> }` over two subtrees, so a leaf can be moved from
/// one sibling subtree to the other with BOTH siblings still matched.
fn let_over(value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::let_bind_with_id("k", VarId::fresh_binding(), value, body)
}

fn delay_of(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Delay(PBox::new(inner))
}

fn force_of(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Force(PBox::new(inner))
}

fn named_var(name: &str) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::fresh_binding())
}

/// The census under test plus the window's match count, so every assertion can
/// also check the five arms PARTITION the matches instead of sampling them.
fn parent_census(from: &PseudoExpr, to: &PseudoExpr) -> (ParentConsistencyCensus, usize) {
    let snapshots = [snapshot_expr(from), snapshot_expr(to)];
    let initial = HashMap::new();
    let (recorder, _, _) = record(&snapshots, &initial);
    let window = &recorder.windows()[0];
    let matched: usize = window.node_matches.iter().sum();
    assert_eq!(
        window.parent.classified(),
        matched,
        "the five arms must partition the window's matches, not sample them"
    );
    (window.parent, matched)
}

/// Two identical trees: every node anchors and every parent link survives.
///
/// The baseline the other four are read against, and the reason the claim is
/// never stated over R1: `pseudo_node_id` is a rolling prefix hash of the path,
/// so equal ids force equal parent paths and an anchor is BY CONSTRUCTION a
/// node that did not move. R1 agreeing here is not evidence about matching.
///
/// MUTATION (this layer): return `Consistent` unconditionally from
/// `parent_consistency_census` -> the tests below fail while this one still
/// passes, so it cannot stand alone.
#[test]
fn identical_trees_leave_every_matched_parent_link_intact() {
    let expr = let_over_delay();

    let (census, matched) = parent_census(&expr, &expr);

    assert_eq!(matched, 4);
    assert_eq!(census.consistent[Route::Anchor.index()], 4);
    assert_eq!(census.unrelated_parent.iter().sum::<usize>(), 0);
    assert_eq!(census.parent_removed.iter().sum::<usize>(), 0);
    assert_eq!(census.within_ancestry.iter().sum::<usize>(), 0);
}

/// (i) BENIGN. `let k = delay(a) { b }` -> `let k = a { b }`: the pass deleted
/// the `delay`, so `a` re-parents onto the `let` because it had no choice —
/// what inlining through a wrapper and flattening a spine both look like from
/// inside the matcher.
///
/// MUTATION (this layer): classify a missing `match_map` entry as
/// `UnrelatedParent` -> the accusation arm swallows every deletion, this fails.
/// MUTATION (wrong layer): `propagate_removed_wrapper_lineage`'s
/// descendant-first `or` chain decides where the deleted `delay`'s mids LAND
/// and cannot move a match, so every count here is unchanged.
#[test]
fn a_child_whose_parent_the_pass_deleted_is_classified_benign() {
    let from = let_over_delay();
    let to = let_over_var();

    let (census, matched) = parent_census(&from, &to);

    assert_eq!(matched, 3);
    // `let` and `b` keep their exact path and kind; only `a` moved.
    assert_eq!(census.consistent[Route::Anchor.index()], 2);
    assert_eq!(census.parent_removed[Route::SigPosition.index()], 1);
    assert_eq!(census.unrelated_parent.iter().sum::<usize>(), 0);
}

/// (ii) BENIGN. `let k = a { b }` -> `let k = delay(a) { b }`: `a`'s new parent
/// is a NEW node sitting under `a`'s old parent, so the node moved along the
/// ancestry it was already on. Read the other way round this is the hoist: a
/// parent chain that grew or shrank while staying the same chain. Legitimate
/// relocations — lambda-edge crossings, else-chain flattenings, cons-spines,
/// curried applies — belong here and in (i), never in the accusation arm.
///
/// MUTATION (this layer): make `related_in_ancestry` return `false`
/// unconditionally -> this becomes an accusation and the test fails.
/// MUTATION (wrong layer): `emit_containment_lineage`'s bottom-up union runs
/// after every window and cannot reach a match.
#[test]
fn a_child_pushed_one_level_down_its_own_ancestry_is_classified_benign() {
    let from = let_over_var();
    let to = let_over_delay();

    let (census, matched) = parent_census(&from, &to);

    assert_eq!(matched, 3);
    assert_eq!(census.consistent[Route::Anchor.index()], 2);
    assert_eq!(census.within_ancestry[Route::SigPosition.index()], 1);
    assert_eq!(census.unrelated_parent.iter().sum::<usize>(), 0);
}

/// (iii) THE CLAIM. Two leaves swap sibling subtrees while both subtrees
/// survive as matched nodes, so each leaf's new parent is neither an ancestor
/// nor a descendant of its old parent's image.
///
/// R2's failure mode in the small: the signature bucket `var|x|0` holds one
/// node on each side, the pass pairs them BY LIST INDEX with no structural
/// check whatever, and the pairing crosses siblings. The `unit` leaf denies
/// the anchor pass — a `var` moving to a position another `var` occupies
/// would anchor on (path, kind) and never reach R2.
///
/// MUTATION (this layer): treat two nodes with a common ancestor as related
/// (every pair in a tree has one) -> everything becomes (ii) and this fails.
/// MUTATION (wrong layer): the `0.55` fuzzy threshold — the signature pass
/// claims these pairs before R3 runs.
#[test]
fn a_leaf_that_swapped_sibling_subtrees_is_the_unrelated_parent_arm() {
    let from = let_over(delay_of(named_var("x")), force_of(PseudoExpr::Unit));
    let to = let_over(delay_of(PseudoExpr::Unit), force_of(named_var("x")));

    let (census, matched) = parent_census(&from, &to);

    // `let`, `delay` and `force` keep path and kind; `x` and the `unit` swap.
    assert_eq!(matched, 5);
    assert_eq!(census.consistent[Route::Anchor.index()], 3);
    assert_eq!(census.unrelated_parent[Route::SigPosition.index()], 2);
    assert_eq!(census.within_ancestry.iter().sum::<usize>(), 0);
    assert_eq!(census.parent_removed.iter().sum::<usize>(), 0);
}

/// A match with a root on exactly one side is counted apart from all four: the
/// (iii) predicate is not defined for it — there is no `parent(l)` to take an
/// image of — and folding it into the accusation would inflate the one number
/// the edit-budget bar reads.
///
/// MUTATION (this layer): fold `RootAsymmetric` into `UnrelatedParent` -> the
/// last assertion fails.
#[test]
fn a_match_with_a_root_on_one_side_only_is_counted_apart() {
    let from = delay_of(named_var("a"));
    let to = let_over(delay_of(named_var("a")), named_var("b"));

    let (census, matched) = parent_census(&from, &to);

    // The `delay` root pairs with the inner `delay`, and `a` with `a`.
    assert_eq!(matched, 2);
    assert_eq!(census.root_asymmetric[Route::SigPosition.index()], 1);
    assert_eq!(census.unrelated_parent.iter().sum::<usize>(), 0);
}

/// The census is computed for a window that transferred NO lineage at all.
///
/// It is read off `matches`, not off the mid transfers: a window that moved no
/// mid still edited the tree, and the edit-budget denominator is a per-window
/// quantity, so a skipped row is not a missing sample, it is a shifted ratio.
///
/// MUTATION (this layer): compute the census inside the `for` loop over
/// `matches` that notes transfers, so it only fires when `prev_owned` has an
/// entry -> the counts go to zero and this fails.
#[test]
fn the_parent_census_is_computed_for_a_window_that_moved_no_mid() {
    let from = let_over(delay_of(named_var("x")), force_of(PseudoExpr::Unit));
    let to = let_over(delay_of(PseudoExpr::Unit), force_of(named_var("x")));
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];

    let (recorder, _, _) = record(&snapshots, &HashMap::new());

    assert_eq!(
        recorder.mids().len(),
        0,
        "this fixture is seeded with nothing, so nothing can have transferred"
    );
    assert_eq!(recorder.windows()[0].mid_transfers.iter().sum::<usize>(), 0);
    assert_eq!(
        recorder.windows()[0].parent.unrelated_parent[Route::SigPosition.index()],
        2
    );
}

/// `structural_edits` is `removed + added` and nothing else, and
/// `anchor_share_of_matches` is 0.0 rather than a division by zero when a
/// window matched nothing.
///
/// Both are read by the edit-budget bar: the first is its denominator and the
/// second selects its stratum, so a window with no match must not be admitted
/// to the low-anchor stratum on the strength of an empty ratio.
///
/// MUTATION (this layer): return `100.0` for the no-match case -> the stratum
/// silently loses every fully-rewritten window.
#[test]
fn the_edit_budget_denominator_and_the_anchor_share_are_what_they_say() {
    let from = let_over_delay();
    let to = let_over_var();
    let snapshots = [snapshot_expr(&from), snapshot_expr(&to)];
    let (recorder, _, _) = record(&snapshots, &HashMap::new());
    let window = &recorder.windows()[0];

    assert_eq!(window.removed, 1);
    assert_eq!(window.added, 0);
    assert_eq!(window.structural_edits(), 1);
    // Two of the three matches anchored.
    assert!((window.anchor_share_of_matches() - 200.0 / 3.0).abs() < 1e-9);

    let empty = WindowRouteCensus {
        window: 0,
        is_bridge: false,
        from_nodes: 0,
        to_nodes: 0,
        node_matches: [0; 6],
        removed: 0,
        added: 0,
        donations: [0; 6],
        mid_transfers: [0; 6],
        parent: ParentConsistencyCensus::default(),
    };
    assert_eq!(empty.anchor_share_of_matches(), 0.0);
}

/// `heuristic` sums R2 AND R3, and nothing else.
///
/// Every headline in the edit-budget report is computed through it — kind
/// (i), (ii), (iii), the root-asymmetric arm and the heuristic-match
/// denominator are all `Parent::heuristic(&...)` — so dropping one of its two
/// terms would move every published figure at once. Nothing else in this file
/// catches that: the other seven fixtures are all claimed by the signature
/// pass, so they read the R2 slot directly and stay green while R3 is
/// silently discarded.
///
/// The live half is why this test is not on literals alone: `delay(x) -> y`
/// is the one window in this file whose single match arrives by R3, so its
/// census row has a populated Fuzzy slot and an empty SigPosition one — the
/// row the other seven fixtures cannot produce. The literal half is a
/// hand-built row with powers of two in the six slots, so ANY wrong slot set
/// — a missing term, an extra one, an off-by-one in `Route::index` —
/// produces a different total rather than a coincidentally equal one.
///
/// MUTATION (this layer): dropping `counts[Route::Fuzzy.index()]` from the
/// sum, and swapping `Route::DonateDescLca` in for it, each fail this test
/// and ONLY this test.
/// MUTATION (wrong layer): the donation half's descendant-first `or` chain,
/// which decides where a REMOVED node's mids land and cannot move a match.
/// Reversing it fails the donate-desc-LCA test alone and leaves all eight
/// parent-consistency tests green.
/// NOT wrong-layer controls: the `0.55` fuzzy floor and the verdict arms of
/// `parent_consistency_census` both reach the live half — the floor is what
/// makes this fixture's one match arrive by R3 at all, and the arms decide
/// which array it lands in. Raising the floor to 0.99 fails this test beside
/// the fuzzy-route test; forcing every verdict to `Consistent` fails it
/// beside the other five. The literal row below survives all of them, which
/// is the half that pins the selector on its own.
#[test]
fn the_headline_selector_sums_both_match_passes_and_no_other_route() {
    let from = delay_of(named_var("x"));
    let to = named_var("y");

    let (census, matched) = parent_census(&from, &to);

    // The pair the fuzzy pass claims is `x <-> y` — same kind, same arity,
    // similar summary — NOT the `delay`, whose kind no longer exists on the
    // right and which is removed and donates instead. `x` has a parent and `y`
    // is the new root, so the arm is `RootAsymmetric`. The arm is not the
    // point; the SLOT is.
    assert_eq!(matched, 1);
    assert_eq!(census.root_asymmetric[Route::Fuzzy.index()], 1);
    assert_eq!(census.root_asymmetric[Route::SigPosition.index()], 0);
    assert_eq!(
        ParentConsistencyCensus::heuristic(&census.root_asymmetric),
        1
    );

    let mut counts = [0usize; 6];
    counts[Route::Anchor.index()] = 1;
    counts[Route::SigPosition.index()] = 2;
    counts[Route::Fuzzy.index()] = 4;
    counts[Route::DonateDescLca.index()] = 8;
    counts[Route::DonateAncestor.index()] = 16;
    counts[Route::DonateToRoot.index()] = 32;
    assert_eq!(ParentConsistencyCensus::heuristic(&counts), 2 + 4);
}
