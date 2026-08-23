use super::*;
use std::rc::Rc;
use uplc::ast::{Constant, DeBruijn};

fn nd(text: &str, index: usize) -> NamedDeBruijn {
    NamedDeBruijn {
        text: text.to_string(),
        index: DeBruijn::new(index),
    }
}

fn sample_term() -> Term<NamedDeBruijn> {
    Term::Apply {
        function: Rc::new(Term::Lambda {
            parameter_name: Rc::new(nd("x", 1)),
            body: Rc::new(Term::Var {
                name: Rc::new(nd("x", 1)),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(1.into())),
            uniq_id: 4,
        }),
        uniq_id: 1,
    }
}

fn deep_delay_chain(depth: usize) -> Term<NamedDeBruijn> {
    let mut term = Term::Var {
        name: Rc::new(nd("leaf", 1)),
        uniq_id: 1,
    };

    for uniq_id in 0..depth {
        term = Term::Delay {
            body: Rc::new(term),
            uniq_id: uniq_id as isize + 2,
        };
    }

    term
}

#[test]
fn test_saturate_uplc_term_spans_fills_sparse_tree_coverage() {
    let term = sample_term();
    let mut source_map = SourceMap::new();
    let span = SourceSpan {
        start_line: 3,
        start_col: 1,
        end_line: 3,
        end_col: 7,
    };

    source_map.register_uplc_span(2, span);
    let inserted = source_map.saturate_uplc_term_spans(&term);

    assert_eq!(inserted, 3, "root, var, and argument should be densified");
    for term_id in [1, 2, 3, 4] {
        assert_eq!(source_map.source_for_uplc(term_id), Some(&span));
    }
}

#[test]
fn test_missing_uplc_term_ids_reports_only_unmapped_original_nodes() {
    let term = sample_term();
    let mut source_map = SourceMap::new();
    let span = SourceSpan {
        start_line: 3,
        start_col: 1,
        end_line: 3,
        end_col: 7,
    };

    source_map.register_uplc_span(2, span);
    assert_eq!(source_map.missing_uplc_term_ids(&term), vec![1, 3, 4]);

    source_map.saturate_uplc_term_spans(&term);
    assert!(source_map.missing_uplc_term_ids(&term).is_empty());
}

#[test]
fn test_source_map_term_graph_handles_deep_delay_chain_iteratively() {
    let term = deep_delay_chain(20_000);
    let mut source_map = SourceMap::new();
    let span = SourceSpan {
        start_line: 7,
        start_col: 1,
        end_line: 7,
        end_col: 9,
    };

    source_map.register_uplc_span(1, span);
    assert_eq!(source_map.missing_uplc_term_ids(&term).len(), 20_000);
    assert_eq!(source_map.saturate_uplc_term_spans(&term), 20_000);
    assert!(source_map.missing_uplc_term_ids(&term).is_empty());
    std::mem::forget(term);
}

fn span(start_line: u32, end_line: u32) -> SourceSpan {
    SourceSpan {
        start_line,
        start_col: 1,
        end_line,
        end_col: 40,
    }
}

/// `Apply(block) -> Lambda(one line) -> Var(block)`: the shape span claiming
/// produces when a mid collapses into a block-scale rendered node and every
/// UPLC term it owns inherits that block's span. The leaf then reports the
/// block's header while its own parent reports one exact line.
fn block_anchored_leaf_term() -> Term<NamedDeBruijn> {
    Term::Apply {
        function: Rc::new(Term::Lambda {
            parameter_name: Rc::new(nd("i", 1)),
            body: Rc::new(Term::Var {
                name: Rc::new(nd("i", 1)),
                uniq_id: 784,
            }),
            uniq_id: 785,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(1.into())),
            uniq_id: 786,
        }),
        uniq_id: 787,
    }
}

#[test]
fn test_narrow_uplc_spans_pulls_a_block_anchored_leaf_onto_its_parents_line() {
    // A deep `Var` whose span is the whole `fn decompiled(...)` block (L1-L150)
    // while its parent lambda holds the one line it renders on (L47). Reporting L1
    // for that Var is the defect.
    let term = block_anchored_leaf_term();
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(787, span(1, 150));
    source_map.register_uplc_span(785, span(47, 47));
    source_map.register_uplc_span(784, span(1, 150));
    source_map.register_uplc_span(786, span(1, 150));

    assert_eq!(
        source_map
            .uplc_span_tree_inversions(&term)
            .iter()
            .filter(|(_, hoistable)| !hoistable)
            .count(),
        1,
        "the leaf Var claims a span wider than its own parent's"
    );

    let narrowed = source_map.narrow_uplc_spans_to_term_tree(&term);

    assert_eq!(narrowed, 1, "only the leaf Var is inverted");
    assert_eq!(
        source_map.source_for_uplc(784),
        Some(&span(47, 47)),
        "the Var must report the line its parent renders on"
    );
    // The block's own term keeps its span: nothing above it disproves it.
    assert_eq!(source_map.source_for_uplc(787), Some(&span(1, 150)));
    // ... and the sibling argument, whose parent really is the block, keeps it.
    assert_eq!(source_map.source_for_uplc(786), Some(&span(1, 150)));

    // `line_to_uplc` has to mirror the move, or a breakpoint on L1 would still
    // arm the Var that no longer reports L1.
    assert!(
        !source_map.uplc_for_line(1).contains(&784),
        "narrowed id must be withdrawn from its previous line"
    );
    assert!(source_map.uplc_for_line(47).contains(&784));
}

#[test]
fn test_narrow_uplc_spans_is_idempotent_and_leaves_no_non_hoisted_inversion() {
    let term = block_anchored_leaf_term();
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(787, span(1, 150));
    source_map.register_uplc_span(785, span(47, 47));
    source_map.register_uplc_span(784, span(1, 150));
    source_map.register_uplc_span(786, span(1, 150));

    source_map.narrow_uplc_spans_to_term_tree(&term);
    assert!(
        source_map
            .uplc_span_tree_inversions(&term)
            .iter()
            .all(|(_, hoistable)| *hoistable),
        "every surviving inversion must be a hoistable definition"
    );
    assert_eq!(
        source_map.narrow_uplc_spans_to_term_tree(&term),
        0,
        "a second pass must find nothing left to narrow"
    );
}

#[test]
fn test_narrow_uplc_spans_exempts_a_hoisted_lambda_definition() {
    // A lambda printed as a top-level `rec fn` spans its whole definition
    // (L93-L120) while the `Apply` that binds it keeps the tight bind-site line
    // (L100) *inside* that definition. The lambda's wider span is the
    // definition it prints as, not an inversion, so it must survive — and its
    // body must be bounded by the definition, not by the bind site.
    let term = Term::Apply {
        function: Rc::new(Term::Lambda {
            parameter_name: Rc::new(nd("y", 1)),
            body: Rc::new(Term::Var {
                name: Rc::new(nd("y", 1)),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(1.into())),
            uniq_id: 4,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(100, 100));
    source_map.register_uplc_span(2, span(93, 120));
    source_map.register_uplc_span(3, span(93, 120));
    source_map.register_uplc_span(4, span(100, 100));

    source_map.narrow_uplc_spans_to_term_tree(&term);

    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(93, 120)),
        "a hoisted lambda keeps the definition span it prints as"
    );
    assert_eq!(
        source_map.source_for_uplc(3),
        Some(&span(93, 120)),
        "its body is bounded by the definition, not pulled to the bind site"
    );
    assert_eq!(
        source_map.uplc_span_tree_inversions(&term),
        vec![(2, true)],
        "the only surviving inversion is the hoisted lambda itself"
    );
}

#[test]
fn test_narrow_uplc_spans_cascades_through_a_tight_intermediate() {
    // block -> tight -> block: the grandchild inherited the same block span, so
    // the tight middle line must cascade onto it.
    let term = Term::Force {
        body: Rc::new(Term::Delay {
            body: Rc::new(Term::Var {
                name: Rc::new(nd("x", 1)),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(10, 60));
    source_map.register_uplc_span(2, span(20, 20));
    source_map.register_uplc_span(3, span(10, 60));

    assert_eq!(source_map.narrow_uplc_spans_to_term_tree(&term), 1);
    assert_eq!(source_map.source_for_uplc(3), Some(&span(20, 20)));
}

#[test]
fn test_narrow_uplc_spans_never_relocates_a_term_outside_its_own_span() {
    // The hoisting confound: the parent renders in a wholly different region.
    // Narrowing must not move the child there — its new span is always a subset
    // of the span it already claimed, or it is left alone.
    let term = Term::Force {
        body: Rc::new(Term::Var {
            name: Rc::new(nd("x", 1)),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(5, 5));
    source_map.register_uplc_span(2, span(200, 260));

    assert_eq!(source_map.narrow_uplc_spans_to_term_tree(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(200, 260)));
    assert!(source_map.uplc_for_line(200).contains(&2));
}

#[test]
fn test_narrow_uplc_spans_tightens_columns_within_one_line() {
    // Containment is a (line, column) relation: a same-line parent with tighter
    // columns still refines the child's span, and the reported line is unchanged.
    let term = Term::Force {
        body: Rc::new(Term::Var {
            name: Rc::new(nd("x", 1)),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let tight = SourceSpan {
        start_line: 12,
        start_col: 9,
        end_line: 12,
        end_col: 20,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, tight);
    source_map.register_uplc_span(2, span(12, 12));

    assert_eq!(source_map.narrow_uplc_spans_to_term_tree(&term), 1);
    assert_eq!(source_map.source_for_uplc(2), Some(&tight));
    assert!(source_map.uplc_for_line(12).contains(&2));
}

#[test]
fn test_narrow_uplc_spans_carries_the_bound_across_unmapped_terms() {
    // A term with no span of its own must not break the chain: the bound has to
    // keep travelling so an inversion further down is still caught.
    let term = Term::Force {
        body: Rc::new(Term::Delay {
            body: Rc::new(Term::Var {
                name: Rc::new(nd("x", 1)),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(30, 30));
    source_map.register_uplc_span(3, span(10, 90));

    assert_eq!(source_map.narrow_uplc_spans_to_term_tree(&term), 1);
    assert_eq!(source_map.source_for_uplc(3), Some(&span(30, 30)));
    assert!(source_map.source_for_uplc(2).is_none());
}

#[test]
fn test_narrow_uplc_spans_stops_at_an_unmapped_hoisted_lambda() {
    // The hoist exemption must not depend on the lambda carrying a span of its
    // own: exact lineage may be sparse, so an unmapped lambda can have a body
    // mapped to the definition region it prints as. If the bound travelled
    // past it, the body would narrow onto the call site — the caller's line.
    let term = Term::Apply {
        function: Rc::new(Term::Lambda {
            parameter_name: Rc::new(nd("y", 1)),
            body: Rc::new(Term::Var {
                name: Rc::new(nd("y", 1)),
                uniq_id: 3,
            }),
            // deliberately left unmapped below
            uniq_id: 2,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(1.into())),
            uniq_id: 4,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(100, 100)); // the call site
    source_map.register_uplc_span(3, span(93, 120)); // the hoisted definition
    source_map.register_uplc_span(4, span(100, 100));

    assert_eq!(
        source_map.narrow_uplc_spans_to_term_tree(&term),
        0,
        "nothing may be narrowed across a hoisted definition boundary"
    );
    assert_eq!(
        source_map.source_for_uplc(3),
        Some(&span(93, 120)),
        "the body keeps the definition span; the call site is not evidence about it"
    );
    assert!(
        source_map.uplc_span_tree_inversions(&term).is_empty(),
        "the measurement must draw the same boundary as the pass, or it would \
         report an inversion the pass deliberately refuses to narrow"
    );
}

#[test]
fn test_narrow_uplc_spans_still_crosses_an_unmapped_non_definition() {
    // The negative control for the test above: a plain unmapped wrapper is NOT
    // a hoist boundary, so the bound must still travel through it. Without this
    // pairing, clearing the bound at every unmapped term would look correct.
    let term = Term::Force {
        body: Rc::new(Term::Force {
            body: Rc::new(Term::Var {
                name: Rc::new(nd("x", 1)),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(30, 30));
    source_map.register_uplc_span(3, span(10, 90));

    assert_eq!(source_map.narrow_uplc_spans_to_term_tree(&term), 1);
    assert_eq!(source_map.source_for_uplc(3), Some(&span(30, 30)));
}

/// `Force(block) -> Force(block) -> Apply(block) -> {Var(one line), Var(block)}`:
/// every structural term inherited the `rec fn` header span, and one leaf inside
/// the block claims the line the block's code actually renders on.
fn sandwiched_structural_term() -> Term<NamedDeBruijn> {
    Term::Force {
        body: Rc::new(Term::Force {
            body: Rc::new(Term::Apply {
                function: Rc::new(Term::Var {
                    name: Rc::new(nd("head", 1)),
                    uniq_id: 4,
                }),
                argument: Rc::new(Term::Var {
                    name: Rc::new(nd("y", 2)),
                    uniq_id: 5,
                }),
                uniq_id: 3,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    }
}

#[test]
fn test_subtree_hull_pulls_a_sandwiched_structural_term_onto_its_own_content() {
    // A `Force` reporting L248 `rec fn i(y_30) {` whose parent reports the
    // identical L248-L279 — so the term cannot be the block's head — while its
    // own subtree renders at L254. The upward pass is structurally unable to
    // see this: there is no tighter ancestor to narrow toward.
    let term = sandwiched_structural_term();
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(248, 279));
    source_map.register_uplc_span(2, span(248, 279));
    source_map.register_uplc_span(3, span(248, 279));
    source_map.register_uplc_span(4, span(254, 254));
    source_map.register_uplc_span(5, span(248, 279));

    assert_eq!(
        source_map.narrow_uplc_spans_to_term_tree(&term),
        0,
        "the defect: no ancestor is tighter, so upward narrowing cannot move \
         a term whose parent holds the same block span"
    );

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 2);
    assert_eq!(
        source_map.source_for_uplc(3),
        Some(&span(254, 254)),
        "the Apply must report the line its own content renders on"
    );
    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(254, 254)),
        "bottom-up: the tightened child is evidence for its parent too"
    );
    assert_eq!(
        source_map.source_for_uplc(1),
        Some(&span(248, 279)),
        "the outermost term has no parent holding its span, so it is left alone"
    );

    // `line_to_uplc` must mirror the move, or a breakpoint on the header would
    // still arm terms that no longer report it.
    assert!(!source_map.uplc_for_line(248).contains(&3));
    assert!(source_map.uplc_for_line(254).contains(&3));
}

#[test]
fn test_subtree_hull_leaves_a_term_that_heads_its_own_block() {
    // The class a fix must NOT move: no parent occupies the span, so the term
    // may legitimately BE the construct the header opens (the `Apply` that is a
    // `let`'s whole value). Its descendants sitting on interior lines is exactly
    // what a correct block head looks like, so that signal cannot convict it.
    let term = Term::Force {
        body: Rc::new(Term::Apply {
            function: Rc::new(Term::Var {
                name: Rc::new(nd("f", 1)),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Var {
                name: Rc::new(nd("x", 2)),
                uniq_id: 4,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(190, 204));
    source_map.register_uplc_span(2, span(193, 202));
    source_map.register_uplc_span(3, span(195, 195));
    source_map.register_uplc_span(4, span(193, 202));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(193, 202)));
}

#[test]
fn test_subtree_hull_never_relocates_a_term_outside_its_own_span() {
    // One child renders at a hoisted definition site (L249-L256) wholly outside
    // the term's own span. Only descendants strictly INSIDE the span may bound
    // it, so the replacement is always a subset of what the term claimed and no
    // term is relocated across the file.
    let term = Term::Force {
        body: Rc::new(Term::Apply {
            function: Rc::new(Term::Delay {
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("k", 1)),
                    uniq_id: 4,
                }),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Var {
                name: Rc::new(nd("w", 2)),
                uniq_id: 5,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(7, 80));
    source_map.register_uplc_span(2, span(7, 80));
    source_map.register_uplc_span(3, span(249, 256));
    source_map.register_uplc_span(4, span(249, 256));
    source_map.register_uplc_span(5, span(9, 9));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 1);
    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(9, 9)),
        "only the descendant inside the block may supply the bound"
    );
    assert_eq!(
        source_map.source_for_uplc(3),
        Some(&span(249, 256)),
        "the hoisted-out descendant is untouched and never drags its ancestor out"
    );
}

#[test]
fn test_subtree_hull_skips_hoisted_definition_interiors() {
    // `Apply(Lambda, value)` is this pipeline's `let`. The lambda is the
    // continuation, printed as a relocatable definition, so neither its header
    // nor its body says where the `let` renders — the bound value does.
    let term = Term::Force {
        body: Rc::new(Term::Apply {
            function: Rc::new(Term::Lambda {
                parameter_name: Rc::new(nd("f1", 1)),
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("f1", 1)),
                    uniq_id: 4,
                }),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Constant {
                value: Rc::new(Constant::Integer(1.into())),
                uniq_id: 5,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(141, 279));
    source_map.register_uplc_span(2, span(141, 279));
    source_map.register_uplc_span(3, span(150, 160));
    source_map.register_uplc_span(4, span(151, 151));
    source_map.register_uplc_span(5, span(269, 269));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 1);
    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(269, 269)),
        "the bound value is the let's surface; the definition it binds is not"
    );
}

#[test]
fn test_subtree_hull_leaves_surface_bearing_terms_on_the_header() {
    // A `Case` IS the `when` it heads and a `Constr` its constructor call, so a
    // block header really can be their line. Only terms that print nothing may
    // be pulled down, or the pass moves a term off its own surface.
    let term = Term::Case {
        constr: Rc::new(Term::Var {
            name: Rc::new(nd("subject", 1)),
            uniq_id: 2,
        }),
        branches: vec![Term::Var {
            name: Rc::new(nd("arm", 2)),
            uniq_id: 3,
        }],
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    // The Case's parent would hold the identical span; model that by giving the
    // Case itself a parent-shaped wrapper.
    let wrapped = Term::Force {
        body: Rc::new(term),
        uniq_id: 4,
    };
    source_map.register_uplc_span(4, span(71, 82));
    source_map.register_uplc_span(1, span(71, 82));
    source_map.register_uplc_span(2, span(73, 73));
    source_map.register_uplc_span(3, span(71, 82));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&wrapped), 0);
    assert_eq!(source_map.source_for_uplc(1), Some(&span(71, 82)));
}

#[test]
fn test_subtree_hull_spans_every_descendant_that_bounds_it() {
    // Two tight descendants on different lines: the replacement is their hull,
    // not whichever one happens to be visited first.
    let term = Term::Force {
        body: Rc::new(Term::Apply {
            function: Rc::new(Term::Var {
                name: Rc::new(nd("f", 1)),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Var {
                name: Rc::new(nd("x", 2)),
                uniq_id: 4,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(10, 60));
    source_map.register_uplc_span(2, span(10, 60));
    source_map.register_uplc_span(3, span(20, 20));
    source_map.register_uplc_span(4, span(40, 40));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 1);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(20, 40)));
}

#[test]
fn test_span_pass_sequence_reaches_a_fixed_point_with_no_non_hoisted_inversion() {
    // The order the pipeline runs: narrow up, pull down, narrow up again. The
    // second upward pass is not optional — pulling a parent down leaves its
    // children holding the wider block span, an inversion it must not leave.
    let term = sandwiched_structural_term();
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(248, 279));
    source_map.register_uplc_span(2, span(248, 279));
    source_map.register_uplc_span(3, span(248, 279));
    source_map.register_uplc_span(4, span(254, 254));
    source_map.register_uplc_span(5, span(248, 279));

    source_map.narrow_uplc_spans_to_term_tree(&term);
    source_map.narrow_uplc_spans_to_subtree_hull(&term);
    assert!(
        source_map
            .uplc_span_tree_inversions(&term)
            .iter()
            .any(|(_, hoistable)| !hoistable),
        "pulling a parent down does create an inversion below it"
    );

    let repaired = source_map.narrow_uplc_spans_to_term_tree(&term);
    assert!(repaired > 0);
    assert!(
        source_map
            .uplc_span_tree_inversions(&term)
            .iter()
            .all(|(_, hoistable)| *hoistable),
        "after the second upward pass every surviving inversion is a hoisted \
         definition"
    );

    let snapshot = |map: &SourceMap| {
        let mut entries: Vec<(isize, SourceSpan)> =
            map.uplc_to_source.iter().map(|(k, v)| (*k, *v)).collect();
        entries.sort_by_key(|(id, _)| *id);
        entries
    };
    let before = snapshot(&source_map);
    source_map.narrow_uplc_spans_to_term_tree(&term);
    source_map.narrow_uplc_spans_to_subtree_hull(&term);
    source_map.narrow_uplc_spans_to_term_tree(&term);
    assert_eq!(
        before,
        snapshot(&source_map),
        "the sequence must be at a fixed point"
    );
}

#[test]
fn test_subtree_hull_handles_a_deep_chain_iteratively() {
    // Same reason every other walk here is iterative: the pipeline produces term
    // trees thousands deep, and a recursive flatten would blow the stack.
    let term = deep_delay_chain(20_000);
    let mut source_map = SourceMap::new();
    for uniq_id in 1..=20_001isize {
        source_map.register_uplc_span(uniq_id, span(1, 400));
    }
    source_map.register_uplc_span(1, span(37, 37));

    assert!(source_map.narrow_uplc_spans_to_subtree_hull(&term) > 0);
    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(37, 37)),
        "the leaf's tight span bounds the whole chain above it"
    );
    std::mem::forget(term);
}

/// `Force -> Force -> <inner> -> {Var(tight), Var(block)}`, where `<inner>` is
/// either a `Case` (the `when` the block header opens) or an `Apply` (which
/// prints nothing). Same spans in both shapes, so the only difference the
/// assertions can be reading is the kind of the descendant riding the anchor.
fn block_anchor_with_inner(inner: Term<NamedDeBruijn>) -> Term<NamedDeBruijn> {
    Term::Force {
        body: Rc::new(Term::Force {
            body: Rc::new(inner),
            uniq_id: 2,
        }),
        uniq_id: 1,
    }
}

fn tight_and_block_operands() -> (Term<NamedDeBruijn>, Term<NamedDeBruijn>) {
    (
        Term::Var {
            name: Rc::new(nd("subject", 1)),
            uniq_id: 4,
        },
        Term::Var {
            name: Rc::new(nd("arm", 2)),
            uniq_id: 5,
        },
    )
}

fn block_anchor_spans() -> SourceMap {
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(71, 82));
    source_map.register_uplc_span(2, span(71, 82));
    source_map.register_uplc_span(3, span(71, 82));
    source_map.register_uplc_span(4, span(73, 73));
    source_map.register_uplc_span(5, span(71, 82));
    source_map
}

#[test]
fn test_subtree_hull_is_vetoed_by_a_when_that_still_holds_the_block() {
    // The regression this veto exists to prevent. The `Case` on uplc 3 may
    // genuinely BE the `when` whose header opens L71: unlike the structural
    // terms above it, it owns a token. Pulling uplc 2 down to L73 would leave
    // the `Case` wider than its own parent, and the second upward narrow would
    // then drag it off L71 — the line its own surface is on.
    let (subject, arm) = tight_and_block_operands();
    let term = block_anchor_with_inner(Term::Case {
        constr: Rc::new(subject),
        branches: vec![arm],
        uniq_id: 3,
    });
    let mut source_map = block_anchor_spans();

    assert_eq!(
        source_map.uplc_terms_pullable_to_subtree_hull(&term),
        Vec::new(),
        "a `when` still holding the block span must veto the pull-down"
    );
    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(71, 82)));
}

#[test]
fn test_subtree_hull_is_not_vetoed_by_surface_free_plumbing() {
    // The negative control for the test above: identical spans and shape, the
    // only change being that the term riding the anchor prints nothing. With
    // no surface on L71 to protect the pull-down must happen, or the veto
    // would be a blanket "never move" that forfeits the whole pass.
    let (subject, arm) = tight_and_block_operands();
    let term = block_anchor_with_inner(Term::Apply {
        function: Rc::new(subject),
        argument: Rc::new(arm),
        uniq_id: 3,
    });
    let mut source_map = block_anchor_spans();

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 2);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(73, 73)));
    assert_eq!(source_map.source_for_uplc(3), Some(&span(73, 73)));
}

#[test]
fn test_subtree_hull_post_condition_is_empty_after_the_pass() {
    // The pass and its post-condition are the same code, so this asserts the
    // pass ran to completion, not its rule: nothing pullable is left behind.
    let term = sandwiched_structural_term();
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(248, 279));
    source_map.register_uplc_span(2, span(248, 279));
    source_map.register_uplc_span(3, span(248, 279));
    source_map.register_uplc_span(4, span(254, 254));
    source_map.register_uplc_span(5, span(248, 279));

    assert!(
        !source_map
            .uplc_terms_pullable_to_subtree_hull(&term)
            .is_empty()
    );
    source_map.narrow_uplc_spans_to_subtree_hull(&term);
    assert_eq!(
        source_map.uplc_terms_pullable_to_subtree_hull(&term),
        Vec::new()
    );
}

#[test]
fn test_subtree_hull_counts_an_inline_lambda_argument_as_its_own_surface() {
    // A `Lambda` in ARGUMENT position is printed in place — `list.any(xs,
    // fn(x) { .. })` — so its lines are part of the surface the call covers.
    // Discarding it as a "definition", right only for the hoisted and
    // continuation cases, makes the hull stop short of the closure the call
    // passes, so the term reports a position that skips its own argument.
    //
    // Contrast test_subtree_hull_skips_hoisted_definition_interiors, where the
    // lambda is the FUNCTION child — a `let` continuation — and must not count.
    // Kind alone cannot tell the two apart; position can.
    let term = Term::Force {
        body: Rc::new(Term::Apply {
            function: Rc::new(Term::Var {
                name: Rc::new(nd("any", 1)),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("x", 1)),
                    uniq_id: 5,
                }),
                uniq_id: 4,
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_uplc_span(1, span(20, 30));
    source_map.register_uplc_span(2, span(20, 30)); // parent holds the same span
    source_map.register_uplc_span(3, span(20, 20)); // the callee
    source_map.register_uplc_span(4, span(22, 26)); // the inline closure
    source_map.register_uplc_span(5, span(23, 23));

    assert_eq!(source_map.narrow_uplc_spans_to_subtree_hull(&term), 1);
    assert_eq!(
        source_map.source_for_uplc(2),
        Some(&span(20, 26)),
        "the hull must cover the inline closure the call passes, not stop at the callee"
    );
}

/// `Apply(outer) -> Apply(inner) -> Var`, where both applies hold the identical
/// block-scale span. The inner one is the abstain channel's target shape: a
/// term with no surface of its own, reporting a header its own parent already
/// occupies.
fn nested_apply_sharing_a_block_span() -> Term<NamedDeBruijn> {
    Term::Apply {
        function: Rc::new(Term::Apply {
            function: Rc::new(Term::Var {
                name: Rc::new(nd("f", 1)),
                uniq_id: 3,
            }),
            argument: Rc::new(Term::Constant {
                value: Rc::new(Constant::Integer(1.into())),
                uniq_id: 4,
            }),
            uniq_id: 2,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(2.into())),
            uniq_id: 5,
        }),
        uniq_id: 1,
    }
}

/// Baseline: all four conditions hold, so the inner `Apply` is withdrawn from
/// BOTH span maps, and its parent — which is what keeps the withdrawal free —
/// still holds the span it gave up.
#[test]
fn abstain_withdraws_a_heirless_apply_duplicating_its_parents_block_span() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));
    source_map.register_uplc_span(3, span(12, 12));

    assert_eq!(source_map.apply_abstain_channel(&term), 1);
    assert_eq!(source_map.source_for_uplc(2), None, "span withdrawn");
    assert!(
        !source_map.uplc_for_line(10).contains(&2),
        "`line_to_uplc` must be withdrawn from too, or a breakpoint still finds the term \
         the stepper can no longer position"
    );
    assert_eq!(
        source_map.source_for_uplc(1),
        Some(&span(10, 40)),
        "the parent must still hold the span — that is what makes the withdrawal free"
    );
    assert!(source_map.abstained_uplc_ids().contains(&2));
}

/// Condition (a). The mid has an heir, so the position was OBSERVED on a
/// surviving node rather than donated to it. Nothing may be withdrawn.
#[test]
fn abstain_keeps_a_position_whose_mid_still_has_an_heir() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    // heirless_mids deliberately left empty.
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));

    assert_eq!(source_map.apply_abstain_channel(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 40)));
}

/// Condition (a) with two writers, heirless FIRST. One of the term's mids has
/// an heir, so the position was observed on a surviving node and the term keeps
/// it. Write order must not matter — the companion test covers the reverse.
#[test]
fn abstain_keeps_a_term_whose_earlier_writer_has_an_heir() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map.register_mid(MidExprId::new(9), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map
        .mid_to_source
        .insert(MidExprId::new(9), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));

    assert_eq!(
        source_map.mid_order,
        vec![MidExprId::new(7), MidExprId::new(9)],
        "mid_9 must be the LAST writer for this test to mean anything"
    );
    assert_eq!(source_map.apply_abstain_channel(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 40)));
}

/// Condition (a) with two writers, heirless LAST.
///
/// The term is stamped by a mid that HAS an heir, so it earned this position on
/// a surviving node; a heirless mid then writes the SAME span. Nothing about
/// that second write unearns the first, so the decision keys on ALL matched
/// writers being heirless, never on whichever sorts last in `mid_order`.
#[test]
fn abstain_keeps_a_term_whose_later_writer_is_heirless_but_an_earlier_one_is_not() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]); // has an heir
    source_map.register_mid(MidExprId::new(9), &[2]); // heirless, writes LAST
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map
        .mid_to_source
        .insert(MidExprId::new(9), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(9));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));

    assert_eq!(
        source_map.mid_order,
        vec![MidExprId::new(7), MidExprId::new(9)],
        "mid_9 must be the LAST writer for this test to mean anything"
    );
    assert_eq!(
        source_map.apply_abstain_channel(&term),
        0,
        "a term with any heirful writer earned its span and must keep it"
    );
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 40)));
}

/// An abstained id may never be handed a span again, by any writer.
///
/// The saturation write-back skips abstained ids, but that is one site: the
/// guard lives in `register_uplc_span` itself, so no later pass or second
/// finalization can resurrect a position the term declined and leave
/// `abstained_uplc_ids` disagreeing with both span maps.
#[test]
fn abstain_refuses_every_later_re_registration() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));
    assert_eq!(source_map.apply_abstain_channel(&term), 1);
    assert_eq!(source_map.source_for_uplc(2), None);

    // Direct re-registration, the shape a later pass would take.
    source_map.register_uplc_span(2, span(12, 12));
    assert_eq!(source_map.source_for_uplc(2), None, "still withdrawn");
    assert!(!source_map.uplc_for_line(12).contains(&2));

    // And through `set_mid_span`, the shape a second finalization would take.
    source_map.set_mid_span(MidExprId::new(7), span(14, 14));
    assert_eq!(source_map.source_for_uplc(2), None, "still withdrawn");
    assert!(!source_map.uplc_for_line(14).contains(&2));
}

/// Condition (b). The parent holds a DIFFERENT span, so this term is the
/// topmost member of its identical-span chain. Withdrawing it would take a
/// line's last covering evidence with it — the induction that makes the channel
/// free depends on exactly this case being refused.
#[test]
fn abstain_keeps_the_top_of_an_identical_span_chain() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(1, 80)); // parent span differs
    source_map.register_uplc_span(2, span(10, 40));

    assert_eq!(source_map.apply_abstain_channel(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 40)));
}

/// Condition (d). A short span is not a block header, and withdrawing it would
/// remove an honest small position.
#[test]
fn abstain_keeps_a_span_too_short_to_be_a_block_header() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 12));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 12));
    source_map.register_uplc_span(2, span(10, 12));

    assert_eq!(source_map.apply_abstain_channel(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 12)));
}

/// Condition (c). A `Case` meets every other condition and is still kept: it
/// prints a `when` header, so the position may be its own surface rather than
/// an inherited one. `narrow_uplc_spans_to_subtree_hull` vetoes the same kinds
/// for the same reason.
#[test]
fn abstain_keeps_a_case_because_a_when_header_can_be_its_own_line() {
    let term = Term::Apply {
        function: Rc::new(Term::Case {
            constr: Rc::new(Term::Var {
                name: Rc::new(nd("s", 1)),
                uniq_id: 3,
            }),
            branches: vec![Term::Var {
                name: Rc::new(nd("b", 1)),
                uniq_id: 4,
            }],
            uniq_id: 2,
        }),
        argument: Rc::new(Term::Constant {
            value: Rc::new(Constant::Integer(1.into())),
            uniq_id: 5,
        }),
        uniq_id: 1,
    };
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));

    assert_eq!(source_map.apply_abstain_channel(&term), 0);
    assert_eq!(source_map.source_for_uplc(2), Some(&span(10, 40)));
}

/// An abstention must survive saturation. Saturation refills unmapped ids from
/// a graph neighbour, and an abstained id is unmapped ON PURPOSE — refilling it
/// would replace one unfounded line with a differently unfounded one.
///
/// The exclusion has to sit in the write-back, not the seed loop or the BFS:
/// spans must still FLOW THROUGH an abstained term to genuinely unmapped terms
/// beyond it. Here uplc#4 is unmapped for no reason and must still be filled.
#[test]
fn saturation_refills_past_an_abstained_term_but_never_the_term_itself() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(10, 40));
    source_map.register_uplc_span(2, span(10, 40));
    source_map.register_uplc_span(3, span(12, 12));
    // uplc#4 and #5 are left unmapped; #4 is only reachable through #2.

    assert_eq!(source_map.apply_abstain_channel(&term), 1);
    source_map.saturate_uplc_term_spans(&term);

    assert_eq!(
        source_map.source_for_uplc(2),
        None,
        "saturation must not hand a position back to a term that declined one"
    );
    assert!(
        source_map.source_for_uplc(4).is_some(),
        "a span must still flow THROUGH the abstained term to terms beyond it — \
         an abstention is a decision, not a cut in the graph"
    );
}

/// A position the term COMPUTED is not a position it was given.
///
/// `resolve_spans_for_stepping` runs the subtree-hull pass before the abstain
/// channel, so a structural term can hold a span no mid ever wrote — derived
/// from its own descendants rather than donated by a deleted node's lineage.
/// Its historical writers are heirless, so adjudicating on them would withdraw
/// a position that was computed; the channel only ever withdraws a span some
/// mid actually wrote.
#[test]
fn abstain_keeps_a_span_no_mid_wrote() {
    let term = nested_apply_sharing_a_block_span();
    let mut source_map = SourceMap::new();
    source_map.register_mid(MidExprId::new(7), &[2]);
    source_map
        .mid_to_source
        .insert(MidExprId::new(7), span(10, 40));
    source_map.heirless_mids.insert(MidExprId::new(7));
    source_map.register_uplc_span(1, span(20, 35));
    // The term holds a DIFFERENT span from the one its heirless mid wrote —
    // the shape the hull pass leaves behind. Its parent still matches it, so
    // conditions (b), (c) and (d) all hold and only the writer test can refuse.
    source_map.register_uplc_span(2, span(20, 35));

    assert_eq!(
        source_map.apply_abstain_channel(&term),
        0,
        "no mid wrote this span, so it cannot be a donation to withdraw"
    );
    assert_eq!(source_map.source_for_uplc(2), Some(&span(20, 35)));
}
