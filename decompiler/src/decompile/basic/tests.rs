use super::constructor_index;

/// The rule is the machine's rule, on every tag, not just the tags that
/// happen to occur.
///
/// What `unConstrData` hands a running script is `uplc::machine::runtime`'s
/// `convert_tag_to_constr(tag).unwrap_or_else(|| any_constructor.unwrap())`.
/// Naming a constructor other than the one the script itself branches on
/// would be a wrong answer, so the two are asserted EQUAL over the whole
/// `u64` tag space rather than over the part the decoder accepts today: an
/// unreachable disagreement is still one waiting for the decoder to widen.
///
/// The one deliberate difference is total-vs-panicking — the machine
/// `unwrap()`s a missing `any_constructor` on an escape tag, where
/// `constructor_index` returns `0` — so those rows are skipped.
#[test]
fn the_index_is_the_one_the_machine_reads() {
    use uplc::machine::runtime::convert_tag_to_constr;

    let mut escapes = 0usize;
    let mut tagged = 0usize;
    for tag in tags_worth_asking() {
        for any in [
            None,
            Some(0u64),
            Some(7),
            Some(102),
            Some(128),
            Some(u64::MAX),
        ] {
            let machine = match convert_tag_to_constr(tag) {
                Some(ix) => {
                    tagged += 1;
                    ix
                }
                // Where the machine would `unwrap()`; see above.
                None => match any {
                    Some(ix) => {
                        escapes += 1;
                        ix
                    }
                    None => continue,
                },
            };
            // Built from a real `Data::constr` so `fields` is what the
            // encoder makes; only `tag` and `any_constructor` are varied.
            let mut node = match uplc::ast::Data::constr(0, Vec::new()) {
                uplc::PlutusData::Constr(c) => c,
                other => panic!("not a constructor: {other:?}"),
            };
            node.tag = tag;
            node.any_constructor = any;
            assert_eq!(
                constructor_index(&node),
                machine as usize,
                "tag {tag}, any_constructor {any:?}"
            );
        }
    }
    // Guards against a vacuous pass: both arms must actually be exercised.
    assert!(tagged >= 128 * 5, "only {tagged} tag-carried rows");
    assert!(escapes >= 5, "only {escapes} escape rows");
}

/// Every tag the rule distinguishes, both sides of each boundary, and the
/// ends of the space: the two closed ranges in full, the rest sampled.
fn tags_worth_asking() -> Vec<u64> {
    let mut tags: Vec<u64> = (118..=131).collect();
    tags.extend(1276..=1405);
    tags.extend([
        0,
        1,
        101,
        102,
        103,
        120,
        1279,
        1401,
        65535,
        1 << 32,
        u64::MAX - 1,
        u64::MAX,
    ]);
    tags.sort_unstable();
    tags.dedup();
    tags
}
