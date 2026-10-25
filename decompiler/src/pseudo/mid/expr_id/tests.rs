use super::*;

#[test]
fn test_provenance_builder() {
    let mut pb = ProvenanceBuilder::new();
    let id1 = pb.fresh_id();
    let id2 = pb.fresh_id();
    assert_ne!(id1, id2);

    pb.link(id1, 42);
    pb.link(id1, 43);
    pb.link(id2, 100);

    assert_eq!(pb.uplc_ids(id1), &[42, 43]);
    assert_eq!(pb.uplc_ids(id2), &[100]);
    assert_eq!(pb.mid_for_uplc(42), Some(id1));
    assert_eq!(pb.mid_for_uplc(100), Some(id2));
    assert_eq!(pb.mid_for_uplc(999), None);
}

/// The provenance a derived node had when derivation copied its source's
/// ids eagerly: the reference [`ProvenanceBuilder`]'s snapshots must match.
#[derive(Default)]
struct EagerProvenance {
    parts: std::collections::HashMap<u32, Vec<EagerPart>>,
}

#[derive(Clone, Copy)]
enum EagerPart {
    Linked(isize),
    Absorbed(isize),
    Node(u32),
}

impl EagerProvenance {
    fn uplc_ids(&self, root: u32) -> Vec<isize> {
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut visited = std::collections::HashSet::from([root]);
        let mut stack = vec![(root, 0usize, true)];
        while let Some((node, index, is_root)) = stack.pop() {
            let Some(&part) = self.parts.get(&node).and_then(|parts| parts.get(index)) else {
                continue;
            };
            stack.push((node, index + 1, is_root));
            match part {
                EagerPart::Linked(id) => {
                    if is_root {
                        seen.insert(id);
                        out.push(id);
                    } else if seen.insert(id) {
                        out.push(id);
                    }
                }
                EagerPart::Absorbed(id) => {
                    if seen.insert(id) {
                        out.push(id);
                    }
                }
                EagerPart::Node(source) => {
                    if visited.insert(source) {
                        stack.push((source, 0, false));
                    }
                }
            }
        }
        out
    }

    fn derive(&mut self, mid: u32, sources: &[u32]) {
        let mut seen = std::collections::HashSet::new();
        let mut parts = Vec::new();
        for &source in sources {
            for id in self.uplc_ids(source) {
                if seen.insert(id) {
                    parts.push(EagerPart::Linked(id));
                }
            }
        }
        self.parts.insert(mid, parts);
    }
}

/// Random interleavings of every mutation, checked against eager copying
/// after each step, for every node. Absorption cycles are allowed: the
/// invariant forbids them, but materialization must terminate regardless and
/// then still agree.
#[test]
fn derived_provenance_matches_eager_copies() {
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move |bound: usize| -> usize {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((state >> 33) as usize) % bound
    };

    for _ in 0..40 {
        let mut lazy = ProvenanceBuilder::new();
        let mut eager = EagerProvenance::default();
        let mut ids: Vec<MidExprId> = Vec::new();
        for step in 0..120 {
            let op = if ids.len() < 2 { 0 } else { next(7) };
            match op {
                0 => ids.push(lazy.fresh_id()),
                6 => {
                    // An id made up by hand, which a later `fresh_id` hands
                    // out again: the derivation then replaces its parts.
                    let ahead = MidExprId::new(lazy.node_count() + next(3) as u32);
                    let uplc = next(24) as isize;
                    lazy.link(ahead, uplc);
                    eager
                        .parts
                        .entry(ahead.as_u32())
                        .or_default()
                        .push(EagerPart::Linked(uplc));
                    if !ids.contains(&ahead) {
                        ids.push(ahead);
                    }
                }
                1 | 2 => {
                    let mid = ids[next(ids.len())];
                    let uplc = next(24) as isize;
                    if op == 1 {
                        lazy.link(mid, uplc);
                        eager
                            .parts
                            .entry(mid.as_u32())
                            .or_default()
                            .push(EagerPart::Linked(uplc));
                    } else {
                        lazy.absorb_uplc(mid, uplc);
                        eager
                            .parts
                            .entry(mid.as_u32())
                            .or_default()
                            .push(EagerPart::Absorbed(uplc));
                    }
                }
                3 => {
                    let (target, source) = (ids[next(ids.len())], ids[next(ids.len())]);
                    if target != source {
                        lazy.absorb_mid(target, source);
                        eager
                            .parts
                            .entry(target.as_u32())
                            .or_default()
                            .push(EagerPart::Node(source.as_u32()));
                    }
                }
                4 => {
                    let source = ids[next(ids.len())];
                    let mid = lazy.fresh_derived_from(source);
                    eager.derive(mid.as_u32(), &[source.as_u32()]);
                    ids.push(mid);
                }
                _ => {
                    let sources: Vec<MidExprId> =
                        (0..1 + next(3)).map(|_| ids[next(ids.len())]).collect();
                    let mid = lazy.fresh_derived_from_many(&sources);
                    let raw: Vec<u32> = sources.iter().map(|id| id.as_u32()).collect();
                    eager.derive(mid.as_u32(), &raw);
                    ids.push(mid);
                }
            }
            for &id in &ids {
                assert_eq!(
                    lazy.uplc_ids(id),
                    eager.uplc_ids(id.as_u32()),
                    "node {id} after step {step}"
                );
            }
        }
    }
}
