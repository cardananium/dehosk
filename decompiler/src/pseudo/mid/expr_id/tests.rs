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
