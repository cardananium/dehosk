use std::collections::HashSet;

use super::PipelinePassId;

#[test]
fn pipeline_pass_labels_are_unique() {
    let mut labels = HashSet::new();
    for pass in PipelinePassId::ALL {
        assert!(
            labels.insert(pass.label()),
            "duplicate pipeline pass label: {}",
            pass.label()
        );
    }
}
