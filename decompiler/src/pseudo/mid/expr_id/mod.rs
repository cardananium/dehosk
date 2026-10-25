//! Identifiers and provenance tracking for MidExpr nodes.

use serde::{Deserialize, Serialize};

use super::expr::MidExpr;

/// Unique identifier for a MidExpr node, assigned during UPLC → MidExpr translation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct MidExprId(u32);

impl MidExprId {
    pub(crate) fn new(raw: u32) -> Self {
        Self(raw)
    }

    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for MidExprId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "mid_{}", self.0)
    }
}

/// Source location in decompiled output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SourceSpan {
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// One entry in a node's provenance, in the order it was recorded.
///
/// `Node` and `Snapshot` are references to another node's parts, not copies
/// of its ids. Copying would be quadratic: absorbing a chain recopies the
/// whole list at every step, and chain length is script-controlled.
#[derive(Debug, Clone, Copy)]
enum Part {
    /// A UPLC id from [`ProvenanceBuilder::link`]. On the node that recorded
    /// it, kept even if the id appears again later.
    Linked(isize),
    /// A UPLC id from [`ProvenanceBuilder::absorb_uplc`]. Dropped at
    /// materialization if already present.
    Absorbed(isize),
    /// The parts of another node.
    Node(MidExprId),
    /// The ids `source` owned at generation `at`, from
    /// [`ProvenanceBuilder::fresh_derived_from`]. Parts are only ever
    /// appended (replacing them only marks the old ones dropped), each
    /// stamped with its generation, so what `source` and everything it
    /// reaches held at `at` stays recoverable: a derivation costs one entry
    /// instead of a copy of the source's ids.
    Snapshot { source: MidExprId, at: u64 },
}

/// A [`Part`] as recorded on its node.
#[derive(Debug, Clone, Copy)]
struct Recorded {
    part: Part,
    /// The generation that recorded it.
    added: u64,
    /// The generation that replaced the node's parts, `u64::MAX` while it
    /// stands — see [`ProvenanceBuilder::link_derived`].
    dropped: u64,
}

/// Tracks provenance links between all representation levels.
pub(crate) struct ProvenanceBuilder {
    /// MidExprId → what contributed to this node, in order (so ascending in
    /// `added` along the list).
    parts: std::collections::HashMap<MidExprId, Vec<Recorded>>,
    /// Whether [`Self::link_derived`] ever replaced a node's parts. A walk
    /// under a looser cut-off can then see fewer of them, so
    /// [`Self::uplc_ids`] stops reasoning across cut-offs.
    replaced: bool,
    /// UPLC uniq_id → the MidExprId that recorded it. May name a node that
    /// has since been absorbed; [`Self::mid_for_uplc`] resolves that.
    uplc_to_mid: std::collections::HashMap<isize, MidExprId>,
    /// source → the node that absorbed it. [`Self::mid_for_uplc`] follows
    /// these hops instead of rewriting every UPLC id the source owned.
    absorbed_into: std::collections::HashMap<MidExprId, MidExprId>,
    /// Counter for allocating MidExprIds.
    next_id: u32,
    /// Bumped on every mutation, so a cached materialization can tell whether
    /// it is still current.
    generation: u64,
    /// Memo for [`Self::uplc_ids`], valid only for its recorded generation.
    materialized: std::cell::RefCell<std::collections::HashMap<MidExprId, (u64, Vec<isize>)>>,
}

impl ProvenanceBuilder {
    pub(crate) fn new() -> Self {
        Self {
            parts: std::collections::HashMap::new(),
            replaced: false,
            uplc_to_mid: std::collections::HashMap::new(),
            absorbed_into: std::collections::HashMap::new(),
            next_id: 0,
            generation: 0,
            materialized: std::cell::RefCell::new(std::collections::HashMap::new()),
        }
    }

    pub(crate) fn fresh_id(&mut self) -> MidExprId {
        let id = MidExprId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Record that `mid_id` was produced from `uplc_uniq_id` and owns
    /// it in the canonical `uplc -> mid` lookup.
    pub(crate) fn link(&mut self, mid_id: MidExprId, uplc_uniq_id: isize) {
        self.push_part(mid_id, Part::Linked(uplc_uniq_id));
        self.uplc_to_mid.insert(uplc_uniq_id, mid_id);
    }

    /// Append `part` to `mid_id`'s provenance, stamped with a new generation.
    fn push_part(&mut self, mid_id: MidExprId, part: Part) {
        self.generation += 1;
        let added = self.generation;
        self.parts.entry(mid_id).or_default().push(Recorded {
            part,
            added,
            dropped: u64::MAX,
        });
    }

    /// Record provenance for a synthesized node without changing the canonical
    /// uplc -> mid lookup used for original translation nodes: the ids each of
    /// `sources` owns now, in order, each id once.
    ///
    /// A snapshot by design: the derived node inherits the ids its sources
    /// had at this moment, and later changes to them do not reach it.
    ///
    /// The node's own earlier parts, if any, are replaced. Only an id made up
    /// by hand rather than by [`Self::fresh_id`] can already have some; they
    /// stay recorded, marked dropped, for the snapshots taken while they held.
    fn link_derived(&mut self, mid_id: MidExprId, sources: &[MidExprId]) {
        let at = self.generation;
        self.generation += 1;
        let added = self.generation;
        let parts = self.parts.entry(mid_id).or_default();
        for recorded in parts.iter_mut() {
            if recorded.dropped == u64::MAX {
                recorded.dropped = added;
                self.replaced = true;
            }
        }
        parts.extend(sources.iter().map(|&source| Recorded {
            part: Part::Snapshot { source, at },
            added,
            dropped: u64::MAX,
        }));
    }

    /// Attach an additional original UPLC node to an already-retained MidExpr.
    ///
    /// Translation collapses several UPLC nodes into one owner — flattened
    /// lambda chains, apply spines — so the canonical `uplc -> mid` lookup
    /// must point at the surviving MidExpr, not a dead intermediate id.
    pub(crate) fn absorb_uplc(&mut self, mid_id: MidExprId, uplc_uniq_id: isize) {
        self.push_part(mid_id, Part::Absorbed(uplc_uniq_id));
        self.uplc_to_mid.insert(uplc_uniq_id, mid_id);
    }

    /// Attach all original UPLC nodes currently owned by `source_mid` to the
    /// surviving retained owner `mid_id`.
    ///
    /// O(1): the source is referenced, not copied.
    pub(crate) fn absorb_mid(&mut self, mid_id: MidExprId, source_mid: MidExprId) {
        if mid_id == source_mid {
            return;
        }
        self.push_part(mid_id, Part::Node(source_mid));
        self.absorbed_into.entry(source_mid).or_insert(mid_id);
    }

    /// Allocate a fresh MidExprId that inherits provenance from `source_mid`.
    pub(crate) fn fresh_derived_from(&mut self, source_mid: MidExprId) -> MidExprId {
        self.fresh_derived_from_many(&[source_mid])
    }

    /// Allocate a fresh MidExprId that inherits provenance from several
    /// contributing MidExpr nodes.
    pub(crate) fn fresh_derived_from_many(&mut self, source_mids: &[MidExprId]) -> MidExprId {
        let mid_id = self.fresh_id();
        self.link_derived(mid_id, source_mids);
        mid_id
    }

    /// The UPLC ids this node owns, in the order they were recorded.
    ///
    /// Materialized from the parts on demand. The reference graph is as deep
    /// as the eliminations that built it, so the walk is a heap stack. An id
    /// recorded by `link` on this node is kept even if it also appears later;
    /// everything reached through absorption or derivation is dropped if
    /// already present.
    ///
    /// A `Snapshot` part stands for the ids its source owned when the
    /// snapshot was taken, so it is expanded by walking the source with every
    /// part recorded after that cut-off left out, down to the nodes the
    /// source reaches. A node met again is walked again only when that can
    /// add something here: not if a finished walk of it ran under a cut-off
    /// at least as loose, or left out nothing the new cut-off takes in, and
    /// not if a walk of it under the same cut-off is still in progress (a
    /// cycle). That keeps a chain of derivations linear rather than
    /// re-walking it once per link.
    pub(crate) fn uplc_ids(&self, mid_id: MidExprId) -> Vec<isize> {
        if let Some((generation, ids)) = self.materialized.borrow().get(&mid_id)
            && *generation == self.generation
        {
            return ids.clone();
        }

        /// A node being walked.
        struct Frame {
            node: MidExprId,
            /// Index of the next part to look at.
            index: usize,
            /// Parts recorded after this generation are left out.
            cutoff: u64,
            /// Whether this is the node asked for.
            is_root: bool,
            /// Reached through a `Snapshot`, whose cut-off is its own: what
            /// this walk leaves out says nothing about the node holding it.
            via_snapshot: bool,
            /// The earliest generation among the parts this walk, or the
            /// walks it reached through `Node` parts, left out.
            left_out: u64,
            /// Whether this walk, or one it reached, passed over a node still
            /// being walked (a cycle): the ids that node has yet to give are
            /// then missing here, so the walk vouches for nothing.
            partial: bool,
        }

        /// What the walks of one node so far have covered.
        #[derive(Default)]
        struct Walks {
            /// The loosest finished walk that is not `partial`: its cut-off
            /// and its `left_out`.
            finished: Option<(u64, u64)>,
            /// The cut-off of every finished walk that is not `partial`,
            /// for when parts have been replaced.
            finished_cutoffs: Vec<u64>,
            /// Cut-offs of the walks still in progress, outermost first. A
            /// node is only re-entered under a tighter cut-off, so these
            /// strictly decrease.
            active: Vec<u64>,
        }

        let mut out: Vec<isize> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut walks: std::collections::HashMap<MidExprId, Walks> =
            std::collections::HashMap::new();
        walks.entry(mid_id).or_default().active.push(u64::MAX);
        let mut stack = vec![Frame {
            node: mid_id,
            index: 0,
            cutoff: u64::MAX,
            is_root: true,
            via_snapshot: false,
            left_out: u64::MAX,
            partial: false,
        }];

        while let Some(mut frame) = stack.pop() {
            let next = self
                .parts
                .get(&frame.node)
                .and_then(|parts| parts.get(frame.index));
            let part = match next {
                Some(recorded) if recorded.added <= frame.cutoff => {
                    if recorded.dropped != u64::MAX && recorded.dropped <= frame.cutoff {
                        // Already replaced at this cut-off.
                        frame.index += 1;
                        stack.push(frame);
                        continue;
                    }
                    recorded.part
                }
                _ => {
                    // The walk is over: past the last part, or at the first
                    // one recorded after the cut-off (as is everything after
                    // it on this node).
                    let left_out = match next {
                        Some(recorded) => frame.left_out.min(recorded.added),
                        None => frame.left_out,
                    };
                    let node_walks = walks.entry(frame.node).or_default();
                    node_walks.active.pop();
                    if !frame.partial {
                        node_walks.finished_cutoffs.push(frame.cutoff);
                    }
                    if !frame.partial
                        && node_walks
                            .finished
                            .is_none_or(|(cutoff, _)| cutoff <= frame.cutoff)
                    {
                        node_walks.finished = Some((frame.cutoff, left_out));
                    }
                    if let Some(holder) = stack.last_mut() {
                        holder.partial |= frame.partial;
                        if !frame.via_snapshot {
                            holder.left_out = holder.left_out.min(left_out);
                        }
                    }
                    continue;
                }
            };
            frame.index += 1;
            let (source, cutoff, via_snapshot) = match part {
                Part::Linked(id) => {
                    // A `link` on this node is kept even if the id appears
                    // again later; through an absorption it is dropped if
                    // already present.
                    if frame.is_root {
                        seen.insert(id);
                        out.push(id);
                    } else if seen.insert(id) {
                        out.push(id);
                    }
                    stack.push(frame);
                    continue;
                }
                Part::Absorbed(id) => {
                    if seen.insert(id) {
                        out.push(id);
                    }
                    stack.push(frame);
                    continue;
                }
                Part::Node(source) => (source, frame.cutoff, false),
                Part::Snapshot { source, at } => (source, at.min(frame.cutoff), true),
            };
            let source_walks = walks.entry(source).or_default();
            // Whether the source has nothing to add under `cutoff`, and if so
            // the earliest generation it would leave out: exact when a walk
            // under this cut-off finished, or left out nothing up to it;
            // otherwise the earliest that could be.
            let covered = if source_walks.active.last() == Some(&cutoff) {
                frame.partial = true;
                Some(cutoff.saturating_add(1))
            } else if self.replaced {
                // A looser cut-off may no longer see a replaced part: only a
                // finished walk under this very cut-off covers this one.
                source_walks
                    .finished_cutoffs
                    .contains(&cutoff)
                    .then(|| cutoff.saturating_add(1))
            } else {
                match source_walks.finished {
                    Some((walked, left_out)) if walked <= cutoff && left_out > cutoff => {
                        Some(left_out)
                    }
                    Some((walked, left_out)) if walked == cutoff => Some(left_out),
                    Some((walked, _)) if walked > cutoff => Some(cutoff.saturating_add(1)),
                    _ => None,
                }
            };
            match covered {
                Some(source_left_out) => {
                    if !via_snapshot {
                        frame.left_out = frame.left_out.min(source_left_out);
                    }
                    stack.push(frame);
                }
                None => {
                    source_walks.active.push(cutoff);
                    stack.push(frame);
                    stack.push(Frame {
                        node: source,
                        index: 0,
                        cutoff,
                        is_root: false,
                        via_snapshot,
                        left_out: u64::MAX,
                        partial: false,
                    });
                }
            }
        }

        self.materialized
            .borrow_mut()
            .insert(mid_id, (self.generation, out.clone()));
        out
    }

    pub(crate) fn mid_for_uplc(&self, uplc_id: isize) -> Option<MidExprId> {
        let mut mid = *self.uplc_to_mid.get(&uplc_id)?;
        // Follow absorptions to the surviving owner. Bounded by the number of
        // nodes, so a cycle cannot spin forever.
        for _ in 0..=self.next_id {
            match self.absorbed_into.get(&mid) {
                Some(&next) if next != mid => mid = next,
                _ => break,
            }
        }
        Some(mid)
    }

    pub(crate) fn node_count(&self) -> u32 {
        self.next_id
    }
}

/// Reassign fresh unique MidExprIds to the entire tree, preserving provenance
/// by deriving each new id from the previous node id.
pub(crate) fn refresh_mid_ids(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = crate::pseudo::mid::rewrite::rewrite_bottom_up(taken, &mut |mut node| {
        let refreshed = provenance.fresh_derived_from(node.id());
        node.set_id(refreshed);
        node
    });
}

impl Default for ProvenanceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
