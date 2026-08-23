//! Typed identifier for field-access selectors.
//!
//! The enum on `PseudoExpr::FieldAccess` makes the closed-set
//! selectors (`fst`, `snd`, `head`) explicit; `NamedField` is the
//! escape hatch for any selector the decompiler carries by name
//! (`tag`, `fields`, blueprint-sourced record fields).
//!
//! No dependencies on the rest of the AST, so tests and helpers
//! can reuse it without pulling in the large `pseudo::ast` graph.

use serde::{Deserialize, Serialize};

/// Typed selector for a `FieldAccess` node.
///
/// `PairFst`/`PairSnd`/`ListHead` are the built-in structural
/// accessors; `ContextField` is reserved for a typed Cardano
/// `ScriptContext` schema and no construction path populates it;
/// everything else is a `NamedField`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum FieldSelector {
    /// `fst` — Pair first component. Maps to `BuiltinId::FstPair` at
    /// the UPLC level.
    PairFst,
    /// `snd` — Pair second component. Maps to `BuiltinId::SndPair` at
    /// the UPLC level.
    PairSnd,
    /// `head` — List head. Maps to `BuiltinId::HeadList` at the UPLC
    /// level.
    ListHead,
    /// A Cardano `ScriptContext` field identifier. Carries the
    /// display-name string; reserved for callers that have already
    /// resolved a typed context identifier.
    ContextField(String),
    /// Any other named selector — record fields, Constr-internal
    /// `tag`/`fields`, blueprint-sourced names, etc.
    NamedField(String),
}

impl FieldSelector {
    /// Build a selector from the name a `FieldAccess` renders.
    ///
    /// Never produces `ContextField` — that variant is reserved for
    /// callers that have already resolved a typed context identifier.
    pub(crate) fn from_display_name(name: &str) -> Self {
        match name {
            "fst" => Self::PairFst,
            "snd" => Self::PairSnd,
            "head" => Self::ListHead,
            other => Self::NamedField(other.to_string()),
        }
    }

    /// Pretty-printable name. Round-trips with [`from_display_name`]
    /// for the three built-in selectors and for `NamedField`;
    /// `ContextField` returns its carried name verbatim, so it does
    /// not round-trip.
    pub(crate) fn as_pretty_name(&self) -> &str {
        match self {
            Self::PairFst => "fst",
            Self::PairSnd => "snd",
            Self::ListHead => "head",
            Self::ContextField(name) | Self::NamedField(name) => name.as_str(),
        }
    }

    /// The accessor as it must render in surface syntax. the surface has no
    /// `.fst`/`.snd`, so a `Pair`'s elements use the 1-based ordinals
    /// `.1st`/`.2nd`, the same as tuples; everything else renders as its
    /// [`as_pretty_name`]. Kept distinct so the internal `"fst"`/`"snd"`
    /// recognizers and the `from_display_name` round-trip stay intact.
    pub(crate) fn as_surface_accessor(&self) -> &str {
        match self {
            Self::PairFst => "1st",
            Self::PairSnd => "2nd",
            _ => self.as_pretty_name(),
        }
    }

    /// `true` when this selector is one of the built-in structural
    /// accessors (`fst`, `snd`, `head`).
    pub(crate) fn is_structural(&self) -> bool {
        matches!(self, Self::PairFst | Self::PairSnd | Self::ListHead)
    }

    /// `true` when this selector targets the first component of a pair.
    pub(crate) fn is_pair_fst(&self) -> bool {
        matches!(self, Self::PairFst)
    }

    /// `true` when this selector targets the second component of a pair.
    pub(crate) fn is_pair_snd(&self) -> bool {
        matches!(self, Self::PairSnd)
    }

    /// `true` when this selector targets the head of a list.
    pub(crate) fn is_list_head(&self) -> bool {
        matches!(self, Self::ListHead)
    }
}

#[cfg(test)]
mod tests;
