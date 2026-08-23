//! Typed identity for constructors.
//!
//! `KnownConstructor` is a closed set: the twelve standard ADT constructors
//! (`True`, `False`, `Some`, `None`, `Ok`, `Error`, `Pair`, `Nil`, `Cons`,
//! `Less`, `Equal`, `Greater`), the six Cardano script-purpose constructors
//! (`Mint` … `Propose`), and the nullary `Void` marker aliasing the Plutus
//! unit constructor. `ConstructorShape` adds an `Unknown { tag, arity }`
//! escape hatch for user-defined ADTs known only by structure.
//!
//! This module is the typed-identity primitive — it depends on nothing else
//! in the AST.

/// Closed set of constructors the decompiler recognizes by name.
///
/// Each variant has a canonical Plutus tag and arity, intrinsic to its ABI
/// shape and exposed via [`expected_tag`] and [`expected_arity`] so
/// callers can validate decoded `Constr` data.
///
/// [`expected_tag`]: KnownConstructor::expected_tag
/// [`expected_arity`]: KnownConstructor::expected_arity
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum KnownConstructor {
    /// `False : Bool` — Plutus `Constr 0 []`.
    False,
    /// `True : Bool` — Plutus `Constr 1 []`.
    True,
    /// `None : Option<a>` — Plutus `Constr 1 []` (`Some=0, None=1`).
    /// The reversed Plinth/PlutusTx encoding (`None=0, Some=1`) is handled
    /// via `ConstructorShape::Unknown` and the `adt_disambiguation` pass.
    None,
    /// `Some(a) : Option<a>` — Plutus `Constr 0 [a]`.
    Some,
    /// `Ok(a) : Result<a, b>` — Plutus `Constr 0 [a]`.
    Ok,
    /// `Error(b) : Result<a, b>` — Plutus `Constr 1 [b]`.
    Error,
    /// `Pair(a, b)` — Plutus `Constr 0 [a, b]`.
    Pair,
    /// `Nil : List<a>` — Plutus `Constr 0 []` (`[]` at tag 0).
    /// The reversed Plinth/PlutusTx encoding (`Nil = Constr 1 []`) is still
    /// handled via `ConstructorShape::Unknown`.
    Nil,
    /// `Cons(head, tail) : List<a>` — Plutus `Constr 1 [head, tail]`
    /// (`[]` at 0, cons at 1; the reversed encoding uses `Unknown`).
    Cons,
    /// `Less : Ordering` — Plutus `Constr 0 []`.
    Less,
    /// `Equal : Ordering` — Plutus `Constr 1 []`.
    Equal,
    /// `Greater : Ordering` — Plutus `Constr 2 []`.
    Greater,
    /// `Mint(policy_id) : ScriptPurpose/ScriptInfo` — Plutus `Constr 0 [_]`.
    ///
    /// The short recognizer name `"Mint"` matches the alias used by
    /// `cardano/patterns.rs::identify_purpose`. The longer rendered form
    /// (`"Minting"`) is sourced at display time from
    /// [`crate::decompile::blueprint_registry::BlueprintHintRegistry`], keyed
    /// by [`SumTypeId::Purpose`] / [`SumTypeId::ScriptInfo`].
    ///
    /// [`SumTypeId::Purpose`]: crate::decompile::simplify::postprocess::SumTypeId::Purpose
    /// [`SumTypeId::ScriptInfo`]: crate::decompile::simplify::postprocess::SumTypeId::ScriptInfo
    Mint,
    /// `Spend(output_ref) : ScriptPurpose` (V1/V2) — Plutus `Constr 1 [_]`.
    /// V3 `ScriptInfo::Spending` carries an extra datum field; the V3
    /// arity-2 shape falls into [`ConstructorShape::Unknown`] rather than
    /// rebinding `Spend` to two variants.
    Spend,
    /// `Withdraw(stake_credential) : ScriptPurpose/ScriptInfo` —
    /// Plutus `Constr 2 [_]`.
    Withdraw,
    /// `Publish(certificate) : ScriptPurpose` (V1/V2 `Certifying`) —
    /// Plutus `Constr 3 [_]`. V3 `ScriptInfo::Certifying` carries an
    /// extra index field; that arity-2 shape falls into
    /// [`ConstructorShape::Unknown`].
    Publish,
    /// `Vote(voter) : ScriptInfo` (V3) — Plutus `Constr 4 [_]`.
    Vote,
    /// `Propose(action) : ScriptInfo` (V3) — Plutus `Constr 5 [_, _]`.
    /// Arity 2 because the V3 governance action carries a proposal id
    /// alongside the action body.
    Propose,
    /// `Void : Void` — Plutus `Constr 0 []`, rendered as `Void`; the alias
    /// `Unit` is also accepted. Nullary and structurally identical to
    /// `False`/`Nil`/`Less`, so like the Cardano-purpose variants it is
    /// name-anchored and excluded from [`candidates_by_tag_arity`].
    ///
    /// [`candidates_by_tag_arity`]: KnownConstructor::candidates_by_tag_arity
    Void,
}

impl KnownConstructor {
    /// Parse a constructor name string, ignoring tag/arity.
    ///
    /// Returns `None` for any name outside the closed set. Use
    /// [`from_str_and_tag`] to also reject a name whose tag disagrees.
    ///
    /// [`from_str_and_tag`]: KnownConstructor::from_str_and_tag
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        match name {
            "False" => Some(Self::False),
            "True" => Some(Self::True),
            "None" => Some(Self::None),
            "Some" => Some(Self::Some),
            "Ok" => Some(Self::Ok),
            "Error" => Some(Self::Error),
            "Pair" => Some(Self::Pair),
            "Nil" => Some(Self::Nil),
            "Cons" => Some(Self::Cons),
            "Less" => Some(Self::Less),
            "Equal" => Some(Self::Equal),
            "Greater" => Some(Self::Greater),
            "Mint" => Some(Self::Mint),
            "Spend" => Some(Self::Spend),
            "Withdraw" => Some(Self::Withdraw),
            "Publish" => Some(Self::Publish),
            "Vote" => Some(Self::Vote),
            "Propose" => Some(Self::Propose),
            "Void" | "Unit" => Some(Self::Void),
            _ => None,
        }
    }

    /// Parse a constructor name string and validate its Plutus tag.
    ///
    /// Returns `None` when the name is unknown or its tag differs from the
    /// constructor's canonical [`expected_tag`]. Most call sites should
    /// use this recognizer: a name and tag that disagree indicate corrupt
    /// or hand-built `Constr` data.
    ///
    /// [`expected_tag`]: KnownConstructor::expected_tag
    pub(crate) fn from_str_and_tag(name: &str, tag: usize) -> Option<Self> {
        let kc = Self::from_name(name)?;
        (kc.expected_tag() == tag).then_some(kc)
    }

    /// Canonical pretty-printable name. Round-trips with [`from_name`].
    ///
    /// [`from_name`]: KnownConstructor::from_name
    pub(crate) fn pretty_name(self) -> &'static str {
        match self {
            Self::False => "False",
            Self::True => "True",
            Self::None => "None",
            Self::Some => "Some",
            Self::Ok => "Ok",
            Self::Error => "Error",
            Self::Pair => "Pair",
            Self::Nil => "Nil",
            Self::Cons => "Cons",
            Self::Less => "Less",
            Self::Equal => "Equal",
            Self::Greater => "Greater",
            Self::Mint => "Mint",
            Self::Spend => "Spend",
            Self::Withdraw => "Withdraw",
            Self::Publish => "Publish",
            Self::Vote => "Vote",
            Self::Propose => "Propose",
            Self::Void => "Void",
        }
    }

    /// Canonical Plutus `Constr` tag for this constructor.
    ///
    /// The Cardano-purpose variants ([`Self::Mint`] … [`Self::Propose`]) use
    /// the V1/V2 `ScriptPurpose` tag layout, extended with V3 `ScriptInfo`'s
    /// `Voting`/`Proposing` at tags 4 and 5.
    pub(crate) fn expected_tag(self) -> usize {
        match self {
            Self::False
            | Self::Some
            | Self::Ok
            | Self::Pair
            | Self::Nil
            | Self::Less
            | Self::Mint
            | Self::Void => 0,
            Self::True | Self::None | Self::Error | Self::Cons | Self::Equal | Self::Spend => 1,
            Self::Greater | Self::Withdraw => 2,
            Self::Publish => 3,
            Self::Vote => 4,
            Self::Propose => 5,
        }
    }

    /// Number of fields this constructor carries.
    ///
    /// Each Cardano-purpose variant uses its V1/V2 `ScriptPurpose` arity
    /// (the V3 `ScriptInfo` shapes for `Spending`/`Certifying` carry an
    /// extra field; those arity-2 layouts fall through to
    /// [`ConstructorShape::Unknown`] rather than overloading the variants).
    pub(crate) fn expected_arity(self) -> usize {
        match self {
            Self::False
            | Self::True
            | Self::None
            | Self::Nil
            | Self::Less
            | Self::Equal
            | Self::Greater
            | Self::Void => 0,
            Self::Some
            | Self::Ok
            | Self::Error
            | Self::Mint
            | Self::Spend
            | Self::Withdraw
            | Self::Publish
            | Self::Vote => 1,
            Self::Pair | Self::Cons | Self::Propose => 2,
        }
    }

    /// All `KnownConstructor`s that share the given Plutus ABI shape.
    ///
    /// Returns an empty slice when no standard constructor matches the
    /// `(tag, arity)` pair, leaving the caller free to treat the shape as
    /// a user-defined ADT. Slices are ordered deterministically so callers
    /// can pattern-match on them directly.
    ///
    /// **Note**: the Cardano-purpose variants (`Mint`/`Spend`/…/`Propose`)
    /// and [`Self::Void`] are name-anchored rather than structurally
    /// disambiguatable, and are deliberately absent: listing them would
    /// widen `(0, 1)` from `[Some, Ok]` to `[Some, Ok, Mint]` and `(0, 0)`
    /// from `[False, Nil, Less]` to `[False, Nil, Less, Void]`, silently
    /// breaking the exact-slice patterns matched against this table.
    pub(crate) fn candidates_by_tag_arity(tag: usize, arity: usize) -> &'static [Self] {
        match (tag, arity) {
            (0, 0) => &[Self::False, Self::Nil, Self::Less],
            (0, 1) => &[Self::Some, Self::Ok],
            (0, 2) => &[Self::Pair],
            (1, 0) => &[Self::True, Self::None, Self::Equal],
            (1, 1) => &[Self::Error],
            (1, 2) => &[Self::Cons],
            (2, 0) => &[Self::Greater],
            _ => &[],
        }
    }

    /// Disambiguate a two-branch case pattern where both branches belong
    /// to the same standard two-constructor ADT.
    ///
    /// Arguments are `(tag, arity)` tuples for branches `a` and `b` in
    /// their original order; the result maps back to that order. Returns
    /// `None` unless the pair is `Bool` (`(0,0)`/`(1,0)`), `Option`
    /// (`(0,1)`/`(1,0)` — `Some` at tag 0, `None` at tag 1) or `Result`
    /// (`(0,1)`/`(1,1)`).
    ///
    /// The `Bool` entry is TAG-keyed: valid only when the tags are REAL
    /// data constructor tags. Scott-case tags are branch POSITIONS
    /// (`try_recognize_scott_encoding` enumerates continuations), and a
    /// church bool has True at position 0 — the opposite of the data
    /// table — so the Scott 2x0 caller bypasses this entry and labels
    /// only via `bool_orientation` witnesses. The Option/Result entries
    /// are SHAPE-keyed (the payload arm is Some/Ok by arity, not by tag)
    /// and stay safe for any encoding.
    pub(crate) fn recognize_two_branch_adt(
        a: (usize, usize),
        b: (usize, usize),
    ) -> Option<(Self, Self)> {
        let mut sorted = [a, b];
        sorted.sort();
        let (kc_low, kc_high) = match (sorted[0], sorted[1]) {
            ((0, 0), (1, 0)) => (Self::False, Self::True),
            ((0, 1), (1, 0)) => (Self::Some, Self::None),
            ((0, 1), (1, 1)) => (Self::Ok, Self::Error),
            _ => return None,
        };
        if a == sorted[0] {
            Some((kc_low, kc_high))
        } else {
            Some((kc_high, kc_low))
        }
    }

    /// Disambiguate a three-branch case pattern whose branches belong to a
    /// standard three-constructor ADT.
    ///
    /// Arguments are `(tag, arity)` tuples for branches `a`, `b`, `c` in
    /// their original order; the result maps back to that order. The only
    /// shape matched is `Ordering` (`(0,0)`/`(1,0)`/`(2,0)` →
    /// `Less`/`Equal`/`Greater`); anything else returns `None`.
    pub(crate) fn recognize_three_branch_adt(
        a: (usize, usize),
        b: (usize, usize),
        c: (usize, usize),
    ) -> Option<(Self, Self, Self)> {
        let mut sorted = [a, b, c];
        sorted.sort();
        let mapping: &[(Self, (usize, usize))] = match (sorted[0], sorted[1], sorted[2]) {
            ((0, 0), (1, 0), (2, 0)) => &[
                (Self::Less, (0, 0)),
                (Self::Equal, (1, 0)),
                (Self::Greater, (2, 0)),
            ],
            _ => return None,
        };
        let lookup = |input: (usize, usize)| {
            mapping
                .iter()
                .find(|(_, key)| *key == input)
                .map(|(kc, _)| *kc)
        };
        Some((lookup(a)?, lookup(b)?, lookup(c)?))
    }
}

/// Provenance of an `Unknown` constructor's `tag` — where the tag came from,
/// which decides whether the CIP data-Bool convention (False=0/True=1) may be
/// applied to it.
///
/// - `DataTag`: a genuine **data constructor index** (from a `Data` `Constr`
///   node or a declaration-ordered ADT). The CIP Bool table is reliable here.
/// - `ScottPositional`: a **continuation / parameter POSITION** recovered from
///   a Scott/church encoding (`\h0 h1. h_i …`). The data-Bool table is NOT
///   reliable — for a church Bool, position 0 selects the FIRST continuation
///   (church TRUE), the opposite of the data convention. Without a
///   `bool_orientation` witness, consumers must treat such a tag as honest
///   positional, never assume `tag0 = False`. (For a declaration-ordered Scott
///   DATA type position still equals the data tag — this is provenance, not a
///   blanket polarity claim.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConstructorOrigin {
    /// Tag is a data constructor index — CIP Bool table reliable.
    DataTag,
    /// Tag is a Scott/church continuation position — Bool table unreliable
    /// without a `bool_orientation` witness.
    ScottPositional,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConstructorShape {
    /// One of the closed-set `KnownConstructor`s.
    Known(KnownConstructor),
    /// User-defined ADT — only structurally identified.
    Unknown {
        tag: usize,
        arity: usize,
        /// Provenance of `tag` (see [`ConstructorOrigin`]). `DataTag` at every
        /// construction site except the Scott-encoding recognizers, which mint
        /// `ScottPositional` via [`ConstructorShape::scott_positional`].
        origin: ConstructorOrigin,
        /// Per-bool church-bool convention: `Some(t)` means `Constr<t>` is
        /// `church_true` for THIS bool, so the when→if collapse swap and
        /// `is_true`/`is_false` read the convention PER-BOOL, not from the
        /// program-scoped flag. `None` = unwitnessed → fall back to that
        /// flag; that is the default at every construction site except the
        /// data-tag church-bool seed (`bool_orientation::orient_datatag`).
        /// Carried verbatim through the nameless round-trip and `with_*`
        /// rebuilds.
        church_true: Option<usize>,
    },
}

impl ConstructorShape {
    /// Build a shape from a (possibly unknown) name plus structural tag/arity.
    ///
    /// The shape is `Known(_)` only when name, tag and arity all agree with a
    /// closed-set constructor's canonical values. Any disagreement falls back
    /// to `unknown_data(tag, arity)`, so the structural info survives a source
    /// name that is absent or wrong.
    pub(crate) fn from_name_and_tag(name: Option<&str>, tag: usize, arity: usize) -> Self {
        if let Some(name) = name
            && let Some(kc) = KnownConstructor::from_str_and_tag(name, tag)
            && kc.expected_arity() == arity
        {
            return Self::Known(kc);
        }
        Self::unknown_data(tag, arity)
    }

    /// Build an `Unknown` shape whose tag is a genuine **data constructor
    /// index** (the common case — a `Data` `Constr` or a declaration-ordered
    /// ADT). The CIP Bool table is reliable for `DataTag` origin.
    pub(crate) fn unknown_data(tag: usize, arity: usize) -> Self {
        Self::Unknown {
            tag,
            arity,
            origin: ConstructorOrigin::DataTag,
            church_true: None,
        }
    }

    /// Build an `Unknown` shape whose tag is a **Scott/church continuation
    /// position** (minted only by the Scott-encoding recognizers). The CIP
    /// Bool table must NOT be applied to a `ScottPositional` tag without a
    /// `bool_orientation` witness — see [`ConstructorOrigin`].
    pub(crate) fn scott_positional(tag: usize, arity: usize) -> Self {
        Self::Unknown {
            tag,
            arity,
            origin: ConstructorOrigin::ScottPositional,
            church_true: None,
        }
    }

    /// This shape's per-bool `church_true` tag witness, if any.
    /// `Known` constructors and unwitnessed `Unknown` shapes return `None`.
    pub(crate) fn church_true(&self) -> Option<usize> {
        match self {
            Self::Unknown { church_true, .. } => *church_true,
            Self::Known(_) => None,
        }
    }

    /// Rebuild with a per-bool `church_true` witness. `Known` shapes are
    /// returned unchanged — their convention is the canonical CIP one.
    pub(crate) fn with_church_true(self, church_true: Option<usize>) -> Self {
        match self {
            Self::Unknown {
                tag, arity, origin, ..
            } => Self::Unknown {
                tag,
                arity,
                origin,
                church_true,
            },
            known => known,
        }
    }

    /// Origin of this shape's tag. `Known` constructors are data tags.
    pub(crate) fn origin(&self) -> ConstructorOrigin {
        match self {
            Self::Known(_) => ConstructorOrigin::DataTag,
            Self::Unknown { origin, .. } => *origin,
        }
    }

    /// Rebuild this shape with a new arity, **preserving** tag and origin.
    /// `Known` shapes are returned unchanged (their arity is canonical).
    pub(crate) fn with_arity(self, arity: usize) -> Self {
        match self {
            Self::Unknown {
                tag,
                origin,
                church_true,
                ..
            } => Self::Unknown {
                tag,
                arity,
                origin,
                church_true,
            },
            known => known,
        }
    }

    /// Rebuild this shape with a new tag, **preserving** arity and origin.
    /// `Known` shapes are returned unchanged.
    pub(crate) fn with_tag(self, tag: usize) -> Self {
        match self {
            Self::Unknown {
                arity,
                origin,
                church_true,
                ..
            } => Self::Unknown {
                tag,
                arity,
                origin,
                church_true,
            },
            known => known,
        }
    }

    /// Wrap a known constructor.
    pub(crate) fn known(kc: KnownConstructor) -> Self {
        Self::Known(kc)
    }

    /// Canonical pretty-printable name when known.
    pub(crate) fn pretty_name(&self) -> Option<&'static str> {
        match self {
            Self::Known(kc) => Some(kc.pretty_name()),
            Self::Unknown { .. } => None,
        }
    }

    /// Resolve a display name for rendering.
    ///
    /// Returns the canonical ABI-anchored name from
    /// [`KnownConstructor::pretty_name`] when `Known`, otherwise
    /// `fallback` — typically the user-defined name stored alongside the
    /// shape during AST construction. Prefer this over reading a
    /// stringly-typed `name` field: closed-set display stays anchored to
    /// `ConstructorShape` while `Unknown` shapes keep their source name.
    pub(crate) fn display_name_or<'a>(&'a self, fallback: Option<&'a str>) -> Option<&'a str> {
        self.pretty_name().or(fallback)
    }

    /// Plutus `Constr` tag for this shape.
    pub(crate) fn tag(&self) -> usize {
        match self {
            Self::Known(kc) => kc.expected_tag(),
            Self::Unknown { tag, .. } => *tag,
        }
    }

    /// Number of fields this shape carries.
    pub(crate) fn arity(&self) -> usize {
        match self {
            Self::Known(kc) => kc.expected_arity(),
            Self::Unknown { arity, .. } => *arity,
        }
    }

    /// `true` if this shape is one of the closed-set constructors.
    pub(crate) fn is_known(&self) -> bool {
        matches!(self, Self::Known(_))
    }

    /// Underlying `KnownConstructor` if this shape is in the closed set.
    pub(crate) fn as_known(&self) -> Option<KnownConstructor> {
        match self {
            Self::Known(kc) => Some(*kc),
            Self::Unknown { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests;
