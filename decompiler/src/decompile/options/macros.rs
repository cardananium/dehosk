//! The two macros that define the options structs and their catalogue
//! entries from a single list.
//!
//! A struct and a catalogue written out separately are two lists that
//! must agree; `define_pipeline_passes!`
//! ([`crate::decompile::pipeline_passes`]) generates the pass enum,
//! its `ALL` slice and its per-pass metadata from one list for the
//! same reason.
//!
//! Here the guarantee is stronger than "a test notices". A field that
//! is not in the catalogue does not exist, because the catalogue
//! entry and the struct field are the same piece of source text. The
//! grammar makes each omission a parse error: a bare `pub foo: bool`,
//! a field with a label but no doc comment, a doc comment but no
//! `=> "Label"`, or (top level) a field with no `= Exposure::…`.
//!
//! The summary line is written once, as the field's first doc line, and
//! the macro emits it both as rustdoc and into the catalogue entry — so
//! `cargo doc` and the web panel cannot describe a field differently.

/// Define the group-id enum, its wire tokens and its `ALL` list from ONE
/// list of variants.
///
/// `ALL` is why this is a macro. A hand-written `ALL` is a second list:
/// adding a variant forces nobody to extend it (the array literal still
/// type-checks at its old length), so
/// `tests::groups_cover_every_group_id` would skip the new group and a
/// group with no [`super::OptionGroup`] would reach a consumer as a
/// heading that does not exist. Generated from the variant list, `ALL`
/// covers a new variant by construction.
///
/// Each variant must carry a doc comment and a token; neither has a
/// default, so a variant cannot arrive unlabelled.
macro_rules! define_group_ids {
    (
        $(#[$eattr:meta])*
        $Name:ident {
            $(
                $(#[doc = $doc:literal])+
                $Variant:ident => $token:literal
            ),+ $(,)?
        }
    ) => {
        $(#[$eattr])*
        pub enum $Name {
            $(
                $(#[doc = $doc])+
                $Variant,
            )+
        }

        impl $Name {
            /// The stable wire token for this group.
            ///
            /// Generated from the variant list with no `_` arm, so a
            /// new variant cannot reach a consumer unlabelled.
            pub const fn token(self) -> &'static str {
                match self {
                    $(Self::$Variant => $token,)+
                }
            }

            /// Every group, in declaration order.
            ///
            /// Generated from the same list as the variants — there is
            /// no second list that could go short.
            pub const ALL: &'static [$Name] = &[$($Name::$Variant),+];
        }
    };
}
pub(crate) use define_group_ids;

/// Build an option's JSON path from a container prefix and a field name.
///
/// `$prefix` arrives as ONE token tree (`["simplify_passes"]`) rather
/// than a repetition, because a `$(…),*` prefix cannot be expanded
/// inside the `$(…)+` repetition over fields — the two repeat different
/// numbers of times and rustc rejects it.
macro_rules! option_path {
    ([$($prefix:literal),* $(,)?], $field:ident) => {
        &[$($prefix,)* stringify!($field)]
    };
}
pub(crate) use option_path;

/// Define a group of leaf pass toggles: the struct, its `all_on` /
/// `all_off` / `any_enabled` / `get` / `set`, and its catalogue
/// `ENTRIES` — all from one list of fields.
///
/// Every leaf is a `bool` and an [`crate::decompile::options::OptionKind::Toggle`],
/// so neither is written per field.
///
/// ```ignore
/// define_pass_group! {
///     /// Struct-level rustdoc.
///     #[derive(Debug, Clone, Copy)]
///     SimplifyPasses in GroupId::Simplify, path ["simplify_passes"] {
///         /// Summary line — becomes the field's first rustdoc line.
///         /// Any further lines become the catalogue `detail`.
///         inline_fp => "Inline fixed-point",
///     }
/// }
/// ```
///
/// Do NOT write the blank line between summary and detail: the macro
/// emits it, so that the summary is a standalone rustdoc first line.
macro_rules! define_pass_group {
    (
        $(#[$sattr:meta])*
        $Name:ident in $group:expr, path $prefix:tt {
            $(
                #[doc = $summary:literal]
                $(#[doc = $detail:literal])*
                $field:ident => $label:literal
            ),+ $(,)?
        }
    ) => {
        $(#[$sattr])*
        pub struct $Name {
            $(
                #[doc = $summary]
                #[doc = ""]
                $(#[doc = $detail])*
                pub $field: bool,
            )+
        }

        impl $Name {
            /// Every pass in this group enabled.
            pub const fn all_on() -> Self {
                Self { $($field: true),+ }
            }

            /// Every pass in this group disabled.
            pub const fn all_off() -> Self {
                Self { $($field: false),+ }
            }

            /// True iff ANY pass in this group is enabled (used to skip
            /// the whole cluster when nothing inside it would run).
            ///
            /// Generated from the field list, so it cannot omit a leaf
            /// the way a hand-written `||` chain can.
            pub const fn any_enabled(&self) -> bool {
                false $(|| self.$field)+
            }

            /// Read one leaf by its field name; `None` if this group has
            /// no such field.
            pub fn get(&self, field: &str) -> Option<bool> {
                match field {
                    $(stringify!($field) => Some(self.$field),)+
                    _ => None,
                }
            }

            /// Write one leaf by its field name; `false` if this group
            /// has no such field.
            pub fn set(&mut self, field: &str, value: bool) -> bool {
                match field {
                    $(stringify!($field) => { self.$field = value; true })+
                    _ => false,
                }
            }

            /// This group's catalogue entries, in declaration order.
            pub const ENTRIES: &'static [$crate::decompile::options::OptionEntry] = &[
                $($crate::decompile::options::OptionEntry {
                    field: stringify!($field),
                    path: $crate::decompile::options::macros::option_path!($prefix, $field),
                    summary: $summary.trim_ascii(),
                    detail: &[$($detail.trim_ascii()),*],
                    exposure: $crate::decompile::options::Exposure::Ui {
                        label: $label,
                        group: $group,
                        kind: $crate::decompile::options::OptionKind::Toggle,
                        cli_flag: None,
                    },
                }),+
            ];
        }
    };
}
pub(crate) use define_pass_group;

/// Define a struct of mixed-type options: the struct and its catalogue
/// `ENTRIES`, from one list of fields.
///
/// Each field must declare its type AND how it is exposed — there is no
/// default classification, so a new field cannot slip in as "probably
/// internal".
///
/// ```ignore
/// define_options! {
///     #[derive(Debug, Clone)]
///     DecompileOptions, path [] {
///         /// Summary line.
///         /// Detail lines.
///         safe_mode: bool = Exposure::Ui { label: "Safe Mode", group: …, kind: OptionKind::Toggle, cli_flag: Some("--safe-mode") },
///     }
/// }
/// ```
macro_rules! define_options {
    (
        $(#[$sattr:meta])*
        $Name:ident, path $prefix:tt {
            $(
                #[doc = $summary:literal]
                $(#[doc = $detail:literal])*
                $field:ident : $ty:ty = $exposure:expr
            ),+ $(,)?
        }
    ) => {
        $(#[$sattr])*
        pub struct $Name {
            $(
                #[doc = $summary]
                #[doc = ""]
                $(#[doc = $detail])*
                pub $field: $ty,
            )+
        }

        impl $Name {
            /// This struct's catalogue entries, in declaration order.
            pub const ENTRIES: &'static [$crate::decompile::options::OptionEntry] = &[
                $($crate::decompile::options::OptionEntry {
                    field: stringify!($field),
                    path: $crate::decompile::options::macros::option_path!($prefix, $field),
                    summary: $summary.trim_ascii(),
                    detail: &[$($detail.trim_ascii()),*],
                    exposure: $exposure,
                }),+
            ];
        }
    };
}
pub(crate) use define_options;
