//! Wire types for the decompilation-option catalogue.
//!
//! The crate owns the option list; these types are the WIRE for it, kept
//! separate from the crate's own descriptor types so the wire format is
//! not pinned to Rust field names, and so the exhaustive matches below
//! turn a new `OptionKind` or `ChoicePayload` into a compile error rather
//! than a silently-dropped control.
//!
//! `path`, `field` and `value` stay verbatim (snake_case / PascalCase):
//! they are request-body keys and serde tags, not display text.

use serde::Serialize;

/// `GET /api/options`.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OptionCatalogueDto {
    /// Bumped when the catalogue's SHAPE changes, not when an option is
    /// added.
    pub version: u32,
    /// Panel sections, in render order.
    pub groups: Vec<OptionGroupDto>,
    /// The exact object to POST as `options` for the server's default
    /// behaviour: the server's own default request, so it carries web
    /// overrides like `synthesize_stub_adts: false`, not the crate's.
    pub defaults: serde_json::Value,
}

/// One panel section.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OptionGroupDto {
    pub id: &'static str,
    pub title: &'static str,
    pub summary: &'static str,
    pub detail: &'static [&'static str],
    /// Present for the five pass groups: the object a master
    /// all-on/all-off switch writes every member of.
    pub master_path: Option<&'static [&'static str]>,
    pub options: Vec<OptionDescriptorDto>,
}

/// One control.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OptionDescriptorDto {
    /// Where this option lives in the request body, as data.
    pub path: &'static [&'static str],
    pub field: &'static str,
    pub label: &'static str,
    pub summary: &'static str,
    pub detail: &'static [&'static str],
    /// The CLI flag that drives this option, if any. Polarity may be
    /// inverted (`synthesize_stub_adts` is driven by `--no-stub-adts`).
    pub cli_flag: Option<&'static str>,
    pub kind: OptionKindDto,
}

/// What sort of control this is.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type", rename_all = "camelCase")]
pub enum OptionKindDto {
    Toggle,
    Choice {
        /// Label for "no value", when the option can be unset.
        unset: Option<&'static str>,
        choices: Vec<OptionChoiceDto>,
    },
}

/// One selectable value.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OptionChoiceDto {
    /// The serde tag to send. Never a display string.
    pub value: &'static str,
    pub label: &'static str,
    pub summary: &'static str,
    /// Extra input this choice needs, if any.
    pub payload: Option<ChoicePayloadDto>,
}

/// Extra input a choice needs beyond being picked.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type", rename_all = "camelCase")]
pub enum ChoicePayloadDto {
    /// The choice travels as the object `{ <key>: <count> }`. `key` is
    /// carried so a consumer builds that object from the descriptor
    /// rather than knowing which option it is looking at.
    Count {
        key: &'static str,
        min: u32,
        default: u32,
    },
}

impl OptionCatalogueDto {
    /// Build the catalogue response from the crate's static catalogue.
    ///
    /// `defaults` is supplied by the caller because the DEFAULT request
    /// belongs to the API layer, not the crate.
    pub fn from_catalogue(defaults: serde_json::Value) -> Self {
        let groups = dehosk::decompile::options::GROUPS
            .iter()
            .map(|group| OptionGroupDto {
                id: group.id.token(),
                title: group.title,
                summary: group.summary,
                detail: group.detail,
                master_path: group.master_path,
                options: dehosk::decompile::options::ui_options_in(group.id)
                    .into_iter()
                    .filter_map(OptionDescriptorDto::from_entry)
                    .collect(),
            })
            .collect();
        Self {
            version: dehosk::decompile::options::CATALOGUE_VERSION,
            groups,
            defaults,
        }
    }
}

impl OptionDescriptorDto {
    /// `None` for an entry with no UI control.
    ///
    /// The match is exhaustive on purpose: a new `Exposure` variant
    /// fails the build here rather than reaching the frontend as
    /// nothing at all.
    pub fn from_entry(entry: &'static dehosk::decompile::options::OptionEntry) -> Option<Self> {
        use dehosk::decompile::options::Exposure;
        match entry.exposure {
            Exposure::Ui {
                label,
                group: _,
                kind,
                cli_flag,
            } => Some(Self {
                path: entry.path,
                field: entry.field,
                label,
                summary: entry.summary,
                detail: entry.detail,
                cli_flag,
                kind: OptionKindDto::from_kind(kind),
            }),
            Exposure::Nested { .. } | Exposure::Internal { .. } => None,
        }
    }
}

impl OptionKindDto {
    /// A new `OptionKind` variant is a compile error here — which is
    /// the point: a control with no wire mapping must not ship.
    pub fn from_kind(kind: dehosk::decompile::options::OptionKind) -> Self {
        use dehosk::decompile::options::OptionKind;
        match kind {
            OptionKind::Toggle => Self::Toggle,
            OptionKind::Choice { choices, unset } => Self::Choice {
                unset,
                choices: choices
                    .iter()
                    .map(|choice| OptionChoiceDto {
                        value: choice.value,
                        label: choice.label,
                        summary: choice.summary,
                        payload: choice.payload.map(ChoicePayloadDto::from_payload),
                    })
                    .collect(),
            },
        }
    }
}

impl ChoicePayloadDto {
    /// A new `ChoicePayload` variant is a compile error here.
    pub fn from_payload(payload: dehosk::decompile::options::ChoicePayload) -> Self {
        use dehosk::decompile::options::ChoicePayload;
        match payload {
            ChoicePayload::Count { key, min, default } => Self::Count { key, min, default },
        }
    }
}
