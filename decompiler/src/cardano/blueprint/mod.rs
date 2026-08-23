//! Plutus Blueprint (plutus.json) parsing: validator metadata and type
//! definitions, used as decompilation hints.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

use crate::error::{DecompileError, Result};

/// A Plutus blueprint (plutus.json).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Blueprint {
    /// Blueprint preamble with metadata.
    pub preamble: Preamble,

    /// List of validators in this blueprint.
    pub validators: Vec<ValidatorBlueprint>,

    /// Additional definitions (types, etc.)
    #[serde(default)]
    pub definitions: HashMap<String, serde_json::Value>,
}

/// Blueprint preamble with project metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Preamble {
    /// Project title.
    pub title: String,

    /// Project description.
    #[serde(default)]
    pub description: String,

    /// Project version.
    pub version: String,

    /// Plutus version used.
    #[serde(default)]
    pub plutus_version: String,

    /// Compiler name and version.
    #[serde(default)]
    pub compiler: Option<CompilerInfo>,

    /// License.
    #[serde(default)]
    pub license: String,
}

/// Compiler information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilerInfo {
    /// Compiler name.
    pub name: String,

    /// Compiler version.
    pub version: String,
}

/// A validator in the blueprint.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidatorBlueprint {
    /// Validator title/name.
    pub title: String,

    /// Validator description.
    #[serde(default)]
    pub description: String,

    /// Datum schema (for spend validators).
    #[serde(default)]
    pub datum: Option<ParameterSchema>,

    /// Redeemer schema. Optional because `else` entries omit it
    /// (CIP-0117 §3.2: the `else` arm receives the raw
    /// `ScriptContext` and has no per-purpose redeemer).
    #[serde(default)]
    pub redeemer: Option<ParameterSchema>,

    /// Additional parameters (for parameterized validators).
    #[serde(default)]
    pub parameters: Vec<ParameterSchema>,

    /// Compiled CBOR code (hex encoded).
    pub compiled_code: String,

    /// Script hash.
    pub hash: String,
}

impl ValidatorBlueprint {
    pub fn datum_name(&self) -> Option<&str> {
        self.datum.as_ref().and_then(|d| d.title.as_deref())
    }

    pub fn redeemer_name(&self) -> Option<&str> {
        self.redeemer.as_ref().and_then(|r| r.title.as_deref())
    }

    /// Get parameter names in order: parameters → datum → redeemer.
    /// Entries without a corresponding schema are skipped (`else`
    /// entries legitimately have no redeemer).
    pub fn parameter_names(&self) -> Vec<Option<&str>> {
        let mut names = Vec::new();

        for param in &self.parameters {
            names.push(param.title.as_deref());
        }

        if let Some(datum) = &self.datum {
            names.push(datum.title.as_deref());
        }

        if let Some(redeemer) = &self.redeemer {
            names.push(redeemer.title.as_deref());
        }

        names
    }

    /// Decode the compiled code from hex.
    pub fn decode_code(&self) -> Result<Vec<u8>> {
        hex::decode(&self.compiled_code).map_err(|e| DecompileError::decode(e.to_string()))
    }
}

/// Schema for a parameter (datum, redeemer, or parameter).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParameterSchema {
    /// Parameter title/name.
    #[serde(default)]
    pub title: Option<String>,

    /// Parameter description.
    #[serde(default)]
    pub description: Option<String>,

    /// Schema reference or inline schema.
    #[serde(flatten)]
    pub schema: SchemaContent,
}

/// Schema content (either a reference or inline definition).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum SchemaContent {
    /// Reference to a definition.
    Reference {
        #[serde(rename = "$ref")]
        reference: String,
    },

    /// Inline schema.
    Inline {
        #[serde(flatten)]
        content: HashMap<String, serde_json::Value>,
    },
}

impl SchemaContent {
    pub fn as_reference(&self) -> Option<&str> {
        match self {
            Self::Reference { reference } => Some(reference),
            Self::Inline { .. } => None,
        }
    }

    /// Try to extract a simple type name from the schema.
    pub fn type_name(&self) -> Option<String> {
        match self {
            Self::Reference { reference } => {
                // Extract type name from reference like "#/definitions/MyType"
                reference.split('/').next_back().map(String::from)
            }
            Self::Inline { content } => content
                .get("dataType")
                .and_then(|v| v.as_str())
                .map(String::from),
        }
    }
}

/// Type definition extracted from blueprint.
#[derive(Debug, Clone)]
pub struct TypeDefinition {
    /// Type name.
    pub name: String,
    /// Constructor variants (for sum types).
    pub constructors: Vec<ConstructorDef>,
    /// Is this a record type (single constructor).
    pub is_record: bool,
}

/// Constructor definition.
#[derive(Debug, Clone)]
pub struct ConstructorDef {
    /// Constructor name.
    pub name: String,
    /// Constructor tag (index).
    pub tag: usize,
    /// Fields.
    pub fields: Vec<FieldDef>,
}

/// Field definition.
#[derive(Debug, Clone)]
pub struct FieldDef {
    /// Field name.
    pub name: Option<String>,
    /// Field type reference.
    pub type_ref: Option<String>,
    /// Field index.
    pub index: usize,
}

impl Blueprint {
    pub fn from_json(json: &str) -> Result<Self> {
        serde_json::from_str(json).map_err(|e| DecompileError::blueprint(e.to_string()))
    }

    pub fn from_file(path: impl AsRef<Path>) -> Result<Self> {
        let content = std::fs::read_to_string(path)?;
        Self::from_json(&content)
    }

    /// Find a validator by title.
    pub fn find_validator(&self, title: &str) -> Option<&ValidatorBlueprint> {
        self.validators.iter().find(|v| v.title == title)
    }

    pub fn get_validator_code(&self, title: &str) -> Result<&str> {
        self.find_validator(title)
            .map(|v| v.compiled_code.as_str())
            .ok_or_else(|| DecompileError::ValidatorNotFound(title.to_string()))
    }

    pub fn validator_titles(&self) -> Vec<&str> {
        self.validators.iter().map(|v| v.title.as_str()).collect()
    }

    /// Group validators by their compiled-image hash.
    ///
    /// Several `ValidatorBlueprint` entries can point at one compiled
    /// image — a module's `spend` and `mint` share a hash. The
    /// validator-block render emits one `validator NAME { spend(...)
    /// {...} mint(...) {...} }` block per group, one arm per entry.
    ///
    /// Groups come back in first-appearance order of each hash in
    /// `validators`.
    pub fn validators_by_hash(&self) -> Vec<Vec<&ValidatorBlueprint>> {
        let mut order: Vec<&str> = Vec::new();
        let mut groups: std::collections::HashMap<&str, Vec<&ValidatorBlueprint>> =
            std::collections::HashMap::new();
        for v in &self.validators {
            let entry = groups.entry(v.hash.as_str()).or_default();
            if entry.is_empty() {
                order.push(v.hash.as_str());
            }
            entry.push(v);
        }
        order
            .into_iter()
            .map(|h| groups.remove(h).unwrap_or_default())
            .collect()
    }

    pub fn extract_types(&self) -> Vec<TypeDefinition> {
        let mut types = Vec::new();

        for (name, def) in &self.definitions {
            if let Some(type_def) = Self::parse_type_definition(name, def) {
                types.push(type_def);
            }
        }

        types
    }

    fn parse_type_definition(name: &str, value: &serde_json::Value) -> Option<TypeDefinition> {
        let obj = value.as_object()?;

        // Check for anyOf (sum type) or single constructor (record type)
        if let Some(any_of) = obj.get("anyOf").and_then(|v| v.as_array()) {
            let constructors: Vec<ConstructorDef> = any_of
                .iter()
                .enumerate()
                .filter_map(|(tag, c)| Self::parse_constructor(c, tag))
                .collect();

            if !constructors.is_empty() {
                return Some(TypeDefinition {
                    name: name.to_string(),
                    constructors,
                    is_record: false,
                });
            }
        } else if let Some(constructor) = Self::parse_constructor(value, 0) {
            return Some(TypeDefinition {
                name: name.to_string(),
                constructors: vec![constructor],
                is_record: true,
            });
        }

        None
    }

    fn parse_constructor(value: &serde_json::Value, default_tag: usize) -> Option<ConstructorDef> {
        let obj = value.as_object()?;

        let name = obj
            .get("title")
            .and_then(|v| v.as_str())
            .unwrap_or("Unknown")
            .to_string();

        let tag = obj
            .get("index")
            .and_then(|v| v.as_u64())
            .map(|i| i as usize)
            .unwrap_or(default_tag);

        let fields = if let Some(fields_value) = obj.get("fields").and_then(|v| v.as_array()) {
            fields_value
                .iter()
                .enumerate()
                .filter_map(|(idx, f)| Self::parse_field(f, idx))
                .collect()
        } else {
            Vec::new()
        };

        Some(ConstructorDef { name, tag, fields })
    }

    fn parse_field(value: &serde_json::Value, index: usize) -> Option<FieldDef> {
        let obj = value.as_object()?;

        let name = obj.get("title").and_then(|v| v.as_str()).map(String::from);

        let type_ref = obj
            .get("$ref")
            .and_then(|v| v.as_str())
            .map(|r| r.split('/').next_back().unwrap_or("Unknown").to_string())
            .or_else(|| {
                obj.get("dataType")
                    .and_then(|v| v.as_str())
                    .map(String::from)
            });

        Some(FieldDef {
            name,
            type_ref,
            index,
        })
    }

    /// Resolve a type reference to its definition.
    pub fn resolve_type(&self, reference: &str) -> Option<&serde_json::Value> {
        let type_name = reference.strip_prefix("#/definitions/")?;
        self.definitions.get(type_name)
    }

    pub fn get_constructor_info(&self, type_name: &str, tag: usize) -> Option<ConstructorDef> {
        let types = self.extract_types();
        types
            .into_iter()
            .find(|t| t.name == type_name)
            .and_then(|t| t.constructors.into_iter().find(|c| c.tag == tag))
    }
}

/// Helper to build type hints from blueprint for decompilation.
#[derive(Debug, Clone, Default)]
pub struct BlueprintHints {
    /// Validator parameter names.
    pub param_names: Vec<String>,
    /// Type definitions for reference.
    pub types: HashMap<String, TypeDefinition>,
    /// Constructor name lookup: (type_name, tag) -> constructor_name
    pub constructor_names: HashMap<(String, usize), String>,
    // No `PseudoType` field can live here: `PseudoType` holds `Rc<...>`
    // (non-Send) while `BlueprintHints` crosses the Send-bound closure
    // in `lib.rs::run_on_large_stack`, so this struct carries names and
    // raw schema references only.
}

impl BlueprintHints {
    pub fn from_blueprint(blueprint: &Blueprint, validator_title: &str) -> Option<Self> {
        let validator = blueprint.find_validator(validator_title)?;

        let param_names: Vec<String> = validator
            .parameter_names()
            .into_iter()
            .map(|n| n.unwrap_or("_").to_string())
            .collect();

        let type_defs = blueprint.extract_types();
        let types: HashMap<String, TypeDefinition> =
            type_defs.into_iter().map(|t| (t.name.clone(), t)).collect();

        let mut constructor_names = HashMap::new();
        for (type_name, type_def) in &types {
            for constr in &type_def.constructors {
                constructor_names.insert((type_name.clone(), constr.tag), constr.name.clone());
            }
        }

        Some(Self {
            param_names,
            types,
            constructor_names,
        })
    }

    pub fn get_constructor_name(&self, type_name: &str, tag: usize) -> Option<&str> {
        self.constructor_names
            .get(&(type_name.to_string(), tag))
            .map(|s| s.as_str())
    }

    pub fn get_field_names(&self, type_name: &str, tag: usize) -> Vec<Option<String>> {
        self.types
            .get(type_name)
            .and_then(|t| t.constructors.iter().find(|c| c.tag == tag))
            .map(|c| c.fields.iter().map(|f| f.name.clone()).collect())
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests;
