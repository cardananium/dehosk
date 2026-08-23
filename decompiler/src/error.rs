//! Error types for the decompiler.

use miette::Diagnostic;
use thiserror::Error;

/// Result type alias for decompiler operations.
pub type Result<T> = std::result::Result<T, DecompileError>;

/// Errors that can occur during decompilation.
#[derive(Error, Diagnostic, Debug)]
pub enum DecompileError {
    /// Failed to decode UPLC from bytes.
    #[error("Failed to decode UPLC: {0}")]
    #[diagnostic(code(decompiler::decode))]
    DecodeError(String),

    /// Invalid hex string.
    #[error("Invalid hex string: {0}")]
    #[diagnostic(code(decompiler::hex))]
    HexError(#[from] hex::FromHexError),

    /// IO error.
    #[error("IO error: {0}")]
    #[diagnostic(code(decompiler::io))]
    IoError(#[from] std::io::Error),

    /// JSON parsing error.
    #[error("JSON error: {0}")]
    #[diagnostic(code(decompiler::json))]
    JsonError(#[from] serde_json::Error),

    /// Blueprint parsing error.
    #[error("Blueprint error: {0}")]
    #[diagnostic(code(decompiler::blueprint))]
    BlueprintError(String),

    /// Validator not found in blueprint.
    #[error("Validator '{0}' not found in blueprint")]
    #[diagnostic(code(decompiler::validator_not_found))]
    ValidatorNotFound(String),

    /// Unknown builtin surfaced in the pseudo AST.
    #[error("Unknown builtin '{name}' during {stage}")]
    #[diagnostic(code(decompiler::unknown_builtin))]
    UnknownBuiltin { name: String, stage: String },

    /// Unsupported UPLC construct.
    #[error("Unsupported UPLC construct: {0}")]
    #[diagnostic(code(decompiler::unsupported))]
    Unsupported(String),

    /// `DecompileOptions` violates a pass-dependency invariant.
    /// Reported up-front (before the pipeline runs) so library
    /// users get a clean error instead of a runtime panic.
    #[error("Invalid DecompileOptions: {0}")]
    #[diagnostic(code(decompiler::invalid_options))]
    InvalidOptions(String),

    /// Internal error.
    #[error("Internal error: {0}")]
    #[diagnostic(code(decompiler::internal))]
    Internal(String),
}

impl DecompileError {
    pub(crate) fn decode(msg: impl Into<String>) -> Self {
        Self::DecodeError(msg.into())
    }

    pub(crate) fn blueprint(msg: impl Into<String>) -> Self {
        Self::BlueprintError(msg.into())
    }

    pub(crate) fn unknown_builtin(name: impl Into<String>, stage: impl Into<String>) -> Self {
        Self::UnknownBuiltin {
            name: name.into(),
            stage: stage.into(),
        }
    }

    pub(crate) fn unsupported(msg: impl Into<String>) -> Self {
        Self::Unsupported(msg.into())
    }

    pub(crate) fn internal(msg: impl Into<String>) -> Self {
        Self::Internal(msg.into())
    }

    pub(crate) fn invalid_options(msg: impl Into<String>) -> Self {
        Self::InvalidOptions(msg.into())
    }
}
