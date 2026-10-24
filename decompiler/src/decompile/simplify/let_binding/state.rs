use crate::decompile::simplify::state::{LexicalNameShadow, SelectorBinding};
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

/// State captured after pre-processing of simplify_let, held while the
/// value is simplified until mid-processing consumes it.
pub(crate) struct LetAfterValueState {
    pub name: String,
    pub var_id: Option<VarId>,
    pub name_shadow: LexicalNameShadow,
    pub body: PseudoExpr,
    pub is_y_comb: bool,
    pub is_and: bool,
    pub is_or: bool,
    pub has_delayed_rec: bool,
    pub has_delayed_fst: bool,
    pub has_delayed_snd: bool,
}

/// State captured after mid-processing of simplify_let, held while the
/// body is simplified until post-processing consumes it.
pub(crate) struct LetAfterBodyState {
    pub name: String,
    pub var_id: Option<VarId>,
    pub name_shadow: LexicalNameShadow,
    pub simplified_value: PseudoExpr,
    pub is_y_comb: bool,
    pub is_and: bool,
    pub is_or: bool,
    pub has_delayed_rec: bool,
    pub has_delayed_fst: bool,
    pub has_delayed_snd: bool,
    pub is_builtin_alias: bool,
    pub is_partial_app: bool,
    pub selector_entry: Option<((usize, usize), Option<SelectorBinding>)>,
    pub track_non_thunk: bool,
    pub already_tracked_non_thunk: bool,
    pub pre_context_name: Option<String>,
}

/// Result from post-processing of simplify_let.
pub(crate) enum LetPostResult {
    /// Simplification complete; this is the Let's result.
    Done(PseudoExpr),
    /// The expression needs another fold before it becomes the result.
    Resimplify(PseudoExpr),
}
