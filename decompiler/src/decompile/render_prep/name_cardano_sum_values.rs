//! Name a Cardano sum constructor that appears as a VALUE.
//!
//! [`super::name_cardano_sum_arms`] names the constructors a `when`
//! MATCHES. The same type built as a value goes unnamed, and the two
//! halves of one comparison end up speaking different languages:
//!
//! ```text
//! when entry.1st is {
//!   ConstitutionalCommitteeMember(value) -> value == Unknown_E_1_0(#"00")
//!   …
//! }
//! ```
//!
//! `value` is a `Credential`, so the thing it is compared against is one
//! too — `VerificationKey(#"00")`. A sibling fixture that reaches the
//! same credential through a PATTERN renders exactly that, which is what
//! makes the mismatch visible.
//!
//! The evidence is the comparison itself. `==` is homogeneous, so a side
//! whose Cardano type the env knows types the other side; there is no
//! guessing about what an unrelated `Constr` might be. Three further
//! gates keep it honest:
//!
//!   * The constructor must be UNRESOLVED (an `Unknown` shape). A
//!     recovered or user-typed constructor already says what it is.
//!   * Its tag and field count must match the sum's ABI exactly —
//!     `known_ctor_arity`, the same check the arm naming applies.
//!   * A real (non-stub) `type_hint` is left alone: a user ADT attached
//!     by the blueprint outranks a schema guess.
//!
//! Stamping the sum's legacy-name hint is all it takes; the renderer
//! resolves the constructor name from the registry, exactly as it does
//! for a named arm.

use crate::decompile::ScriptVersion;
use crate::decompile::simplify::postprocess::SumTypeId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::fold::ExprFolder;

use super::cardano_type_env::CardanoTypeEnv;
use super::ctx::RenderCtx;
use super::name_cardano_sum_arms::{is_stub_type_hint, known_ctor_arity};

pub(super) fn name_cardano_sum_values(
    expr: PseudoExpr,
    env: &CardanoTypeEnv,
    ctx: &RenderCtx,
) -> PseudoExpr {
    let version = ctx.version_or_v2();
    Namer { env, version, ctx }.fold(expr)
}

struct Namer<'a> {
    env: &'a CardanoTypeEnv,
    version: ScriptVersion,
    ctx: &'a RenderCtx,
}

impl Namer<'_> {
    /// The sum type an operand is known to have.
    fn sum_of(&self, expr: &PseudoExpr) -> Option<SumTypeId> {
        self.env.infer_sum(expr, self.version)
    }

    /// Stamp `sum`'s hint on an unresolved constructor of the right shape.
    fn stamp(&self, expr: PseudoExpr, sum: SumTypeId) -> PseudoExpr {
        let PseudoExpr::Constr {
            type_hint,
            tag,
            fields,
            shape,
        } = expr
        else {
            return expr;
        };
        let nameable = matches!(shape, ConstructorShape::Unknown { .. })
            && known_ctor_arity(sum, tag, self.ctx) == Some(fields.len())
            && type_hint.as_ref().is_none_or(is_stub_type_hint)
            && (sum != SumTypeId::Credential || fields.first().is_some_and(builds_bytearray));
        PseudoExpr::Constr {
            type_hint: if nameable {
                Some(crate::decompile::TypeHintId::new(sum.display_name()))
            } else {
                type_hint
            },
            tag,
            fields,
            shape,
        }
    }
}

impl ExprFolder for Namer<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_binop(
        &mut self,
        op: crate::pseudo::ast::BinaryOp,
        left: PseudoExpr,
        right: PseudoExpr,
    ) -> PseudoExpr {
        if !matches!(op, crate::pseudo::ast::BinaryOp::Eq) {
            return PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            };
        }
        // Type flows from the side the env knows to the side it does not.
        let (left, right) = match (self.sum_of(&left), self.sum_of(&right)) {
            (Some(sum), None) => (left, self.stamp(right, sum)),
            (None, Some(sum)) => (self.stamp(left, sum), right),
            _ => (left, right),
        };
        PseudoExpr::BinOp {
            op,
            left: PBox::new(left),
            right: PBox::new(right),
        }
    }
}

/// Whether an expression PRODUCES a byte string.
///
/// `Credential` needs this and the other sums do not, for the reason
/// `name_cardano_sum_arms` spells out at its own Credential gate:
/// `merge_isomorphic_stub_adts` pools every `{(0,1),(1,1)}` stub, so
/// tag-and-arity alone does not separate a real `Credential` — which is
/// `Constr<0|1>(ByteArray)` — from any other two-variant one-field
/// shape. A literal, or a `b_data`/`un_b_data` call, is that witness;
/// anything else fails closed and keeps the honest `Unknown_*` name.
fn builds_bytearray(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::ByteArray(_) => true,
        PseudoExpr::Data(d) => matches!(d.as_ref(), crate::pseudo::ast::PseudoData::ByteString(_)),
        PseudoExpr::BuiltinCall { name, args } => {
            matches!(
                name,
                crate::BuiltinId::DataByteArray | crate::BuiltinId::DataUnByteArray
            ) || args.first().is_some_and(builds_bytearray)
        }
        PseudoExpr::Apply { function, args } => match function.as_ref() {
            PseudoExpr::BuiltinCall { name, .. } => matches!(
                name,
                crate::BuiltinId::DataByteArray | crate::BuiltinId::DataUnByteArray
            ),
            _ => args.first().is_some_and(builds_bytearray),
        },
        _ => false,
    }
}

#[cfg(test)]
mod tests;
