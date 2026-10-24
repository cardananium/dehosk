//! Main simplification transform for `PseudoExpr`: the `simplify`
//! entry point, the shared `simplify_*` helpers, and the `Walker`
//! impl that drives them.

use super::apply::ApplyAction;
use super::state::DelayRestoreList;
use super::step::Step;
use super::{BuiltinId, Simplifier};
use crate::decompile::constructor_data::{
    ConstrPairProjection, rewrite_constr_unpack_pair_projection,
};
use crate::decompile::list_traversal::{list_literal_parts, list_subject_and_tail_depth};
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoData, PseudoExpr, UnaryOp};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;
use crate::pseudo::walker::{Entered, Walker};

mod entry;

pub(crate) use self::entry::simplify_with_state_opts;
// Test-only entry points: the suites drive the simplifier standalone,
// the pipeline always goes through `simplify_with_state_opts`.
#[cfg(test)]
pub(crate) use self::entry::{simplify, simplify_with_options, simplify_with_state};

impl Simplifier {
    pub(super) fn delay_depth(expr: &PseudoExpr) -> u8 {
        let mut depth = 0u8;
        let mut current = expr;
        while let PseudoExpr::Delay(inner) = current {
            depth = depth.saturating_add(1);
            current = inner.as_ref();
        }
        depth
    }

    fn force_chain_var(expr: &PseudoExpr) -> Option<(String, Option<VarId>, u8)> {
        let mut depth: u8 = 0;
        let mut current = expr;
        while let PseudoExpr::Force(inner) = current {
            depth = depth.saturating_add(1);
            current = inner.as_ref();
        }
        if depth == 0 {
            return None;
        }
        if let PseudoExpr::Var { name, id, .. } = current {
            Some((name.clone(), *id, depth))
        } else {
            None
        }
    }

    fn make_var_for_observed_ref(&self, name: &str, id: Option<VarId>) -> PseudoExpr {
        if let Some(vid) = id.get() {
            PseudoExpr::var_with_id(self.get_renamed_with_id(name, Some(vid)), vid)
        } else {
            self.make_var(name)
        }
    }

    pub(super) fn build_force_chain(mut expr: PseudoExpr, depth: u8) -> PseudoExpr {
        for _ in 0..depth {
            expr = PseudoExpr::Force(PBox::new(expr));
        }
        expr
    }

    pub(super) fn build_delay_chain(mut expr: PseudoExpr, depth: u8) -> PseudoExpr {
        for _ in 0..depth {
            expr = PseudoExpr::Delay(PBox::new(expr));
        }
        expr
    }

    fn cancel_force_delay_chain(expr: PseudoExpr) -> PseudoExpr {
        let mut force_depth = 0u8;
        let mut current = expr;
        while let PseudoExpr::Force(inner) = current {
            force_depth = force_depth.saturating_add(1);
            current = inner.into_inner();
        }

        if force_depth == 0 {
            return current;
        }

        let mut delay_depth = 0u8;
        while let PseudoExpr::Delay(inner) = current {
            delay_depth = delay_depth.saturating_add(1);
            current = inner.into_inner();
        }

        if delay_depth == 0 {
            return Self::build_force_chain(current, force_depth);
        }

        if force_depth > delay_depth {
            Self::build_force_chain(current, force_depth - delay_depth)
        } else if delay_depth > force_depth {
            Self::build_delay_chain(current, delay_depth - force_depth)
        } else {
            current
        }
    }

    fn looks_like_if_alias(&self, expr: &PseudoExpr) -> bool {
        match expr {
            PseudoExpr::Var { name, id, .. } => {
                name == "if"
                    || name == "if_then_else"
                    || self
                        .builtin_alias_for_var(name, id.get())
                        .is_some_and(|v| v == BuiltinId::IfThenElse)
            }
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } => (*name == BuiltinId::IfThenElse) && builtin_args.is_empty(),
            _ => false,
        }
    }

    fn looks_like_choose_list_alias(&self, expr: &PseudoExpr) -> bool {
        match expr {
            PseudoExpr::Var { name, id, .. } => {
                name == "choose_list"
                    || name == "List.fold"
                    || self
                        .builtin_alias_for_var(name, id.get())
                        .is_some_and(|v| v == BuiltinId::ListFold)
            }
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } => (*name == BuiltinId::ListFold) && builtin_args.is_empty(),
            _ => false,
        }
    }

    pub(super) fn partial_if_cond_from_forced_function(
        &self,
        function: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        let PseudoExpr::Force(inner_force) = function else {
            return None;
        };

        match inner_force.as_ref() {
            // let-bound partial: force(force(p)(then, else)), p = force(if_alias)(cond)
            PseudoExpr::Var { name, id, .. } => {
                self.tracked_var(&self.booleans.partial_if_conds, name, id.get())
            }
            // Inline partial: force(force(force(if_alias)(cond))(then, else))
            PseudoExpr::Apply { function, args } if args.len() == 1 => {
                if let PseudoExpr::Force(if_alias) = function.as_ref() {
                    if self.looks_like_if_alias(if_alias.as_ref()) {
                        return Some(args[0].clone());
                    }
                } else if self.looks_like_if_alias(function.as_ref()) {
                    // force1 builtins can already lose the inner force during simplification.
                    return Some(args[0].clone());
                }
                None
            }
            _ => None,
        }
    }

    pub(super) fn partial_choose_list_subject_from_forced_function(
        &self,
        function: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        let PseudoExpr::Force(inner_force) = function else {
            return None;
        };

        match inner_force.as_ref() {
            // let-bound partial: force(force(p)(empty, non_empty)), p = force(choose_list_alias)(xs)
            PseudoExpr::Var { name, id, .. } => {
                self.tracked_var(&self.delays.partial_choose_list_subjects, name, id.get())
            }
            // Inline partial: force(force(force(choose_list_alias)(xs))(empty, non_empty))
            PseudoExpr::Apply { function, args } if args.len() == 1 => {
                if let PseudoExpr::Force(choose_list_alias) = function.as_ref() {
                    if self.looks_like_choose_list_alias(choose_list_alias.as_ref()) {
                        return Some(args[0].clone());
                    }
                } else if self.looks_like_choose_list_alias(function.as_ref()) {
                    return Some(args[0].clone());
                }
                None
            }
            _ => None,
        }
    }

    pub(super) fn maybe_emit_expect(
        &self,
        cond: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> Option<PseudoExpr> {
        if self.safe_mode {
            return None;
        }

        // Lift fail messages into the 3-arg expect! shape; the
        // pretty-printer renders 3-arg as `expect! cond, @"msg"`.
        if Self::is_fail(&else_branch) && !Self::is_fail(&then_branch) {
            let mut args = vec![cond, then_branch];
            if let Some(msg) = Self::fail_message(&else_branch) {
                args.push(PseudoExpr::String(msg.to_string()));
            }
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: args.into(),
            });
        }

        if Self::is_fail(&then_branch) && !Self::is_fail(&else_branch) {
            let msg = Self::fail_message(&then_branch).map(|m| m.to_string());
            let mut args = vec![
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(cond),
                },
                else_branch,
            ];
            if let Some(msg) = msg {
                args.push(PseudoExpr::String(msg));
            }
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: args.into(),
            });
        }

        None
    }

    /// Simplify `expr` from outside the fold machine. Code running inside it
    /// returns a [`Step`] instead, so the machine does the descent.
    pub(crate) fn simplify(&mut self, expr: PseudoExpr) -> PseudoExpr {
        self.fold(expr)
    }
}

// Simple structural post-order cases (`BinOp`, `Constr`, `List`,
// `Tuple`, `Pair`, `Delay`, `Trace`, `FieldAccess`, `IndexAccess`)
// are factored into `simplify_*` helpers that run once the children are
// simplified. A helper takes ownership of the simplified children; the
// two that may re-simplify what they build (`FieldAccess`,
// `IndexAccess`) return a [`Step`].
impl Simplifier {
    pub(super) fn simplify_binop(
        &mut self,
        op: BinaryOp,
        mut left: PseudoExpr,
        mut right: PseudoExpr,
    ) -> PseudoExpr {
        // `&&` / `||` are already short-circuiting in pseudo syntax,
        // so delay wrappers on operands are cosmetic noise.
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            left = Self::unwrap_delay(&left);
            right = Self::unwrap_delay(&right);
        }

        // Boolean constant folding for && and ||.
        if matches!(op, BinaryOp::And) {
            if self.is_true(&left) {
                return right;
            }
            if self.is_true(&right) {
                return left;
            }
            if self.is_false(&left) || self.is_false(&right) {
                return PseudoExpr::Bool(false);
            }
        }
        if matches!(op, BinaryOp::Or) {
            if self.is_false(&left) {
                return right;
            }
            if self.is_false(&right) {
                return left;
            }
            if self.is_true(&left) || self.is_true(&right) {
                return PseudoExpr::Bool(true);
            }
        }

        // Algebraic simplifications.
        if matches!(op, BinaryOp::Mul) {
            if Self::is_neg_one(&right) {
                return PseudoExpr::UnOp {
                    op: UnaryOp::Negate,
                    operand: PBox::new(left),
                };
            }
            if Self::is_neg_one(&left) {
                return PseudoExpr::UnOp {
                    op: UnaryOp::Negate,
                    operand: PBox::new(right),
                };
            }
        }
        if matches!(op, BinaryOp::Add)
            && let PseudoExpr::Int(ref n) = right
            && n < &num_bigint::BigInt::from(0)
        {
            let pos = -n;
            return PseudoExpr::BinOp {
                op: BinaryOp::Sub,
                left: PBox::new(left),
                right: PBox::new(PseudoExpr::Int(pos)),
            };
        }
        if matches!(op, BinaryOp::Sub) {
            if let PseudoExpr::Int(ref n) = right
                && n < &num_bigint::BigInt::from(0)
            {
                let pos = -n;
                return PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(left),
                    right: PBox::new(PseudoExpr::Int(pos)),
                };
            }
            if matches!(left, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(0)) {
                return PseudoExpr::UnOp {
                    op: UnaryOp::Negate,
                    operand: PBox::new(right),
                };
            }
        }

        // Strip matching injective wrappers: f(a) == f(b) → a == b.
        //
        // Only total, injective ENCODERS (`*.to_data`, which wrap a typed
        // value into `Data` and always succeed) are sound to strip:
        // `iData(a) == iData(b)` is `equalsData` over two `I` constructors,
        // exactly `equalsInteger(a, b)`. Partial DECODERS (`Data.un_*` and
        // their `Data.to_*` aliases) `error` when the Data is not the
        // expected shape, while the stripped `x == y` returns `False` —
        // stripping one erases decode-failure semantics and makes the render
        // ACCEPT inputs the bytecode rejects. Keep them wrapped.
        //
        // The listed `*.to_data` spellings are test-minted builtin names;
        // production lowering mints `Data.Int` / `Data.ByteArray` / … for
        // the encoders, so this strip is inert in production — the live
        // encoder strip is `render_prep/fold_data_eq_roundtrip.rs`
        // (both-sides `list_data`, BuiltinId-matched). Keep the allowlist
        // total-encoder-only: a live encoder strip here would add the
        // encoder spellings, never the `Data.to_*` / `Data.un_*` decoders.
        if matches!(op, BinaryOp::Eq | BinaryOp::Neq)
            && let (
                PseudoExpr::BuiltinCall { name: ln, args: la },
                PseudoExpr::BuiltinCall { name: rn, args: ra },
            ) = (&left, &right)
            && ln == rn
            && la.len() == 1
            && ra.len() == 1
        {
            let injective = matches!(
                ln.as_str(),
                "List.to_data"
                    | "Map.to_data"
                    | "Int.to_data"
                    | "ByteArray.to_data"
                    | "String.to_data"
            );
            if injective {
                left = la[0].clone();
                right = ra[0].clone();
            }
        }

        let (op, left, right) = Self::canonicalize_comparison_order(op, left, right);
        let mut result = PseudoExpr::BinOp {
            op,
            left: PBox::new(left),
            right: PBox::new(right),
        };

        if !self.safe_mode && matches!(op, BinaryOp::Eq) {
            result = self.extract_large_data_literal_from_eq(result);
        }

        if matches!(op, BinaryOp::And) {
            if self.safe_mode {
                Self::flatten_and(result)
            } else {
                self.improve_and_chain_readability(result)
            }
        } else {
            result
        }
    }

    pub(super) fn simplify_constr(
        &mut self,
        type_hint: Option<crate::decompile::TypeHintId>,
        tag: usize,
        fields: Vec<PseudoExpr>,
        shape: ConstructorShape,
    ) -> PseudoExpr {
        // Collapse Cons-shaped Constrs to a list literal: Constr<1>(head,
        // tail) with tail a Constr<0>/Constr<1> chain or List → [head, ...].
        // Matching on shape keeps `constr_known(Cons, [h, t])` landing here
        // even when walker folds drop the `Known(Cons)` shape.
        let is_cons_shape = matches!(
            shape,
            ConstructorShape::Known(KnownConstructor::Cons)
                | ConstructorShape::Unknown {
                    tag: 1,
                    arity: 2,
                    ..
                }
        );
        if is_cons_shape
            && let Some((elements, tail)) = list_literal_parts(&PseudoExpr::Constr {
                type_hint: None,
                tag,
                fields: (fields.clone()).into(),
                shape,
            })
            && tail.is_none()
        {
            return PseudoExpr::List {
                elements: elements.into(),
                tail: None,
            };
        }

        PseudoExpr::Constr {
            type_hint,
            tag,
            fields: fields.into(),
            shape,
        }
    }

    pub(super) fn simplify_list(
        &mut self,
        elements: Vec<PseudoExpr>,
        tail: Option<PseudoExpr>,
    ) -> PseudoExpr {
        PseudoExpr::List {
            elements: elements.into(),
            tail: tail.map(PBox::new),
        }
    }

    pub(super) fn simplify_tuple(&mut self, elements: Vec<PseudoExpr>) -> PseudoExpr {
        PseudoExpr::Tuple(elements.into())
    }

    pub(super) fn simplify_pair(&mut self, first: PseudoExpr, second: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Pair(PBox::new(first), PBox::new(second))
    }

    pub(super) fn simplify_delay(&mut self, inner: PseudoExpr) -> PseudoExpr {
        // Syntactic cancellation inside delay.
        let simplified_inner = Self::cancel_force_delay_chain(inner);

        if let Some((name, id, force_depth)) = Self::force_chain_var(&simplified_inner)
            && let Some(delay_depth) =
                self.tracked_var(&self.delays.delayed_value_depths, &name, id.get())
            && delay_depth >= force_depth
        {
            let var = self.make_var_for_observed_ref(&name, id);
            if force_depth == 1 {
                return var;
            }
            return Self::build_force_chain(var, force_depth - 1);
        }

        if !self.safe_mode
            && let PseudoExpr::Lambda { params, body } = &simplified_inner
        {
            let non_underscore: Vec<(usize, &Binder)> = params
                .iter()
                .enumerate()
                .filter(|(_, p)| *p != "_")
                .collect();

            if non_underscore.len() == 1 {
                let (idx, param_name) = non_underscore[0];
                if let PseudoExpr::Apply { function, args } = body.as_ref()
                    && let PseudoExpr::Var { name, .. } = function.as_ref()
                    && name == param_name
                {
                    return PseudoExpr::constr(
                        ConstructorShape::scott_positional(idx, args.len()),
                        (args.clone()).into_vec(),
                    );
                }
            }
        }

        if (Self::is_simple_value(&simplified_inner)
            && !(self.safe_mode && matches!(simplified_inner, PseudoExpr::Error { .. })))
            || (!self.safe_mode && Self::is_non_thunk_value(&simplified_inner))
        {
            simplified_inner
        } else if !self.safe_mode {
            if let PseudoExpr::Var { ref name, ref id } = simplified_inner
                && self
                    .selectors
                    .selector_vars
                    .values()
                    .any(|selector| self.selector_binding_matches_ref(selector, name, *id))
            {
                return simplified_inner;
            }
            PseudoExpr::Delay(PBox::new(simplified_inner))
        } else {
            PseudoExpr::Delay(PBox::new(simplified_inner))
        }
    }

    pub(super) fn simplify_trace(&mut self, message: PseudoExpr, value: PseudoExpr) -> PseudoExpr {
        // Collapse Trace(msg, Error) → Error { message: msg }
        // This preserves fail messages like `fail @"reason"`.
        if matches!(&value, PseudoExpr::Error { .. }) {
            let msg_str = match &message {
                PseudoExpr::String(s) => Some(s.clone()),
                PseudoExpr::ByteArray(b) => String::from_utf8(b.clone()).ok(),
                _ => None,
            };
            if msg_str.is_some() {
                return PseudoExpr::Error { message: msg_str };
            }
        }
        PseudoExpr::Trace {
            message: PBox::new(message),
            value: PBox::new(value),
        }
    }

    pub(super) fn simplify_field_access(
        &mut self,
        simplified_record: PseudoExpr,
        selector: FieldSelector,
    ) -> Step {
        let constr_projection = if selector.is_pair_fst() {
            Some(ConstrPairProjection::Tag)
        } else if selector.is_pair_snd() {
            Some(ConstrPairProjection::Fields)
        } else {
            None
        };

        if let Some(projection) = constr_projection
            && let Some(expr) =
                rewrite_constr_unpack_pair_projection(&simplified_record, None, projection)
        {
            return Step::Done(expr);
        }

        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = simplified_record
            && let Some(subject) =
                self.tracked_var(&self.constructors.constr_unpack_subjects, name, id.get())
            && let Some(projection) = constr_projection
            && let Some(expr) =
                rewrite_constr_unpack_pair_projection(&simplified_record, Some(subject), projection)
        {
            return Step::Done(expr);
        }

        let selector_name = selector.as_pretty_name();
        if matches!(
            &simplified_record,
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::DataConstr
                    && args.len() == 2
                    && (selector_name == "fields" || selector_name == "tag")
        ) {
            let PseudoExpr::BuiltinCall { mut args, .. } = simplified_record else {
                unreachable!("Data.Constr field-access shape checked above");
            };
            if selector_name == "fields" {
                return Step::refold(args.pop().expect("Data.Constr fields arg should exist"));
            }
            let mut args = args.into_iter();
            return Step::refold(args.next().expect("Data.Constr tag arg should exist"));
        }

        if let PseudoExpr::Data(ref data) = simplified_record
            && let PseudoData::Constr(tag, fields) = data.as_ref()
        {
            if selector_name == "fields" {
                let elements = fields
                    .iter()
                    .map(|f| PseudoExpr::Data(Box::new(f.clone())))
                    .collect();
                return Step::refold(PseudoExpr::List {
                    elements,
                    tail: None,
                });
            } else if selector_name == "tag" {
                return Step::Done(PseudoExpr::Int((*tag as i128).into()));
            }
        }

        if matches!(
            &simplified_record,
            PseudoExpr::Constr { .. } if selector_name == "fields" || selector_name == "tag"
        ) {
            let PseudoExpr::Constr { tag, fields, .. } = simplified_record else {
                unreachable!("Constr field-access shape checked above");
            };
            if selector_name == "fields" {
                return Step::Done(PseudoExpr::List {
                    elements: fields,
                    tail: None,
                });
            }
            return Step::Done(PseudoExpr::Int((tag as i128).into()));
        }

        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = simplified_record
            && let Some(stored_value) = (selector_name == "fields" || selector_name == "tag")
                .then(|| self.tracked_var(&self.constructors.data_constr_bindings, name, id.get()))
                .flatten()
        {
            return Step::refold(PseudoExpr::field_access_typed(stored_value, selector));
        }

        if matches!(
            &simplified_record,
            PseudoExpr::BuiltinCall { name, args }
                if (name == "Pair.new" || name == "new_pair")
                    && args.len() == 2
                    && (selector.is_pair_fst() || selector.is_pair_snd())
        ) {
            let PseudoExpr::BuiltinCall { args, .. } = simplified_record else {
                unreachable!("Pair.new field-access shape checked above");
            };
            let mut args = args.into_iter();
            let fst = args.next().expect("Pair.new fst arg should exist");
            let snd = args.next().expect("Pair.new snd arg should exist");
            if selector.is_pair_fst() {
                return Step::Done(fst);
            }
            return Step::Done(snd);
        }

        if matches!(
            &simplified_record,
            PseudoExpr::Pair(_, _) if selector.is_pair_fst() || selector.is_pair_snd()
        ) {
            let PseudoExpr::Pair(fst, snd) = simplified_record else {
                unreachable!("Pair field-access shape checked above");
            };
            if selector.is_pair_fst() {
                return Step::Done(fst.into_inner());
            }
            return Step::Done(snd.into_inner());
        }

        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = simplified_record
        {
            return Step::refold(PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(PseudoExpr::field_access_typed(body.into_inner(), selector)),
            });
        }

        Step::Done(PseudoExpr::field_access_typed(simplified_record, selector))
    }

    pub(super) fn simplify_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if let Some(vid) = self.binding_id(&name, id.get()) {
            if let Some(builtin_name) = self.naming.builtin_aliases.get(vid) {
                return PseudoExpr::BuiltinCall {
                    name: *builtin_name,
                    args: vec![].into(),
                };
            }
            if let Some(renamed) = self.naming.renames.get(vid) {
                return PseudoExpr::Var {
                    name: renamed.clone(),
                    id: Some(vid),
                };
            }
            return PseudoExpr::Var {
                name,
                id: Some(vid),
            };
        }
        if let Some(builtin_name) = self.builtin_alias_for_var(&name, None) {
            return PseudoExpr::BuiltinCall {
                name: builtin_name,
                args: vec![].into(),
            };
        }
        PseudoExpr::Var { name, id }
    }

    pub(super) fn simplify_index_access(
        &mut self,
        simplified_collection: PseudoExpr,
        index: usize,
    ) -> Step {
        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = simplified_collection
        {
            return Step::refold(PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(PseudoExpr::IndexAccess {
                    collection: body,
                    index,
                }),
            });
        }

        if let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = simplified_collection
        {
            let indexed_clauses = clauses
                .into_iter()
                .map(|mut clause| {
                    clause.body = PseudoExpr::IndexAccess {
                        collection: PBox::new(clause.body),
                        index,
                    };
                    clause
                })
                .collect();
            return Step::refold(PseudoExpr::When {
                subject,
                subject_name,
                clauses: indexed_clauses,
            });
        }

        let (current, depth) = list_subject_and_tail_depth(&simplified_collection);
        if let PseudoExpr::Var {
            name: var_name, id, ..
        } = &current
            && let Some((base, offset)) =
                self.tracked_var(&self.constructors.tail_chain_offsets, var_name, id.get())
        {
            return Step::Done(PseudoExpr::IndexAccess {
                collection: PBox::new(base),
                index: index + depth + offset,
            });
        }
        Step::Done(PseudoExpr::IndexAccess {
            collection: PBox::new(current),
            index: index + depth,
        })
    }
}

// Simplifier acts as a `Walker`. Each node is taken by value in
// `enter_owned`:
//
// - Leaves (`Int`, `ByteArray`, `String`, `Bool`, `Unit`, `Error`,
//   `Raw`, `Data`, `HelperSymbol`) walk and are reconstructed by the
//   default leaf `post_*` hooks.
// - The simple structural variants (`BinOp`, `Constr`, `List`, `Tuple`,
//   `Pair`, `Delay`, `Trace`) also walk: the machine folds the children,
//   then the overridden `post_*` hooks run the shared `simplify_*`
//   helpers.
// - Everything else goes to its `simplify_*` helper, which returns a
//   [`Step`]: the children it simplifies — and whatever it rebuilds and
//   simplifies again — are folded by the machine, not by a nested
//   `self.simplify`. The nesting of those nodes is the script's, so a
//   nested call per level would put the whole descent back on the call
//   stack, which cannot grow on `wasm32`.
impl Walker for Simplifier {
    fn enter_owned(&mut self, expr: PseudoExpr) -> Entered {
        // Collapse cons_bytearray chains to a ByteArray literal
        // before any pattern-specific simplification, so collapsed
        // literals never reach `simplify_builtin_call` or child
        // recursion.
        if let Some(bytes) = Self::try_collapse_cons_bytestring(&expr) {
            return Entered::Done(PseudoExpr::ByteArray(bytes));
        }
        let step = match expr {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_)
            | PseudoExpr::BinOp { .. }
            | PseudoExpr::Constr { .. }
            | PseudoExpr::List { .. }
            | PseudoExpr::Tuple(_)
            | PseudoExpr::Pair(_, _)
            | PseudoExpr::Delay(_)
            | PseudoExpr::Trace { .. } => return Entered::Walk(expr),
            PseudoExpr::Var { name, id } => return Entered::Done(self.simplify_var(name, id)),
            PseudoExpr::Force(inner) => self.simplify_force(inner.into_inner()),
            PseudoExpr::Lambda { params, body } => self.simplify_lambda(params, body.into_inner()),
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => self.simplify_if(
                condition.into_inner(),
                then_branch.into_inner(),
                else_branch.into_inner(),
            ),
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => self.simplify_when(subject.into_inner(), subject_name, clauses),
            PseudoExpr::UnOp { op, operand } => self.simplify_unop(op, operand.into_inner()),
            PseudoExpr::BuiltinCall { name, args } => {
                self.simplify_builtin_call(name, args.into_vec())
            }
            PseudoExpr::RecFn { name, params, body } => {
                self.simplify_recfn(name, params, body.into_inner())
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => self.simplify_let_expr(name, id, value.into_inner(), body.into_inner()),
            PseudoExpr::Apply { function, args } => {
                self.simplify_apply_expr(function.into_inner(), args.into_vec())
            }
            PseudoExpr::FieldAccess { record, selector } => {
                Step::fold(record.into_inner(), move |simplifier, record| {
                    simplifier.simplify_field_access(record, selector)
                })
            }
            PseudoExpr::IndexAccess { collection, index } => {
                Step::fold(collection.into_inner(), move |simplifier, collection| {
                    simplifier.simplify_index_access(collection, index)
                })
            }
        };
        self.suspend(step)
    }

    fn resume(&mut self, folded: Vec<PseudoExpr>) -> Entered {
        self.resume_awaiting(folded)
    }

    fn post_binop(&mut self, op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
        self.simplify_binop(op, left, right)
    }

    fn post_constr(
        &mut self,
        type_hint: Option<crate::decompile::TypeHintId>,
        tag: usize,
        fields: Vec<PseudoExpr>,
        shape: ConstructorShape,
    ) -> PseudoExpr {
        self.simplify_constr(type_hint, tag, fields, shape)
    }

    fn post_list(&mut self, elements: Vec<PseudoExpr>, tail: Option<PseudoExpr>) -> PseudoExpr {
        self.simplify_list(elements, tail)
    }

    fn post_tuple(&mut self, elements: Vec<PseudoExpr>) -> PseudoExpr {
        self.simplify_tuple(elements)
    }

    fn post_pair(&mut self, first: PseudoExpr, second: PseudoExpr) -> PseudoExpr {
        self.simplify_pair(first, second)
    }

    fn post_delay(&mut self, inner: PseudoExpr) -> PseudoExpr {
        self.simplify_delay(inner)
    }

    fn post_trace(&mut self, message: PseudoExpr, value: PseudoExpr) -> PseudoExpr {
        self.simplify_trace(message, value)
    }
}

impl Simplifier {
    /// `Apply` simplification: simplify `function` and `args`, then run the
    /// `simplify_apply_match` loop — `Done` / `Resimplify` / `ContinueLoop`
    /// with delay-depth save/restore — on the results.
    pub(super) fn simplify_apply_expr(
        &mut self,
        function: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> Step {
        Self::fold_application(function, args, None)
    }

    /// Simplify `function` and then each of `args`, and hand them to
    /// [`Self::simplify_apply_round`] with the rollback a previous
    /// `ContinueLoop` set up.
    pub(super) fn fold_application(
        function: PseudoExpr,
        args: Vec<PseudoExpr>,
        delay_restore: Option<DelayRestoreList>,
    ) -> Step {
        let mut exprs = Vec::with_capacity(args.len() + 1);
        exprs.push(function);
        exprs.extend(args);
        Step::fold_all(exprs, move |simplifier, mut folded| {
            let args = folded.split_off(1);
            let function = folded.pop().expect("simplified apply function");
            simplifier.simplify_apply_round(function, args, delay_restore)
        })
    }

    /// One round of the `Apply` loop over simplified children. A
    /// `ContinueLoop` re-simplifies the new function and args and comes
    /// back here.
    fn simplify_apply_round(
        &mut self,
        function: PseudoExpr,
        args: Vec<PseudoExpr>,
        delay_restore: Option<DelayRestoreList>,
    ) -> Step {
        // The rollback a previous `ContinueLoop` set up applies BEFORE the
        // next `simplify_apply_match` call.
        if let Some(saved) = delay_restore {
            for (param, param_id, previous) in saved {
                if let Some(prev_depth) = previous {
                    self.delays
                        .delayed_value_depths
                        .insert_binding(param, param_id, prev_depth);
                } else if let Some(vid) = param_id {
                    self.delays.delayed_value_depths.remove(vid);
                }
            }
        }
        match self.simplify_apply_match(function, args) {
            ApplyAction::Done(expr) => Step::Done(expr),
            ApplyAction::Then(step) => step,
            ApplyAction::Resimplify(expr) => Step::refold(expr),
            ApplyAction::ContinueLoop {
                function,
                args,
                delay_restore,
            } => Self::fold_application(function, args, delay_restore),
            ApplyAction::ContinueLoopAfter {
                function,
                args,
                delay_restore,
            } => function.then(self, move |_, function| {
                Self::fold_application(function, args, delay_restore)
            }),
        }
    }
}
