//! Main simplification transform for `PseudoExpr`: the `simplify`
//! entry point, the shared `simplify_*` helpers, and the `Walker`
//! impl that drives them.

use super::apply::ApplyAction;
use super::let_binding::{LetPostResult, LetWalkerPhase};
use super::state::DelayRestoreList;
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
use crate::pseudo::walker::{FoldAction, Walker};

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

    pub(crate) fn simplify(&mut self, expr: PseudoExpr) -> PseudoExpr {
        // A named entry point for helpers recursing via
        // `self.simplify(...)`, kept distinct from the `Walker::fold`
        // machinery; `fold()` carries its own `maybe_grow` stack guard.
        self.fold(expr)
    }
}

// Simple structural post-order cases (`BinOp`, `Constr`, `List`,
// `Tuple`, `Pair`, `Delay`, `Trace`, `FieldAccess`, `IndexAccess`)
// are factored into `simplify_*` helpers that the Walker's `post_*`
// hooks call. A helper takes ownership of already-simplified children
// and returns the final `PseudoExpr`; re-simplification steps call
// `self.simplify(...)` directly.
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
    ) -> PseudoExpr {
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
            return expr;
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
            return expr;
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
                return self.simplify(args.pop().expect("Data.Constr fields arg should exist"));
            }
            let mut args = args.into_iter();
            return self.simplify(args.next().expect("Data.Constr tag arg should exist"));
        }

        if let PseudoExpr::Data(ref data) = simplified_record
            && let PseudoData::Constr(tag, fields) = data.as_ref()
        {
            if selector_name == "fields" {
                let elements = fields
                    .iter()
                    .map(|f| PseudoExpr::Data(Box::new(f.clone())))
                    .collect();
                return self.simplify(PseudoExpr::List {
                    elements,
                    tail: None,
                });
            } else if selector_name == "tag" {
                return PseudoExpr::Int((*tag as i128).into());
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
                return PseudoExpr::List {
                    elements: fields,
                    tail: None,
                };
            }
            return PseudoExpr::Int((tag as i128).into());
        }

        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = simplified_record
            && let Some(stored_value) = (selector_name == "fields" || selector_name == "tag")
                .then(|| self.tracked_var(&self.constructors.data_constr_bindings, name, id.get()))
                .flatten()
        {
            return self.simplify(PseudoExpr::field_access_typed(stored_value, selector));
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
                return fst;
            }
            return snd;
        }

        if matches!(
            &simplified_record,
            PseudoExpr::Pair(_, _) if selector.is_pair_fst() || selector.is_pair_snd()
        ) {
            let PseudoExpr::Pair(fst, snd) = simplified_record else {
                unreachable!("Pair field-access shape checked above");
            };
            if selector.is_pair_fst() {
                return fst.into_inner();
            }
            return snd.into_inner();
        }

        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = simplified_record
        {
            return self.simplify(PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(PseudoExpr::field_access_typed(body.into_inner(), selector)),
            });
        }

        PseudoExpr::field_access_typed(simplified_record, selector)
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
    ) -> PseudoExpr {
        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = simplified_collection
        {
            return self.simplify(PseudoExpr::Let {
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
            return self.simplify(PseudoExpr::When {
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
            return PseudoExpr::IndexAccess {
                collection: PBox::new(base),
                index: index + depth + offset,
            };
        }
        PseudoExpr::IndexAccess {
            collection: PBox::new(current),
            index: index + depth,
        }
    }
}

// Simplifier acts as a `Walker`, dispatching each variant through the
// appropriate hook:
//
// - Leaves (`Int`, `ByteArray`, `String`, `Bool`, `Unit`, `Error`,
//   `Raw`, `Data`, `HelperSymbol`) return `FoldAction::Walk` and are
//   reconstructed by the default leaf `post_*` hooks.
// - The 9 simple structural variants (`BinOp`, `Constr`, `List`,
//   `Tuple`, `Pair`, `Delay`, `Trace`, `FieldAccess`, `IndexAccess`)
//   also `Walk`: the Walker recurses into children, then the
//   overridden `post_*` hooks run the shared `simplify_*` helpers.
// - `Var`, `Force`, `Lambda`, `If`, `When`, `UnOp`, `BuiltinCall`
//   and `RecFn` short-circuit via
//   `FoldAction::Replace(self.simplify_*(...))`; those helpers
//   already recurse through `self.simplify(...)`, so letting the
//   Walker recurse too would double-simplify subtrees.
// - `Let` uses the native `pre_let` / `enter_let` / `post_let` flow.
// - `Apply` walks: the Walker folds `function` and args, then
//   `post_apply` runs the simplify-apply loop iteratively.
impl Walker for Simplifier {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        // Collapse cons_bytearray chains to a ByteArray literal
        // before any pattern-specific simplification, so collapsed
        // literals never reach `simplify_builtin_call` or child
        // recursion.
        if let Some(bytes) = Self::try_collapse_cons_bytestring(expr) {
            return FoldAction::Replace(PseudoExpr::ByteArray(bytes));
        }
        match expr {
            // Leaves — default leaf `post_*` hooks.
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => FoldAction::Walk,
            // Simple structural post-order — the overridden `post_*`
            // hooks below delegate to `simplify_*` helpers.
            PseudoExpr::BinOp { .. }
            | PseudoExpr::Constr { .. }
            | PseudoExpr::List { .. }
            | PseudoExpr::Tuple(_)
            | PseudoExpr::Pair(_, _)
            | PseudoExpr::Delay(_)
            | PseudoExpr::Trace { .. }
            | PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. } => FoldAction::Walk,
            // Helpers already recurse via `self.simplify(...)`
            // on children, so short-circuit Walker recursion.
            PseudoExpr::Var { name, id } => {
                FoldAction::Replace(self.simplify_var(name.clone(), *id))
            }
            PseudoExpr::Force(inner) => FoldAction::Replace(self.simplify_force((**inner).clone())),
            PseudoExpr::Lambda { params, body } => {
                FoldAction::Replace(self.simplify_lambda(params.clone(), (**body).clone()))
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => FoldAction::Replace(self.simplify_if(
                (**condition).clone(),
                (**then_branch).clone(),
                (**else_branch).clone(),
            )),
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => FoldAction::Replace(self.simplify_when(
                (**subject).clone(),
                subject_name.clone(),
                clauses.clone(),
            )),
            PseudoExpr::UnOp { op, operand } => {
                FoldAction::Replace(self.simplify_unop(*op, (**operand).clone()))
            }
            PseudoExpr::BuiltinCall { name, args } => {
                FoldAction::Replace(self.simplify_builtin_call(*name, (args.clone()).into_vec()))
            }
            PseudoExpr::RecFn { name, params, body } => FoldAction::Replace(self.simplify_recfn(
                name.clone(),
                params.clone(),
                (**body).clone(),
            )),
            // `Let` routes through pre_let/enter_let/post_let.
            PseudoExpr::Let { .. } => FoldAction::Walk,
            // `Apply` routes through post_apply; Walker
            // folds `function` + args first, then `post_apply` runs
            // the CPS `simplify_apply_match` loop.
            PseudoExpr::Apply { .. } => FoldAction::Walk,
        }
    }

    fn pre_let(
        &mut self,
        name: &str,
        id: &Option<VarId>,
        value: &PseudoExpr,
        body: &PseudoExpr,
    ) -> FoldAction {
        self.let_depth += 1;
        if self.let_depth > 50 {
            // Depth bail-out: skip pattern matching; let Walker recurse
            // over children and reassemble in `post_let`.
            self.let_walker_states.push(LetWalkerPhase::Bailout);
        } else {
            let state =
                self.simplify_let_pre_process(name.to_string(), id.get(), value, body.clone());
            self.let_walker_states.push(LetWalkerPhase::Normal(state));
        }
        FoldAction::Walk
    }

    fn enter_let(&mut self, name: &str, _id: &Option<VarId>, value: &PseudoExpr) -> String {
        let phase = self
            .let_walker_states
            .pop()
            .expect("enter_let: let_walker_states underflow");
        match phase {
            LetWalkerPhase::Normal(state) => {
                // Feed the folded value through after_value; discard the
                // original body it returns, since the Walker folds the
                // same body from the Let struct next.
                let (after_body_state, _body) = self.simplify_let_after_value(state, value.clone());
                let new_name = after_body_state.name.clone();
                self.let_walker_states
                    .push(LetWalkerPhase::AfterValue(after_body_state));
                new_name
            }
            LetWalkerPhase::Bailout => {
                self.let_walker_states.push(LetWalkerPhase::Bailout);
                name.to_string()
            }
            LetWalkerPhase::AfterValue(_) => {
                panic!("enter_let: unexpected AfterValue phase (pre_let must push Normal/Bailout)")
            }
        }
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let phase = self
            .let_walker_states
            .pop()
            .expect("post_let: let_walker_states underflow");
        match phase {
            LetWalkerPhase::AfterValue(state) => {
                match self.simplify_let_after_body(state, body) {
                    LetPostResult::Done(expr) => {
                        self.let_depth = self.let_depth.saturating_sub(1);
                        expr
                    }
                    LetPostResult::Resimplify(expr) => {
                        // Keep let_depth elevated while re-folding so
                        // nested Lets still count against the guard.
                        let re = self.fold(expr);
                        self.let_depth = self.let_depth.saturating_sub(1);
                        re
                    }
                }
            }
            LetWalkerPhase::Bailout => {
                self.let_depth = self.let_depth.saturating_sub(1);
                PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                }
            }
            LetWalkerPhase::Normal(_) => {
                panic!("post_let: unexpected Normal phase (enter_let must consume it)")
            }
        }
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

    fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
        self.simplify_field_access(record, selector)
    }

    fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
        self.simplify_index_access(collection, index)
    }

    /// `Apply` simplification.
    ///
    /// `pre_expr` returns `FoldAction::Walk` for `Apply`, so the
    /// Walker has already folded `function` and `args`. Run the
    /// `simplify_apply_match` loop — `Done` / `Resimplify` /
    /// `ContinueLoop` with delay-depth save/restore — iteratively
    /// in this one method.
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        let mut current_function = function;
        let mut current_args = args;
        // `pending_restore` carries the delay-depth rollback list set
        // up by a previous `ContinueLoop`; apply it BEFORE the next
        // `simplify_apply_match` call.
        let mut pending_restore: Option<DelayRestoreList> = None;
        loop {
            if let Some(saved) = pending_restore.take() {
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
            match self.simplify_apply_match(current_function, current_args) {
                ApplyAction::Done(expr) => return expr,
                ApplyAction::Resimplify(expr) => return self.fold(expr),
                ApplyAction::ContinueLoop {
                    function,
                    args: new_args,
                    delay_restore,
                } => {
                    // Fold the new function and args through the
                    // full Walker pipeline, then loop back to re-run
                    // `simplify_apply_match` on the simplified
                    // children.
                    current_function = self.fold(function);
                    current_args = new_args.into_iter().map(|a| self.fold(a)).collect();
                    pending_restore = delay_restore;
                }
            }
        }
    }
}
