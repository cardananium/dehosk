use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use std::collections::HashSet;

// Boolean / identity / thunk simplification passes

/// Simplify boolean, identity and thunk shapes.
///
/// 1. Church-bool selectors (`choose_fst`/`choose_snd`) → `Bool` in
///    return-value positions — branch bodies, let values, lambda bodies —
///    and in `&&`/`||`/`!` operands, but never as an Apply argument, where
///    the selector semantics still matter.
/// 2. Bare `Constr<0>`/`Constr<1>` → `True`/`False` when a sibling branch
///    of the same if/when is already bool-typed.
/// 3. `if cond { True } else { False }` → `cond` (inverse form negated).
///
/// 1-3 run to a fixpoint, at most 3 rounds. Then `fn(x_N) { x_N }` is
/// renamed to `fn(x) { x }`, and a thunk `fn(__N) { simple_value }` with
/// `__N` unused collapses to its value.
pub(crate) fn simplify_boolean_and_identity(
    expr: PseudoExpr,
    _env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
) -> PseudoExpr {
    let mut expr = expr;
    // Each pass can expose Constrs the next one folds, so loop to a fixpoint.
    for _ in 0..3 {
        // Pass 1: choose_fst -> True in safe (non-argument) positions.
        let e1 = resolve_boolean_selectors(expr.clone());
        // Pass 2: bare Constr<1> -> False / Constr<0> -> True in boolean context.
        let e2 = resolve_bare_bool_constrs(e1);
        // Pass 2b: if cond { True } else { False } → cond (and inverse).
        let e3 = simplify_if_bool_identity(e2);
        if e3.structural_eq(&expr) {
            expr = e3;
            break;
        }
        expr = e3;
    }
    // Pass 3: normalise identity lambdas.
    let expr = normalise_identity_lambdas(expr);
    // Pass 4: strip trivial thunk lambdas.
    strip_trivial_thunks(expr)
}

// Pass 2b (if-bool identity) ----------------------------------------------

/// Simplify `if cond { True } else { False }` → `cond`
/// and `if cond { False } else { True }` → negated cond.
fn simplify_if_bool_identity(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::ast::{BinaryOp, UnaryOp};
    use crate::pseudo::fold::ExprFolder;

    struct IfBoolIdentity;

    fn selector_condition_bool(expr: &PseudoExpr) -> Option<bool> {
        // Linear Delay/Force chain — plain pointer loop, no worklist needed.
        let mut cur = expr;
        loop {
            match cur {
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => cur = inner,
                other if crate::decompile::simplify::Simplifier::is_fst_selector(other) => {
                    return Some(true);
                }
                other if crate::decompile::simplify::Simplifier::is_snd_selector(other) => {
                    return Some(false);
                }
                _ => return None,
            }
        }
    }

    /// Invert a comparison operator.
    fn invert_cmp(op: BinaryOp) -> Option<BinaryOp> {
        match op {
            BinaryOp::Eq => Some(BinaryOp::Neq),
            BinaryOp::Neq => Some(BinaryOp::Eq),
            BinaryOp::Lt => Some(BinaryOp::Gte),
            BinaryOp::Lte => Some(BinaryOp::Gt),
            BinaryOp::Gt => Some(BinaryOp::Lte),
            BinaryOp::Gte => Some(BinaryOp::Lt),
            _ => None,
        }
    }

    /// Negate a condition: prefer inverting BinOp over wrapping with !.
    fn negate_condition(cond: PseudoExpr) -> PseudoExpr {
        if let PseudoExpr::BinOp { op, left, right } = cond {
            if let Some(inv) = invert_cmp(op) {
                return PseudoExpr::BinOp {
                    op: inv,
                    left,
                    right,
                };
            }
            // Can't invert the op (e.g. And/Or) — wrap with Not.
            return PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::BinOp { op, left, right }),
            };
        }
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(cond),
        }
    }

    impl ExprFolder for IfBoolIdentity {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            if let Some(value) = selector_condition_bool(&condition) {
                return if value { then_branch } else { else_branch };
            }

            // if cond { True } else { False } → cond
            if matches!(&then_branch, PseudoExpr::Bool(true))
                && matches!(&else_branch, PseudoExpr::Bool(false))
            {
                return condition;
            }
            // if cond { False } else { True } → !cond (with operator inversion)
            if matches!(&then_branch, PseudoExpr::Bool(false))
                && matches!(&else_branch, PseudoExpr::Bool(true))
            {
                return negate_condition(condition);
            }
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }
    }

    IfBoolIdentity.fold(expr)
}

// Pass 1 -----------------------------------------------------------------

/// Replace `choose_fst`/`choose_snd` — vars let-bound to a nullary
/// `Constr<0>`/`Constr<1>` or an fst/snd selector — with `Bool(true)` /
/// `Bool(false)`, matching by binder id and by name only when id-less.
/// Rewritten only where a Bool is forced: if/when branch bodies, let
/// values, lambda bodies and `&&`/`||`/`!` operands; an Apply arg keeps
/// its selector semantics.
fn resolve_boolean_selectors(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;
    use crate::pseudo::var_id::VarId;

    #[derive(Default)]
    struct SelectorAliases {
        choose_fst_ids: HashSet<VarId>,
        choose_snd_ids: HashSet<VarId>,
        choose_fst_idless: bool,
        choose_snd_idless: bool,
    }

    impl SelectorAliases {
        fn is_empty(&self) -> bool {
            self.choose_fst_ids.is_empty()
                && self.choose_snd_ids.is_empty()
                && !self.choose_fst_idless
                && !self.choose_snd_idless
        }

        fn add_choose_fst(&mut self, id: Option<VarId>) {
            match id.and_then(|v| v.get()) {
                Some(v) => {
                    self.choose_fst_ids.insert(v);
                }
                None => {
                    self.choose_fst_idless = true;
                }
            }
        }

        fn add_choose_snd(&mut self, id: Option<VarId>) {
            match id.and_then(|v| v.get()) {
                Some(v) => {
                    self.choose_snd_ids.insert(v);
                }
                None => {
                    self.choose_snd_idless = true;
                }
            }
        }

        fn matches_choose_fst(&self, name: &str, id: Option<VarId>) -> bool {
            match id.and_then(|v| v.get()) {
                Some(v) => self.choose_fst_ids.contains(&v),
                None => self.choose_fst_idless && name == "choose_fst",
            }
        }

        fn matches_choose_snd(&self, name: &str, id: Option<VarId>) -> bool {
            match id.and_then(|v| v.get()) {
                Some(v) => self.choose_snd_ids.contains(&v),
                None => self.choose_snd_idless && name == "choose_snd",
            }
        }
    }

    let aliases = collect_selector_aliases(&expr);
    if aliases.is_empty() {
        return expr;
    }

    fn is_selector_binding_value(expr: &PseudoExpr, expect_true: bool) -> bool {
        match expr {
            PseudoExpr::Constr { tag, fields, .. } => {
                let expected_tag = usize::from(!expect_true);
                *tag == expected_tag && fields.is_empty()
            }
            other if expect_true => crate::decompile::simplify::Simplifier::is_fst_selector(other),
            other => crate::decompile::simplify::Simplifier::is_snd_selector(other),
        }
    }

    fn collect_selector_aliases(expr: &PseudoExpr) -> SelectorAliases {
        let mut aliases = SelectorAliases::default();
        collect_selector_aliases_into(expr, &mut aliases);
        aliases
    }

    fn collect_selector_aliases_into(expr: &PseudoExpr, aliases: &mut SelectorAliases) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            match cur {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    if name == "choose_fst" && is_selector_binding_value(value, true) {
                        aliases.add_choose_fst(*id);
                    } else if name == "choose_snd" && is_selector_binding_value(value, false) {
                        aliases.add_choose_snd(*id);
                    }
                    pending.push(body);
                    pending.push(value);
                }
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                    pending.push(condition);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for clause in clauses.iter().rev() {
                        pending.push(&clause.body);
                        if let Some(guard) = &clause.guard {
                            pending.push(guard);
                        }
                    }
                    pending.push(subject);
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                }
                | PseudoExpr::Delay(operand)
                | PseudoExpr::Force(operand) => {
                    pending.push(operand);
                }
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        pending.push(item);
                    }
                }
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
    }

    fn rewrite_selector_alias(e: PseudoExpr, aliases: &SelectorAliases) -> PseudoExpr {
        match &e {
            PseudoExpr::Var { name, id, .. } if aliases.matches_choose_fst(name, *id) => {
                PseudoExpr::Bool(true)
            }
            PseudoExpr::Var { name, id, .. } if aliases.matches_choose_snd(name, *id) => {
                PseudoExpr::Bool(false)
            }
            _ => e,
        }
    }

    /// An operand of `&&`/`||`/`!` is a Bool slot, so a church-bool selector
    /// there resolves: `choose_fst` → `True`, `choose_snd` → `False`. Looks
    /// through a `Trace`/`Delay` wrapper, so the traced value of a soft-assert
    /// `cond || trace @"msg": choose_snd` is rewritten too. In a HOF arg, Pair
    /// element or when arm the same const keeps its selector semantics.
    fn rewrite_bool_operand(e: PseudoExpr, aliases: &SelectorAliases) -> PseudoExpr {
        enum Wrapper {
            Trace(PBox), // the trace message, kept as-is
            Delay,
        }

        let mut wrappers = Vec::new();
        let mut current = e;
        loop {
            match current {
                PseudoExpr::Trace { message, value } => {
                    wrappers.push(Wrapper::Trace(message));
                    current = value.into_inner();
                }
                PseudoExpr::Delay(inner) => {
                    wrappers.push(Wrapper::Delay);
                    current = inner.into_inner();
                }
                other => {
                    current = other;
                    break;
                }
            }
        }

        let mut result = if matches!(current, PseudoExpr::Var { .. }) {
            rewrite_selector_alias(current, aliases)
        } else {
            current
        };
        for wrapper in wrappers.into_iter().rev() {
            result = match wrapper {
                Wrapper::Trace(message) => PseudoExpr::Trace {
                    message,
                    value: PBox::new(result),
                },
                Wrapper::Delay => PseudoExpr::Delay(PBox::new(result)),
            };
        }
        result
    }

    struct BoolSelector {
        aliases: SelectorAliases,
    }

    impl ExprFolder for BoolSelector {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            let then_branch = rewrite_selector_alias(then_branch, &self.aliases);
            let else_branch = rewrite_selector_alias(else_branch, &self.aliases);
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }

        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<crate::pseudo::ast::WhenClause>,
        ) -> PseudoExpr {
            let clauses = clauses
                .into_iter()
                .map(|mut c| {
                    c.body = rewrite_selector_alias(c.body, &self.aliases);
                    c
                })
                .collect();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }

        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,

            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            let value = rewrite_selector_alias(value, &self.aliases);
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }

        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            let body = rewrite_selector_alias(body, &self.aliases);
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }

        fn post_binop(
            &mut self,
            op: crate::pseudo::ast::BinaryOp,
            left: PseudoExpr,
            right: PseudoExpr,
        ) -> PseudoExpr {
            use crate::pseudo::ast::BinaryOp;
            let (left, right) = if matches!(op, BinaryOp::And | BinaryOp::Or) {
                (
                    rewrite_bool_operand(left, &self.aliases),
                    rewrite_bool_operand(right, &self.aliases),
                )
            } else {
                (left, right)
            };
            PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            }
        }

        fn post_unop(
            &mut self,
            op: crate::pseudo::ast::UnaryOp,
            operand: PseudoExpr,
        ) -> PseudoExpr {
            let operand = if matches!(op, crate::pseudo::ast::UnaryOp::Not) {
                rewrite_bool_operand(operand, &self.aliases)
            } else {
                operand
            };
            PseudoExpr::UnOp {
                op,
                operand: PBox::new(operand),
            }
        }
    }

    BoolSelector { aliases }.fold(expr)
}

// Pass 2 -----------------------------------------------------------------

/// In if/when expressions where one branch is `Bool(true)` (or bare Constr<0>)
/// and the sibling is bare `Constr<1>`, convert the pair to `True`/`False`.
fn resolve_bare_bool_constrs(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    fn is_bare_constr(e: &PseudoExpr, tag: usize) -> bool {
        match e {
            PseudoExpr::Constr {
                tag: t,
                fields,
                shape,
                ..
            } if *t == tag && fields.is_empty() => match shape {
                ConstructorShape::Unknown { .. } => true,
                ConstructorShape::Known(KnownConstructor::False) => tag == 0,
                ConstructorShape::Known(KnownConstructor::True) => tag == 1,
                ConstructorShape::Known(_) => false,
            },
            _ => false,
        }
    }

    fn is_bool_true_context(e: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![e];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Bool(true) => return true,
                _ if is_bare_constr(current, 0) => return true,
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Delay(inner) => pending.push(inner),
                _ => {}
            }
        }
        false
    }

    fn is_bool_false_context(e: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![e];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Bool(false) => return true,
                _ if is_bare_constr(current, 1) => return true,
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Delay(inner) => pending.push(inner),
                _ => {}
            }
        }
        false
    }

    /// True when every leaf is a Bool: literals, bare `Constr<0/1>`,
    /// comparisons, `&&`/`||`/`!`, and both branches of an `If` — looking
    /// through `Trace` and `Delay`. A bare `Var` does not count.
    fn evaluates_to_bool(e: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![e];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Bool(_) => {}
                _ if is_bare_constr(current, 0) || is_bare_constr(current, 1) => {}
                PseudoExpr::Var { .. } => return false,
                PseudoExpr::BinOp { op, left, right } => match op {
                    crate::pseudo::ast::BinaryOp::Eq
                    | crate::pseudo::ast::BinaryOp::Neq
                    | crate::pseudo::ast::BinaryOp::Lt
                    | crate::pseudo::ast::BinaryOp::Lte
                    | crate::pseudo::ast::BinaryOp::Gt
                    | crate::pseudo::ast::BinaryOp::Gte => {}
                    crate::pseudo::ast::BinaryOp::And | crate::pseudo::ast::BinaryOp::Or => {
                        pending.push(left);
                        pending.push(right);
                    }
                    _ => return false,
                },
                PseudoExpr::UnOp {
                    op: crate::pseudo::ast::UnaryOp::Not,
                    operand,
                } => pending.push(operand),
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                // Trace wraps a value — the traced value determines the type.
                PseudoExpr::Trace { value, .. } => pending.push(value),
                // Delay wraps a value — look through it.
                PseudoExpr::Delay(inner) => pending.push(inner),
                _ => return false,
            }
        }
        true
    }

    /// Detect a nullary `Constr` whose tag is outside the church-bool set
    /// {0, 1} anywhere in an if/when branch tree (through the same shapes
    /// `evaluates_to_bool` looks through). Such a variant belongs to a
    /// genuine 3+-constructor sum — `Ordering::Greater` (`Constr<2>`) out of
    /// `if a<b {Constr<0>} else if a==b {Constr<1>} else {Constr<2>}` — so
    /// the surrounding if/when is not a boolean context: its `Constr<0>` /
    /// `Constr<1>` siblings are `Less`/`Equal`, not `True`/`False`. Folding
    /// them to `Bool` would leave the producer returning `True`/`False`
    /// while the consumer still dispatches on tags 0/1/2.
    /// `can_short_circuit_with_boolean` vetoes the same shape on the
    /// `&&`/`||` collapse path.
    fn has_non_bool_nullary_constr(e: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![e];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Constr { tag, fields, .. }
                    if fields.is_empty() && *tag != 0 && *tag != 1 =>
                {
                    return true;
                }
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::When { clauses, .. } => {
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
                _ => {}
            }
        }
        false
    }

    /// True when one branch is True-like and another False-like, or when a
    /// branch evaluates to Bool and a sibling is a bool-true/bool-false
    /// context.
    fn has_boolean_context(branches: &[&PseudoExpr]) -> bool {
        // Fail-closed: a nullary variant with tag ∉ {0,1} means a 3+-variant
        // sum dispatch, not a boolean context — keep the tags faithful.
        if branches.iter().any(|b| has_non_bool_nullary_constr(b)) {
            return false;
        }
        let has_true = branches.iter().any(|b| is_bool_true_context(b));
        let has_false = branches.iter().any(|b| is_bool_false_context(b));
        if has_true && has_false {
            return true;
        }
        let has_bool_eval = branches.iter().any(|b| evaluates_to_bool(b));
        let has_bool_context_sibling = branches
            .iter()
            .any(|b| is_bool_true_context(b) || is_bool_false_context(b));
        has_bool_eval && has_bool_context_sibling
    }

    fn to_bool(e: PseudoExpr) -> PseudoExpr {
        enum Wrapper {
            Trace(PBox), // the trace message, kept as-is
            Delay,
        }

        let mut wrappers = Vec::new();
        let mut current = e;
        loop {
            if is_bare_constr(&current, 0) || matches!(&current, PseudoExpr::Bool(true)) {
                current = PseudoExpr::Bool(true);
                break;
            }
            if is_bare_constr(&current, 1) || matches!(&current, PseudoExpr::Bool(false)) {
                current = PseudoExpr::Bool(false);
                break;
            }
            match current {
                // Trace wrapping a bool — convert the inner value.
                PseudoExpr::Trace { message, value } => {
                    wrappers.push(Wrapper::Trace(message));
                    current = value.into_inner();
                }
                // Delay wrapping a bool — convert the inner value.
                PseudoExpr::Delay(inner) => {
                    wrappers.push(Wrapper::Delay);
                    current = inner.into_inner();
                }
                other => {
                    current = other;
                    break;
                }
            }
        }

        let mut result = current;
        for wrapper in wrappers.into_iter().rev() {
            result = match wrapper {
                Wrapper::Trace(message) => PseudoExpr::Trace {
                    message,
                    value: PBox::new(result),
                },
                Wrapper::Delay => PseudoExpr::Delay(PBox::new(result)),
            };
        }
        result
    }

    struct BoolConstrResolver;

    impl ExprFolder for BoolConstrResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            if has_boolean_context(&[&then_branch, &else_branch]) {
                PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(to_bool(then_branch)),
                    else_branch: PBox::new(to_bool(else_branch)),
                }
            } else {
                PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                }
            }
        }

        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<crate::pseudo::ast::WhenClause>,
        ) -> PseudoExpr {
            let branch_bodies: Vec<&PseudoExpr> = clauses.iter().map(|c| &c.body).collect();
            if has_boolean_context(&branch_bodies) {
                let clauses = clauses
                    .into_iter()
                    .map(|mut c| {
                        c.body = to_bool(c.body);
                        c
                    })
                    .collect();
                PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                }
            } else {
                PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                }
            }
        }
    }

    BoolConstrResolver.fold(expr)
}

// Pass 3 -----------------------------------------------------------------

/// Normalise identity lambdas: `fn(x_N) { x_N }` -> `fn(x) { x }`.
fn normalise_identity_lambdas(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    let mut used_names = HashSet::new();
    crate::decompile::simplify::Simplifier::collect_var_names(&expr, &mut used_names);

    struct IdentityNorm {
        used_names: HashSet<String>,
    }

    impl IdentityNorm {
        fn fresh_identity_name(&mut self, current: &Binder) -> String {
            if current.as_str() == "x" {
                return "x".to_string();
            }
            if self.used_names.insert("x".to_string()) {
                return "x".to_string();
            }
            for index in 1.. {
                let candidate = format!("x_{index}");
                if self.used_names.insert(candidate.clone()) {
                    return candidate;
                }
            }
            unreachable!("unbounded identity-name allocation loop must return")
        }
    }

    impl ExprFolder for IdentityNorm {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            if params.len() == 1
                && let PseudoExpr::Var { ref id, .. } = body
                && *id == Some(params[0].var_id())
            {
                let fresh_name = self.fresh_identity_name(&params[0]);
                let param = params[0].renamed(fresh_name);
                return PseudoExpr::Lambda {
                    params: vec![param.clone()],
                    body: PBox::new(PseudoExpr::var_with_id(param.as_str(), param.id)),
                };
            }
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
    }

    IdentityNorm { used_names }.fold(expr)
}

// Pass 4 -----------------------------------------------------------------

/// Strip trivial thunk lambdas: `fn(__N) { simple_value }` -> `simple_value`
/// where `__N` is unused and the body is a Var, Bool, Int, Unit or fieldless
/// Constr.
fn strip_trivial_thunks(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    fn is_simple_value(e: &PseudoExpr) -> bool {
        match e {
            PseudoExpr::Var { .. }
            | PseudoExpr::Bool(_)
            | PseudoExpr::Int(_)
            | PseudoExpr::Unit => true,
            PseudoExpr::Constr { fields, .. } => fields.is_empty(),
            _ => false,
        }
    }

    struct ThunkStripper;

    impl ExprFolder for ThunkStripper {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            if params.len() == 1 && params[0].starts_with("__") && is_simple_value(&body) {
                // Verify the param is truly unused in the body.
                if let PseudoExpr::Var { ref id, .. } = body
                    && *id == Some(params[0].var_id())
                {
                    // The body IS the param — not a thunk, it's identity.
                    return PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    };
                }
                // Param unused, body is simple — strip the thunk.
                return body;
            }
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
    }

    ThunkStripper.fold(expr)
}

#[cfg(test)]
mod tests;
