use super::*;
use crate::pseudo::nameless::NamelessExpr;
use crate::pseudo::var_id::VarId;

struct Identity;
impl NamelessFolder for Identity {}

#[test]
fn identity_folder_preserves_let() {
    let id = VarId::fresh_binding();
    let expr = NamelessExpr::Let {
        binder: id,
        value: Box::new(NamelessExpr::Int(num_bigint::BigInt::from(42))),
        body: Box::new(NamelessExpr::Var(id)),
    };
    let mut f = Identity;
    let result = f.fold(expr.clone());
    // `structural_eq` is PseudoExpr-only; a Debug compare suffices here.
    assert_eq!(format!("{result:?}"), format!("{expr:?}"));
}

struct DelayStripper;
impl NamelessFolder for DelayStripper {
    fn post_delay(&mut self, inner: NamelessExpr) -> NamelessExpr {
        // Always strip — for testing the override hook.
        inner
    }
}

#[test]
fn override_post_delay_strips_delays() {
    let expr = NamelessExpr::Delay(Box::new(NamelessExpr::Delay(Box::new(NamelessExpr::Int(
        num_bigint::BigInt::from(7),
    )))));
    let result = DelayStripper.fold(expr);
    assert!(matches!(result, NamelessExpr::Int(_)));
}

struct ScopeStackTracker {
    events: Vec<&'static str>,
}
impl NamelessFolder for ScopeStackTracker {
    fn enter_lambda(&mut self, _: &[VarId]) {
        self.events.push("enter_lambda");
    }
    fn exit_lambda(&mut self, _: &[VarId]) {
        self.events.push("exit_lambda");
    }
    fn enter_let(&mut self, _: VarId, _: &NamelessExpr) {
        self.events.push("enter_let");
    }
    fn exit_let(&mut self, _: VarId) {
        self.events.push("exit_let");
    }
}

#[test]
fn lifecycle_hooks_fire_in_correct_order() {
    let lam_param = VarId::fresh_binding();
    let let_id = VarId::fresh_binding();
    // λx. (let y = x in y)
    let expr = NamelessExpr::Lambda {
        params: vec![lam_param],
        body: Box::new(NamelessExpr::Let {
            binder: let_id,
            value: Box::new(NamelessExpr::Var(lam_param)),
            body: Box::new(NamelessExpr::Var(let_id)),
        }),
    };
    let mut tracker = ScopeStackTracker { events: vec![] };
    tracker.fold(expr);
    assert_eq!(
        tracker.events,
        vec![
            "enter_lambda",
            "enter_let", // value folded first, THEN enter_let
            "exit_let",
            "exit_lambda",
        ]
    );
}

struct PreReplaceUnit;
impl NamelessFolder for PreReplaceUnit {
    fn pre_expr(&mut self, expr: &NamelessExpr) -> NamelessFoldAction {
        if matches!(expr, NamelessExpr::Int(_)) {
            NamelessFoldAction::Replace(NamelessExpr::Unit)
        } else {
            NamelessFoldAction::Walk
        }
    }
}

struct VarCounter {
    count: usize,
}
impl NamelessVisitor for VarCounter {
    fn visit_var(&mut self, _: VarId) {
        self.count += 1;
    }
}

#[test]
fn visitor_counts_var_uses() {
    let id = VarId::fresh_binding();
    // Tuple([Var(id), Var(id), Int(0)])
    let expr = NamelessExpr::Tuple(vec![
        NamelessExpr::Var(id),
        NamelessExpr::Var(id),
        NamelessExpr::Int(num_bigint::BigInt::from(0)),
    ]);
    let mut counter = VarCounter { count: 0 };
    counter.walk(&expr);
    assert_eq!(counter.count, 2);
}

struct ScopeRecorder {
    events: Vec<&'static str>,
}
impl NamelessVisitor for ScopeRecorder {
    fn enter_lambda(&mut self, _: &[VarId]) {
        self.events.push("enter_lambda");
    }
    fn exit_lambda(&mut self, _: &[VarId]) {
        self.events.push("exit_lambda");
    }
    fn enter_let(&mut self, _: VarId, _: &NamelessExpr) {
        self.events.push("enter_let");
    }
    fn exit_let(&mut self, _: VarId) {
        self.events.push("exit_let");
    }
}

struct VarCounterSkippingLambdas {
    count: usize,
}
impl NamelessVisitor for VarCounterSkippingLambdas {
    fn visit_expr(&mut self, expr: &NamelessExpr) -> VisitAction {
        if matches!(expr, NamelessExpr::Lambda { .. }) {
            VisitAction::Skip
        } else {
            VisitAction::Walk
        }
    }
    fn visit_var(&mut self, _: VarId) {
        self.count += 1;
    }
}

#[test]
fn visit_action_skip_does_not_recurse_into_lambda_body() {
    let id = VarId::fresh_binding();
    // (Var(id), λ_. Var(id)) — the Var inside the lambda body
    // should NOT be counted because the lambda subtree is skipped.
    let expr = NamelessExpr::Tuple(vec![
        NamelessExpr::Var(id),
        NamelessExpr::Lambda {
            params: vec![VarId::fresh_binding()],
            body: Box::new(NamelessExpr::Var(id)),
        },
    ]);
    let mut counter = VarCounterSkippingLambdas { count: 0 };
    counter.walk(&expr);
    assert_eq!(counter.count, 1);
}

#[test]
fn visitor_lifecycle_hooks_match_folder_ordering() {
    // λx. (let y = x in y)
    let lam_param = VarId::fresh_binding();
    let let_id = VarId::fresh_binding();
    let expr = NamelessExpr::Lambda {
        params: vec![lam_param],
        body: Box::new(NamelessExpr::Let {
            binder: let_id,
            value: Box::new(NamelessExpr::Var(lam_param)),
            body: Box::new(NamelessExpr::Var(let_id)),
        }),
    };
    let mut recorder = ScopeRecorder { events: vec![] };
    recorder.walk(&expr);
    assert_eq!(
        recorder.events,
        vec![
            "enter_lambda",
            "enter_let", // value walked first, THEN enter_let
            "exit_let",
            "exit_lambda",
        ]
    );
}

#[test]
fn pre_expr_replace_short_circuits_recursion() {
    // Tuple([Int(1), Int(2)]) → Tuple([Unit, Unit])
    let expr = NamelessExpr::Tuple(vec![
        NamelessExpr::Int(num_bigint::BigInt::from(1)),
        NamelessExpr::Int(num_bigint::BigInt::from(2)),
    ]);
    let result = PreReplaceUnit.fold(expr);
    let NamelessExpr::Tuple(items) = result else {
        panic!("expected Tuple");
    };
    assert!(items.iter().all(|e| matches!(e, NamelessExpr::Unit)));
}
