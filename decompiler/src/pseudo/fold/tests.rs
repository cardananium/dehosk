use super::*;

/// Test: identity folder produces the same expression.
#[test]
fn test_identity_fold() {
    struct Identity;
    impl ExprFolder for Identity {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
    }

    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(42),
        PseudoExpr::if_then_else(
            PseudoExpr::bool(true),
            PseudoExpr::var("x"),
            PseudoExpr::int(0),
        ),
    );

    let mut folder = Identity;
    let result = folder.fold(expr.clone());
    assert_eq!(result, expr);
}

/// Test: visitor counts variable usages.
#[test]
fn test_var_counting_visitor() {
    struct VarCounter {
        count: usize,
        target: String,
    }
    impl ExprVisitor for VarCounter {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if name == self.target {
                self.count += 1;
            }
        }
    }

    let expr = PseudoExpr::binop(
        BinaryOp::Add,
        PseudoExpr::var("x"),
        PseudoExpr::binop(BinaryOp::Mul, PseudoExpr::var("x"), PseudoExpr::var("y")),
    );

    let mut counter = VarCounter {
        count: 0,
        target: "x".to_string(),
    };
    counter.walk(&expr);
    assert_eq!(counter.count, 2);
}

#[test]
fn test_visitor_let_value_post_runs_between_value_and_body() {
    struct HookOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for HookOrder {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "value" => "value",
                "body" => "body",
                _ => "other",
            });
        }

        fn visit_let_value_post(&mut self, _name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            self.events.push("between");
        }
    }

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("value")),
        body: PBox::new(PseudoExpr::var("body")),
    };

    let mut visitor = HookOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["value", "between", "body"]);
}

#[test]
fn test_visitor_when_hook_runs_before_clause_walks() {
    struct WhenOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for WhenOrder {
        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            _subject_name: Option<&Binder>,
            _clauses: &[WhenClause],
        ) {
            self.events.push("when");
        }

        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "subject" => "subject",
                "guard" => "guard",
                "body" => "body",
                _ => "var",
            });
        }
    }

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: Some(PseudoExpr::var("guard")),
            body: PseudoExpr::var("body"),
        }],
    };

    let mut visitor = WhenOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["when", "subject", "guard", "body"]);
}

#[test]
fn test_visitor_when_clause_hook_runs_after_literal_before_guard_and_body() {
    struct WhenClauseOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for WhenClauseOrder {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "subject" => "subject",
                "lit" => "lit",
                "guard" => "guard",
                "body" => "body",
                _ => "var",
            });
        }

        fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, _clause: &WhenClause) {
            self.events.push("clause_pre");
        }

        fn visit_when_clause_post(&mut self, _subject_name: Option<&Binder>, _clause: &WhenClause) {
            self.events.push("clause_post");
        }
    }

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::var("lit")),
            guard: Some(PseudoExpr::var("guard")),
            body: PseudoExpr::var("body"),
        }],
    };

    let mut visitor = WhenClauseOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(
        visitor.events,
        vec![
            "subject",
            "lit",
            "clause_pre",
            "guard",
            "body",
            "clause_post"
        ]
    );
}

#[test]
fn test_visitor_let_hook_runs_before_value_and_body() {
    struct LetOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for LetOrder {
        fn visit_let(
            &mut self,
            _name: &str,
            _id: &Option<VarId>,
            _value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            self.events.push("let");
        }

        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "value" => "value",
                "body" => "body",
                _ => "var",
            });
        }
    }

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("value")),
        body: PBox::new(PseudoExpr::var("body")),
    };

    let mut visitor = LetOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["let", "value", "body"]);
}

#[test]
fn test_visitor_recfn_hook_runs_before_body() {
    struct RecfnOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for RecfnOrder {
        fn visit_recfn(&mut self, _name: &Binder, _params: &[Binder], _body: &PseudoExpr) {
            self.events.push("recfn");
        }

        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "body" => "body",
                _ => "var",
            });
        }
    }

    let expr = PseudoExpr::RecFn {
        name: "loop".into(),
        params: vec!["x".into()],
        body: PBox::new(PseudoExpr::var("body")),
    };

    let mut visitor = RecfnOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["recfn", "body"]);
}

#[test]
fn test_visitor_apply_hook_runs_before_function_and_args() {
    struct ApplyOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for ApplyOrder {
        fn visit_apply(
            &mut self,
            _expr: &PseudoExpr,
            _function: &PseudoExpr,
            _args: &[PseudoExpr],
        ) {
            self.events.push("apply");
        }

        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "f" => "function",
                "x" => "arg_x",
                "y" => "arg_y",
                _ => "var",
            });
        }
    }

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::var("x"), PseudoExpr::var("y")].into(),
    };

    let mut visitor = ApplyOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["apply", "function", "arg_x", "arg_y"]);
}

#[test]
fn test_visitor_force_hook_runs_before_inner_walk() {
    struct ForceOrder {
        events: Vec<&'static str>,
    }

    impl ExprVisitor for ForceOrder {
        fn visit_force(&mut self, _inner: &PseudoExpr) {
            self.events.push("force");
        }

        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.events.push(match name {
                "x" => "var:x",
                _ => "var",
            });
        }
    }

    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::var("x")));

    let mut visitor = ForceOrder { events: Vec::new() };
    visitor.walk(&expr);
    assert_eq!(visitor.events, vec!["force", "var:x"]);
}

/// Test: folder that doubles all integer literals.
#[test]
fn test_transform_folder() {
    struct DoubleInts;
    impl ExprFolder for DoubleInts {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_int(&mut self, n: num_bigint::BigInt) -> PseudoExpr {
            PseudoExpr::Int(n * 2)
        }
    }

    let expr = PseudoExpr::binop(BinaryOp::Add, PseudoExpr::int(3), PseudoExpr::int(5));

    let mut folder = DoubleInts;
    let result = folder.fold(expr);

    match result {
        PseudoExpr::BinOp { left, right, .. } => {
            assert_eq!(*left, PseudoExpr::int(6));
            assert_eq!(*right, PseudoExpr::int(10));
        }
        _ => panic!("Expected BinOp"),
    }
}

/// Test: pre_expr can short-circuit recursion.
#[test]
fn test_pre_expr_replace() {
    struct ReplaceVars;
    impl ExprFolder for ReplaceVars {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if let PseudoExpr::Var { name, .. } = expr {
                if name == "old" {
                    return FoldAction::Replace(PseudoExpr::var("new"));
                }
            }
            FoldAction::Walk
        }
    }

    let expr = PseudoExpr::apply(
        PseudoExpr::var("old"),
        vec![PseudoExpr::var("old"), PseudoExpr::var("keep")],
    );

    let mut folder = ReplaceVars;
    let result = folder.fold(expr);

    if let PseudoExpr::Apply { function, args } = result {
        assert_eq!(*function, PseudoExpr::var("new"));
        assert_eq!(args[0], PseudoExpr::var("new"));
        assert_eq!(args[1], PseudoExpr::var("keep"));
    } else {
        panic!("Expected Apply");
    }
}

#[test]
fn test_post_expr_runs_after_children_are_folded() {
    struct DelayStripper;

    impl ExprFolder for DelayStripper {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_int(&mut self, n: num_bigint::BigInt) -> PseudoExpr {
            PseudoExpr::Int(n + 1)
        }

        fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
            match expr {
                PseudoExpr::Delay(inner) => inner.into_inner(),
                other => other,
            }
        }
    }

    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::int(41)));

    let mut folder = DelayStripper;
    let result = folder.fold(expr);

    assert_eq!(result, PseudoExpr::int(42));
}

#[test]
fn pre_let_replace_short_circuits_value_body_and_scope_hooks() {
    // `pre_let::Replace` must short-circuit value fold, body fold,
    // enter_let/exit_let, and post_let for that node.
    struct ReplaceLet {
        pre_let_calls: usize,
        enter_let_calls: usize,
        exit_let_calls: usize,
        post_let_calls: usize,
        post_int_calls: usize,
    }
    impl ExprFolder for ReplaceLet {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_let(
            &mut self,
            _name: &str,
            _id: &Option<VarId>,
            _value: &PseudoExpr,
            _body: &PseudoExpr,
        ) -> FoldAction {
            self.pre_let_calls += 1;
            FoldAction::Replace(PseudoExpr::int(99))
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.enter_let_calls += 1;
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.exit_let_calls += 1;
        }

        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            self.post_let_calls += 1;
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }

        fn post_int(&mut self, n: num_bigint::BigInt) -> PseudoExpr {
            self.post_int_calls += 1;
            PseudoExpr::Int(n)
        }
    }

    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::int(2)),
    );

    let mut w = ReplaceLet {
        pre_let_calls: 0,
        enter_let_calls: 0,
        exit_let_calls: 0,
        post_let_calls: 0,
        post_int_calls: 0,
    };
    let result = w.fold(expr);

    assert_eq!(result, PseudoExpr::int(99));
    assert_eq!(w.pre_let_calls, 1);
    assert_eq!(w.enter_let_calls, 0, "Replace must skip enter_let");
    assert_eq!(w.exit_let_calls, 0, "Replace must skip exit_let");
    assert_eq!(w.post_let_calls, 0, "Replace must skip post_let");
    assert_eq!(
        w.post_int_calls, 0,
        "Replace must skip recursion into value/body children"
    );
}

#[test]
fn pre_let_walk_runs_full_let_lifecycle() {
    // `pre_let::Walk` (default) must preserve the value →
    // enter_let → body → exit_let → post_let flow, so scope-aware
    // passes see the same hook sequence.
    struct Tracer {
        events: Vec<String>,
    }
    impl ExprFolder for Tracer {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_let(
            &mut self,
            name: &str,
            _id: &Option<VarId>,
            _value: &PseudoExpr,
            _body: &PseudoExpr,
        ) -> FoldAction {
            self.events.push(format!("pre_let:{name}"));
            FoldAction::Walk
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.events.push(format!("enter_let:{name}"));
            name.to_string()
        }

        fn exit_let(&mut self, name: &str) {
            self.events.push(format!("exit_let:{name}"));
        }

        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            self.events.push(format!("post_let:{name}"));
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    let expr = PseudoExpr::let_bind("a", PseudoExpr::int(1), PseudoExpr::var("a"));

    let mut w = Tracer { events: Vec::new() };
    w.fold(expr);

    assert_eq!(
        w.events,
        vec![
            "pre_let:a".to_string(),
            "enter_let:a".to_string(),
            "exit_let:a".to_string(),
            "post_let:a".to_string(),
        ],
        "pre_let fires before value fold; enter_let between value/body; \
         exit_let before post_let"
    );
}
