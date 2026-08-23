//! A pretty-printer for the [`OutputLayer::Uplc`] and
//! [`OutputLayer::UplcCanonical`] echoes.
//!
//! Two layouts share one engine:
//!
//! - **flattened** (the `Uplc` layer): the application spine is printed
//!   curried, `((f a) b) c` as `[f a b c]`. The `uplc` parser folds that
//!   straight back to `[[[f a] b] c]`, so the echo round-trips and stays valid
//!   UPLC text. The binary form buries a real script under hundreds of
//!   brackets and indent levels.
//! - **canonical** (the `UplcCanonical` layer): the binary nesting kept as-is.
//!
//! Both are laid out Wadler-style: a construct is printed on one line when it
//! fits within [`WIDTH`], otherwise it breaks with its parts indented by two.
//!
//! # Why this is hand-written
//!
//! It used to build a `pretty::RcDoc` mirroring the term. Two recursions came
//! with that: building the document, and — the one that actually bit —
//! *dropping* it, since `Rc<Doc>`'s destructor is recursive. The nesting depth
//! of a script is attacker-chosen, and on `wasm32` the engine's call stack
//! cannot be grown from the page, so echoing a deep script died in
//! `Rc<Doc>::drop_slow` with the stack exhausted. Nothing here recurses: the
//! term is flattened into an arena, widths are measured bottom-up, and the
//! output is emitted from an explicit job stack.
//!
//! Operates on `Program<Name>` (unique names — see the conversion in
//! [`super::render_uplc_unique_names`]); `Name::text()` is the distinct
//! `i_<unique>` per binder.

use uplc::ast::{Constant, Name, Program, Term};

const WIDTH: usize = 80;
const INDENT: usize = 2;

/// Render a unique-named program with the spine-flattened layout.
pub(super) fn render_program_flattened(program: &Program<Name>) -> String {
    render_program(program, true)
}

/// Render a unique-named program with the canonical binary-nested layout.
pub(super) fn render_program_canonical(program: &Program<Name>) -> String {
    render_program(program, false)
}

fn render_program(program: &Program<Name>, flatten_spine: bool) -> String {
    let version = format!(
        "{}.{}.{}",
        program.version.0, program.version.1, program.version.2
    );
    let arena = Arena::build(&program.term, flatten_spine);
    let head = format!("(program {version}");
    let body = arena.render(INDENT);
    // The program wrapper always breaks: a whole script never fits on a line,
    // and matching the old renderer here keeps the echo's shape.
    format!("{head}\n{}{body}\n)", " ".repeat(INDENT))
}

/// One printable construct. Children are arena indices, so nothing nests.
enum Shape {
    /// Rendered as-is, never broken.
    Atom(String),
    /// `(<kw> <child>)`.
    Keyword { kw: String, child: usize },
    /// `(lam <param> <body>)`.
    Lam { param: String, body: usize },
    /// `[<head> <arg> …]`.
    Spine { head: usize, args: Vec<usize> },
    /// `(<head> <part> …)` — `constr <tag>` and `case` share this shape.
    Seq { head: String, parts: Vec<usize> },
}

struct Arena {
    shapes: Vec<Shape>,
    /// Width each node would take printed on a single line.
    flat: Vec<usize>,
    root: usize,
    /// Canonical layout drops a broken application's `[` onto a line of its
    /// own, the way the `uplc` crate's own printer did; the flattened layout
    /// keeps the head on the bracket's line.
    lone_bracket: bool,
}

impl Arena {
    /// Flatten the term into the arena, iteratively.
    fn build(term: &Term<Name>, flatten_spine: bool) -> Arena {
        let mut shapes: Vec<Shape> = Vec::new();
        // Post-order: a node is built only once its children are on `results`,
        // so a parent always sits at a higher arena index than its children.
        let mut work: Vec<WorkItem<'_>> = vec![WorkItem::Enter(term)];
        let mut results: Vec<usize> = Vec::new();

        while let Some(item) = work.pop() {
            match item {
                WorkItem::Enter(t) => match t {
                    Term::Var { name, .. } => {
                        shapes.push(Shape::Atom(name.text.clone()));
                        results.push(shapes.len() - 1);
                    }
                    Term::Error { .. } => {
                        shapes.push(Shape::Atom("(error)".to_string()));
                        results.push(shapes.len() - 1);
                    }
                    Term::Builtin { fun, .. } => {
                        shapes.push(Shape::Atom(fun.to_string()));
                        let child = shapes.len() - 1;
                        shapes.push(Shape::Keyword {
                            kw: "builtin".to_string(),
                            child,
                        });
                        results.push(shapes.len() - 1);
                    }
                    Term::Constant { value, .. } => {
                        shapes.push(Shape::Atom(constant_text(value)));
                        let child = shapes.len() - 1;
                        shapes.push(Shape::Keyword {
                            kw: "con".to_string(),
                            child,
                        });
                        results.push(shapes.len() - 1);
                    }
                    Term::Delay { body, .. } => {
                        work.push(WorkItem::BuildKeyword("delay"));
                        work.push(WorkItem::Enter(body));
                    }
                    Term::Force { body, .. } => {
                        work.push(WorkItem::BuildKeyword("force"));
                        work.push(WorkItem::Enter(body));
                    }
                    Term::Lambda {
                        parameter_name,
                        body,
                        ..
                    } => {
                        work.push(WorkItem::BuildLam(parameter_name.text.clone()));
                        work.push(WorkItem::Enter(body));
                    }
                    Term::Apply {
                        function, argument, ..
                    } => {
                        if flatten_spine {
                            let (head, args) = collect_apply_spine(t);
                            work.push(WorkItem::BuildSpine(args.len()));
                            for a in args.iter().rev() {
                                work.push(WorkItem::Enter(a));
                            }
                            work.push(WorkItem::Enter(head));
                        } else {
                            work.push(WorkItem::BuildSpine(1));
                            work.push(WorkItem::Enter(argument));
                            work.push(WorkItem::Enter(function));
                        }
                    }
                    Term::Constr { tag, fields, .. } => {
                        work.push(WorkItem::BuildSeq(format!("constr {tag}"), fields.len()));
                        for f in fields.iter().rev() {
                            work.push(WorkItem::Enter(f));
                        }
                    }
                    Term::Case {
                        constr, branches, ..
                    } => {
                        work.push(WorkItem::BuildSeq("case".to_string(), branches.len() + 1));
                        for b in branches.iter().rev() {
                            work.push(WorkItem::Enter(b));
                        }
                        work.push(WorkItem::Enter(constr));
                    }
                },
                WorkItem::BuildKeyword(kw) => {
                    let child = results.pop().expect("keyword child");
                    shapes.push(Shape::Keyword {
                        kw: kw.to_string(),
                        child,
                    });
                    results.push(shapes.len() - 1);
                }
                WorkItem::BuildLam(param) => {
                    let body = results.pop().expect("lambda body");
                    shapes.push(Shape::Lam { param, body });
                    results.push(shapes.len() - 1);
                }
                WorkItem::BuildSpine(argc) => {
                    let args = results.split_off(results.len() - argc);
                    let head = results.pop().expect("spine head");
                    shapes.push(Shape::Spine { head, args });
                    results.push(shapes.len() - 1);
                }
                WorkItem::BuildSeq(head, count) => {
                    let parts = results.split_off(results.len() - count);
                    shapes.push(Shape::Seq { head, parts });
                    results.push(shapes.len() - 1);
                }
            }
        }

        let root = results.pop().expect("one result");
        let flat = flat_widths(&shapes);
        Arena {
            shapes,
            flat,
            root,
            lone_bracket: !flatten_spine,
        }
    }

    fn render(&self, indent: usize) -> String {
        let mut out = String::new();
        let mut column = indent;
        // (node, indent) or literal text / newline
        let mut jobs: Vec<Job> = vec![Job::Node(self.root, indent, false)];

        while let Some(job) = jobs.pop() {
            match job {
                Job::Text(text) => {
                    column += text.chars().count();
                    out.push_str(&text);
                }
                Job::Newline(at) => {
                    out.push('\n');
                    out.push_str(&" ".repeat(at));
                    column = at;
                }
                Job::Node(node, at, forced_flat) => {
                    let flat = forced_flat || column + self.flat[node] <= WIDTH;
                    self.emit(node, at, flat, &mut jobs);
                }
            }
        }
        out
    }

    /// Push the pieces of one node, in reverse so they pop in order.
    fn emit(&self, node: usize, at: usize, flat: bool, jobs: &mut Vec<Job>) {
        // A separator between parts, and the one before the closing bracket.
        let inner = at + INDENT;
        let sep = |jobs: &mut Vec<Job>| {
            if flat {
                jobs.push(Job::Text(" ".to_string()));
            } else {
                jobs.push(Job::Newline(inner));
            }
        };
        // Parts are collected forwards and reversed onto the job stack, so
        // the break has to be pushed before the bracket, not after it.
        let close = |jobs: &mut Vec<Job>, text: &str| {
            if !flat {
                jobs.push(Job::Newline(at));
            }
            jobs.push(Job::Text(text.to_string()));
        };

        match &self.shapes[node] {
            Shape::Atom(text) => jobs.push(Job::Text(text.clone())),
            Shape::Keyword { kw, child } => {
                let mut parts = Vec::new();
                parts.push(Job::Text(format!("({kw}")));
                sep(&mut parts);
                parts.push(Job::Node(*child, inner, flat));
                close(&mut parts, ")");
                jobs.extend(parts.into_iter().rev());
            }
            Shape::Lam { param, body } => {
                let mut parts = Vec::new();
                parts.push(Job::Text(format!("(lam {param}")));
                sep(&mut parts);
                parts.push(Job::Node(*body, inner, flat));
                close(&mut parts, ")");
                jobs.extend(parts.into_iter().rev());
            }
            Shape::Spine { head, args } => {
                let mut parts = Vec::new();
                parts.push(Job::Text("[".to_string()));
                if self.lone_bracket {
                    sep(&mut parts);
                }
                // The head sits on the bracket's own level — only the
                // arguments are indented. Nesting the head too would compound
                // with the head's own nesting and double the indent per level.
                let head_at = if self.lone_bracket { inner } else { at };
                parts.push(Job::Node(*head, head_at, flat));
                for arg in args {
                    sep(&mut parts);
                    parts.push(Job::Node(*arg, inner, flat));
                }
                if self.lone_bracket {
                    close(&mut parts, "]");
                } else {
                    // The flattened layout closes without a preceding break,
                    // so `]` never lands on a line of its own either.
                    parts.push(Job::Text("]".to_string()));
                }
                jobs.extend(parts.into_iter().rev());
            }
            Shape::Seq { head, parts: kids } => {
                let mut parts = Vec::new();
                parts.push(Job::Text(format!("({head}")));
                for kid in kids {
                    sep(&mut parts);
                    parts.push(Job::Node(*kid, inner, flat));
                }
                close(&mut parts, ")");
                jobs.extend(parts.into_iter().rev());
            }
        }
    }
}

enum WorkItem<'t> {
    Enter(&'t Term<Name>),
    BuildKeyword(&'static str),
    BuildLam(String),
    BuildSpine(usize),
    BuildSeq(String, usize),
}

enum Job {
    Text(String),
    Newline(usize),
    /// `(node, indent, inherit-flat)`
    Node(usize, usize, bool),
}

/// Single-line width of every node, children before parents.
///
/// The arena is built bottom-up, so a node's children always sit at lower
/// indices and one forward pass suffices — no recursion.
fn flat_widths(shapes: &[Shape]) -> Vec<usize> {
    let mut flat = vec![0usize; shapes.len()];
    for (i, shape) in shapes.iter().enumerate() {
        flat[i] = match shape {
            Shape::Atom(text) => text.chars().count(),
            // "(kw " + child + ")"
            Shape::Keyword { kw, child } => kw.chars().count() + 3 + flat[*child],
            // "(lam param " + body + ")"
            Shape::Lam { param, body } => param.chars().count() + 7 + flat[*body],
            // "[" + head + (" " + arg)* + "]"
            Shape::Spine { head, args } => {
                2 + flat[*head] + args.iter().map(|a| 1 + flat[*a]).sum::<usize>()
            }
            // "(head" + (" " + part)* + ")"
            Shape::Seq { head, parts } => {
                head.chars().count() + 2 + parts.iter().map(|p| 1 + flat[*p]).sum::<usize>()
            }
        };
    }
    flat
}

/// Unfold a left-nested application `((f a) b) c` into `(f, [a, b, c])`.
fn collect_apply_spine(term: &Term<Name>) -> (&Term<Name>, Vec<&Term<Name>>) {
    let mut args = Vec::new();
    let mut current = term;
    while let Term::Apply {
        function, argument, ..
    } = current
    {
        args.push(argument.as_ref());
        current = function.as_ref();
    }
    args.reverse();
    (current, args)
}

/// Reuse the `uplc` crate's constant renderer for the `(con …)` payload
/// (`integer 42`, `bytestring #ab`, `data …`, lists, pairs).
fn constant_text(value: &Constant) -> String {
    value.to_pretty()
}

#[cfg(test)]
mod tests;
