//! `#[derive(Debug)]`'s output for a recursive type, written from a heap stack.
//!
//! The derived impl formats a child by calling `Debug::fmt` on it — one call
//! frame per level of nesting — and the nesting of a constant is chosen by the
//! script that carries it. A type whose `Debug` output is load-bearing (it is
//! printed into fingerprints and rendered patterns) describes one layer at a
//! time instead, and [`write`] does the descending.
//!
//! The punctuation is the derive's, including the `{:#?}` layout: four spaces
//! per level and a comma after every field, so a hand-written impl prints
//! byte-for-byte what the derived one did.

use std::fmt;

/// A type whose `Debug` output [`write`] can produce one layer at a time.
pub(crate) trait DebugLayers: Sized {
    /// Describe this node's own variant: its name, and its fields with nested
    /// nodes left as [`Field::Node`] / [`Field::Nodes`] / [`Field::Pairs`].
    fn layer<'a>(&'a self, out: &mut Layer<'a, Self>);
}

/// One field of a tuple variant.
pub(crate) enum Field<'a, T> {
    /// A value that does not nest, printed with its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    /// A nested node (behind a `Box` or not — `Box` prints transparently).
    Node(&'a T),
    /// A `Vec` of nested nodes, printed as a list.
    Nodes(&'a [T]),
    /// A `Vec` of node pairs, printed as a list of 2-tuples.
    Pairs(&'a [(T, T)]),
}

enum Token<'a, T> {
    Text(&'static str),
    Leaf(&'a dyn fmt::Debug),
    Node(&'a T),
    /// The derive's `PadAdapter` around one field: four more spaces at the
    /// start of every line until the matching [`Token::Dedent`].
    Indent,
    Dedent,
}

/// The tokens one node expands into, in output order.
pub(crate) struct Layer<'a, T> {
    tokens: Vec<Token<'a, T>>,
    pretty: bool,
}

impl<'a, T> Layer<'a, T> {
    /// A unit variant: just its name.
    pub(crate) fn unit(&mut self, name: &'static str) {
        self.tokens.push(Token::Text(name));
    }

    /// A tuple variant, as `Formatter::debug_tuple` lays it out.
    pub(crate) fn tuple(&mut self, name: &'static str, fields: &[Field<'a, T>]) {
        self.tokens.push(Token::Text(name));
        self.open_fields(fields.len(), |layer, index| layer.field(&fields[index]));
    }

    /// `debug_tuple`'s framing around `count` fields; `field` emits one.
    fn open_fields(&mut self, count: usize, mut field: impl FnMut(&mut Self, usize)) {
        if count == 0 {
            return;
        }
        if self.pretty {
            self.tokens.push(Token::Text("(\n"));
            for index in 0..count {
                self.tokens.push(Token::Indent);
                field(self, index);
                self.tokens.push(Token::Text(",\n"));
                self.tokens.push(Token::Dedent);
            }
        } else {
            for index in 0..count {
                self.tokens
                    .push(Token::Text(if index == 0 { "(" } else { ", " }));
                field(self, index);
            }
        }
        self.tokens.push(Token::Text(")"));
    }

    /// `debug_list`'s framing around `count` entries; `entry` emits one.
    fn list(&mut self, count: usize, mut entry: impl FnMut(&mut Self, usize)) {
        self.tokens.push(Token::Text("["));
        for index in 0..count {
            if self.pretty {
                if index == 0 {
                    self.tokens.push(Token::Text("\n"));
                }
                self.tokens.push(Token::Indent);
                entry(self, index);
                self.tokens.push(Token::Text(",\n"));
                self.tokens.push(Token::Dedent);
            } else {
                if index > 0 {
                    self.tokens.push(Token::Text(", "));
                }
                entry(self, index);
            }
        }
        self.tokens.push(Token::Text("]"));
    }

    fn field(&mut self, field: &Field<'a, T>) {
        match *field {
            Field::Leaf(value) => self.tokens.push(Token::Leaf(value)),
            Field::Node(node) => self.tokens.push(Token::Node(node)),
            Field::Nodes(nodes) => {
                self.list(nodes.len(), |layer, index| {
                    layer.tokens.push(Token::Node(&nodes[index]));
                });
            }
            Field::Pairs(pairs) => {
                self.list(pairs.len(), |layer, index| {
                    // A 2-tuple prints as `debug_tuple("")` does.
                    let (key, value) = &pairs[index];
                    layer.open_fields(2, |layer, field| {
                        layer
                            .tokens
                            .push(Token::Node(if field == 0 { key } else { value }));
                    });
                });
            }
        }
    }
}

/// Where the output goes, and the indentation `{:#?}` owes each new line.
struct Sink<'f, 'g> {
    f: &'f mut fmt::Formatter<'g>,
    pretty: bool,
    depth: usize,
    on_newline: bool,
}

impl Sink<'_, '_> {
    fn write(&mut self, text: &str) -> fmt::Result {
        if !self.pretty {
            return self.f.write_str(text);
        }
        for line in text.split_inclusive('\n') {
            if self.on_newline {
                for _ in 0..self.depth {
                    self.f.write_str("    ")?;
                }
            }
            self.on_newline = line.ends_with('\n');
            self.f.write_str(line)?;
        }
        Ok(())
    }
}

/// Write `root` exactly as `#[derive(Debug)]` would, without recursing.
pub(crate) fn write<T: DebugLayers>(root: &T, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let pretty = f.alternate();
    let mut sink = Sink {
        f,
        pretty,
        depth: 0,
        on_newline: false,
    };
    let mut pending: Vec<Token<'_, T>> = vec![Token::Node(root)];
    while let Some(token) = pending.pop() {
        match token {
            Token::Node(node) => {
                let mut layer = Layer {
                    tokens: Vec::new(),
                    pretty,
                };
                node.layer(&mut layer);
                pending.extend(layer.tokens.into_iter().rev());
            }
            Token::Text(text) => sink.write(text)?,
            Token::Leaf(value) if pretty => sink.write(&format!("{value:#?}"))?,
            Token::Leaf(value) => fmt::Debug::fmt(value, sink.f)?,
            Token::Indent => sink.depth += 1,
            Token::Dedent => sink.depth -= 1,
        }
    }
    Ok(())
}
