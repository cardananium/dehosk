use crate::decompile::constructor_data::{
    ConstrPairProjection, rewrite_constr_unpack_pair_projection,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoData, PseudoExpr};
use crate::pseudo::field_selector::FieldSelector;

pub(super) enum RootStep {
    Continue(PseudoExpr),
    Return(PseudoExpr),
}

pub(super) fn simplify_field_access_root(record: PseudoExpr, selector: FieldSelector) -> RootStep {
    let constr_projection = if selector.is_pair_fst() {
        Some(ConstrPairProjection::Tag)
    } else if selector.is_pair_snd() {
        Some(ConstrPairProjection::Fields)
    } else {
        None
    };
    if let Some(projection) = constr_projection
        && let Some(rewritten) = rewrite_constr_unpack_pair_projection(&record, None, projection)
    {
        return RootStep::Continue(rewritten);
    }

    match record {
        PseudoExpr::BuiltinCall { name, mut args } => {
            if *name == crate::BuiltinId::DataConstr && args.len() == 2 {
                if selector.as_pretty_name() == "fields" {
                    return RootStep::Continue(args.pop().expect("Data.Constr fields arg"));
                } else if selector.as_pretty_name() == "tag" {
                    return RootStep::Continue(args.remove(0));
                }
            }
            if (name == "Pair.new" || name == "new_pair") && args.len() == 2 {
                if selector.is_pair_fst() {
                    return RootStep::Continue(args.remove(0));
                } else if selector.is_pair_snd() {
                    return RootStep::Continue(args.pop().expect("Pair.new snd arg"));
                }
            }
            if *name == crate::BuiltinId::ListTail && args.len() == 1 {
                return RootStep::Continue(PseudoExpr::IndexAccess {
                    collection: PBox::new(args.pop().expect("List.tail arg")),
                    index: 1,
                });
            }
            if *name == crate::BuiltinId::ListHead && args.len() == 1 {
                return RootStep::Continue(PseudoExpr::IndexAccess {
                    collection: PBox::new(args.pop().expect("List.head arg")),
                    index: 0,
                });
            }
            RootStep::Return(PseudoExpr::field_access_typed(
                PseudoExpr::BuiltinCall { name, args },
                selector,
            ))
        }
        PseudoExpr::Data(data) => match *data {
            PseudoData::Constr(tag, fields) => {
                if selector.as_pretty_name() == "tag" {
                    return RootStep::Continue(PseudoExpr::Int(tag.into()));
                }
                if selector.as_pretty_name() == "fields" {
                    return RootStep::Continue(PseudoExpr::List {
                        elements: fields
                            .into_iter()
                            .map(|d| PseudoExpr::Data(Box::new(d)))
                            .collect(),
                        tail: None,
                    });
                }
                RootStep::Return(PseudoExpr::field_access_typed(
                    PseudoExpr::Data(Box::new(PseudoData::Constr(tag, fields))),
                    selector,
                ))
            }
            other => RootStep::Return(PseudoExpr::field_access_typed(
                PseudoExpr::Data(Box::new(other)),
                selector,
            )),
        },
        other => RootStep::Return(PseudoExpr::field_access_typed(other, selector)),
    }
}

pub(super) fn simplify_index_access_root(collection: PseudoExpr, index: usize) -> RootStep {
    match collection {
        PseudoExpr::List { mut elements, tail } => {
            if index < elements.len() {
                return RootStep::Continue(elements.remove(index));
            }
            if index == elements.len() {
                match tail {
                    Some(t) => return RootStep::Continue(t.into_inner()),
                    None => {
                        return RootStep::Return(PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::List {
                                elements,
                                tail: None,
                            }),
                            index,
                        });
                    }
                }
            }
            RootStep::Return(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::List { elements, tail }),
                index,
            })
        }
        other => RootStep::Return(PseudoExpr::IndexAccess {
            collection: PBox::new(other),
            index,
        }),
    }
}
