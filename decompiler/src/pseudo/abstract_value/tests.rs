use super::*;

#[test]
fn test_as_bool() {
    let v = AbstractValue::Constant(AbstractLiteral::Bool(true));
    assert_eq!(v.as_bool(), Some(true));

    let v = AbstractValue::Unknown;
    assert_eq!(v.as_bool(), None);
}
