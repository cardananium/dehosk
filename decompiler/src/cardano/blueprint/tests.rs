use super::*;

#[test]
fn test_parse_minimal_blueprint() {
    let json = r#"
        {
            "preamble": {
                "title": "test",
                "version": "1.0.0"
            },
            "validators": [
                {
                    "title": "test.spend",
                    "redeemer": {
                        "title": "redeemer",
                        "dataType": "integer"
                    },
                    "compiledCode": "deadbeef",
                    "hash": "abcd1234"
                }
            ]
        }
        "#;

    let blueprint = Blueprint::from_json(json).unwrap();
    assert_eq!(blueprint.preamble.title, "test");
    assert_eq!(blueprint.validators.len(), 1);
    assert_eq!(blueprint.validators[0].title, "test.spend");
}

#[test]
fn test_find_validator() {
    let json = r#"
        {
            "preamble": {
                "title": "test",
                "version": "1.0.0"
            },
            "validators": [
                {
                    "title": "spend",
                    "redeemer": {},
                    "compiledCode": "cafe",
                    "hash": "1234"
                },
                {
                    "title": "mint",
                    "redeemer": {},
                    "compiledCode": "babe",
                    "hash": "5678"
                }
            ]
        }
        "#;

    let blueprint = Blueprint::from_json(json).unwrap();

    let spend = blueprint.find_validator("spend");
    assert!(spend.is_some());
    assert_eq!(spend.unwrap().compiled_code, "cafe");

    let mint = blueprint.find_validator("mint");
    assert!(mint.is_some());
    assert_eq!(mint.unwrap().compiled_code, "babe");

    let missing = blueprint.find_validator("withdraw");
    assert!(missing.is_none());
}

#[test]
fn test_parameter_names() {
    let validator = ValidatorBlueprint {
        title: "test".to_string(),
        description: String::new(),
        datum: Some(ParameterSchema {
            title: Some("datum".to_string()),
            description: None,
            schema: SchemaContent::Inline {
                content: HashMap::new(),
            },
        }),
        redeemer: Some(ParameterSchema {
            title: Some("redeemer".to_string()),
            description: None,
            schema: SchemaContent::Inline {
                content: HashMap::new(),
            },
        }),
        parameters: vec![],
        compiled_code: String::new(),
        hash: String::new(),
    };

    let names = validator.parameter_names();
    assert_eq!(names.len(), 2);
    assert_eq!(names[0], Some("datum"));
    assert_eq!(names[1], Some("redeemer"));
}

#[test]
fn test_validators_by_hash_groups_shared_image() {
    // Validators sharing one compiled hash collapse into a single
    // group; a third with a distinct hash forms its own.
    let json = r#"
        {
            "preamble": {
                "title": "test",
                "version": "1.0.0"
            },
            "validators": [
                {
                    "title": "multi.redeem.spend",
                    "redeemer": { "title": "r", "dataType": "integer" },
                    "compiledCode": "aa",
                    "hash": "h1"
                },
                {
                    "title": "oneshot.gift_card.spend",
                    "redeemer": { "title": "r", "dataType": "integer" },
                    "compiledCode": "bb",
                    "hash": "h2"
                },
                {
                    "title": "multi.redeem.mint",
                    "redeemer": { "title": "r", "dataType": "integer" },
                    "compiledCode": "aa",
                    "hash": "h1"
                }
            ]
        }
    "#;
    let blueprint = Blueprint::from_json(json).unwrap();
    let groups = blueprint.validators_by_hash();
    assert_eq!(groups.len(), 2, "expected 2 hash groups");
    // First-appearance order: hash h1 first (it appears at index 0),
    // then h2 (index 1), then h1's second entry joins the first group.
    assert_eq!(groups[0].len(), 2, "h1 group should have 2 entries");
    assert!(groups[0].iter().all(|v| v.hash == "h1"));
    assert_eq!(groups[1].len(), 1, "h2 group should have 1 entry");
    assert_eq!(groups[1][0].hash, "h2");
}

#[test]
fn test_validators_by_hash_empty_blueprint() {
    let json = r#"
        {
            "preamble": { "title": "test", "version": "1.0.0" },
            "validators": []
        }
    "#;
    let blueprint = Blueprint::from_json(json).unwrap();
    let groups = blueprint.validators_by_hash();
    assert!(groups.is_empty());
}

#[test]
fn p6_2_blueprint_with_optional_else_redeemer_parses() {
    // An `else` validator entry legitimately omits `redeemer`
    // (CIP-0117 §3.2: `else` receives the raw ScriptContext).
    let json = r#"
        {
            "preamble": {
                "title": "test",
                "version": "1.0.0"
            },
            "validators": [
                {
                    "title": "mod.foo.spend",
                    "datum": { "title": "d", "dataType": "integer" },
                    "redeemer": { "title": "r", "dataType": "integer" },
                    "compiledCode": "aa",
                    "hash": "h"
                },
                {
                    "title": "mod.foo.else",
                    "compiledCode": "aa",
                    "hash": "h"
                }
            ]
        }
    "#;
    let blueprint = Blueprint::from_json(json).unwrap();
    assert_eq!(blueprint.validators.len(), 2);
    let spend = &blueprint.validators[0];
    let else_v = &blueprint.validators[1];

    assert!(spend.redeemer.is_some());
    assert_eq!(spend.redeemer_name(), Some("r"));

    // Else entry: no redeemer; helpers return None / skip the slot.
    assert!(else_v.redeemer.is_none());
    assert_eq!(else_v.redeemer_name(), None);
    let else_params = else_v.parameter_names();
    assert!(
        else_params.is_empty(),
        "else entry has no params, got {else_params:?}"
    );
}
