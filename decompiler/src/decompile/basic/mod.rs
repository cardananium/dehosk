//! `PlutusData` → `PseudoData` conversion.
//!
//! `convert_plutus_data` materializes CBOR-decoded constants for
//! `mid::lower::lower_plutus_data`. Its two normalization rules,
//! `constructor_index` and `convert_pallas_bigint`, are the single place
//! a CBOR constructor tag and a CBOR integer are decoded.

use crate::pseudo::ast::PseudoData;

/// Convert `uplc::PlutusData` to `PseudoData`,
/// normalizing constructor tags to logical
/// indices.
pub(crate) fn convert_plutus_data(data: &uplc::PlutusData) -> PseudoData {
    use uplc::PlutusData;

    match data {
        PlutusData::BigInt(n) => PseudoData::Integer(convert_pallas_bigint(n)),
        PlutusData::BoundedBytes(bytes) => PseudoData::ByteString(bytes.to_vec()),
        PlutusData::Array(items) => {
            PseudoData::List(items.iter().map(convert_plutus_data).collect())
        }
        PlutusData::Map(pairs) => PseudoData::Map(
            pairs
                .iter()
                .map(|(k, v)| (convert_plutus_data(k), convert_plutus_data(v)))
                .collect(),
        ),
        PlutusData::Constr(constr) => {
            let fields: Vec<PseudoData> = constr.fields.iter().map(convert_plutus_data).collect();
            PseudoData::Constr(constructor_index(constr), fields)
        }
    }
}

/// The logical constructor index a decoded `Constr` node stands for.
///
/// # One index space, three encodings
///
/// Plutus `Data` writes a constructor index three ways, and only two of them
/// put it in the CBOR tag:
///
/// * tags 121-127 ARE indices 0-6;
/// * tags 1280-1400 are indices 7-127;
/// * ANY OTHER tag carries its index in a separate CBOR field —
///   `any_constructor` — which is how every index from 128 up is written. In
///   practice that tag is always 102, because 102 is the only other tag
///   `pallas`'s decoder accepts.
///
/// Those three arms are `uplc::machine::runtime`'s own
/// `convert_tag_to_constr(tag).unwrap_or_else(|| any_constructor.unwrap())` —
/// what `unConstrData` hands a running script — written to total instead of
/// panicking, and agreeing with it on EVERY `u64` tag rather than only on the
/// tags `pallas` accepts today, so widening the decoder cannot open a gap.
///
/// # It takes the NODE, not a bare tag
///
/// A bare `raw_tag: u64` could only report `102` on the general form — the
/// escape tag, not the constructor — and `102` is also what a genuine index
/// 102 (written as tag 1375) normalizes to, so `Constr(128, ..)`,
/// `Constr(1000000, ..)` and `Constr(102, ..)` would all resolve alike.
/// Taking the whole node makes that unspellable: the half of the value that
/// carries the index cannot be left behind.
///
/// The index is never a field. `pallas` keeps it in `any_constructor`, and
/// `fields` holds the constructor's real arguments under either encoding.
///
/// # `any_constructor` missing on an escape tag
///
/// The machine `unwrap()`s here; this returns `0`. Only a hand-assembled
/// `Constr` reaches that arm — `pallas`'s decoder always populates the field
/// for tag 102, and `Data::constr` always populates it for an index >= 128.
/// `0` is not a guess: it is what `pallas`'s ENCODER writes into the index
/// field, so the node resolves to the index its own serialized bytes carry.
pub(crate) fn constructor_index(constr: &uplc::Constr<uplc::PlutusData>) -> usize {
    let raw_tag = constr.tag as usize;
    if (121..=127).contains(&raw_tag) {
        raw_tag - 121
    } else if (1280..=1400).contains(&raw_tag) {
        raw_tag - 1280 + 7
    } else {
        constr.any_constructor.unwrap_or_default() as usize
    }
}

/// Convert pallas `BigInt` to `num_bigint::BigInt`.
pub(crate) fn convert_pallas_bigint(n: &uplc::BigInt) -> num_bigint::BigInt {
    use num_bigint::Sign;

    match n {
        uplc::BigInt::Int(i) => {
            let val: i128 = (*i).into();
            num_bigint::BigInt::from(val)
        }
        uplc::BigInt::BigUInt(bytes) => num_bigint::BigInt::from_bytes_be(Sign::Plus, bytes),
        // Big negative integers: big-endian bytes for `n`, value `-(n + 1)`.
        uplc::BigInt::BigNInt(bytes) => num_bigint::BigInt::from_bytes_be(Sign::Minus, bytes) - 1,
    }
}

#[cfg(test)]
mod tests;
