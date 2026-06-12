//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1051
//!
//! A trait with two associated types bounded by the *same* trait produces two
//! parent clauses which instantiate that trait with different type arguments
//! (here `Self::PublicKey` and `Self::PrivateKey`, both bounded by `KeySerde`).
//! Before the fix, Aeneas generated the same field name (`KeySerdeInst`) for
//! both, producing a structure with duplicate fields.

pub trait KeySerde {
    fn serialize(&self) -> u32;
}

pub trait KeyPairSerde {
    type PublicKey: KeySerde;
    type PrivateKey: KeySerde;
    fn get_public(&self) -> Self::PublicKey;
    fn get_private(&self) -> Self::PrivateKey;
}
