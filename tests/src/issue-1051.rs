//@ [!lean] skip
use std::num::NonZeroU8;

pub fn get_inner(x: NonZeroU8) -> u8 {
    x.get()
}

pub trait KeySerde {
    fn serialize(&self) -> Vec<u8>;
    fn deserialize<T: AsRef<[u8]>>(bytes: T) -> Result<Self, ()>
    where
        Self: Sized;
}

pub trait KeyPairSerde {
    type PublicKey: KeySerde;
    type PrivateKey: KeySerde;
    fn from_public_and_private(public_key: &[u8], private_key: &[u8]) -> Result<Self, ()>
    where
        Self: Sized;
    fn get_public(&self) -> &Self::PublicKey;
    fn get_private(&self) -> &Self::PrivateKey;
}
