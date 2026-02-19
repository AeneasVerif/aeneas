//@ [!lean] skip
use std::mem::discriminant;

pub enum EmptyEnum {}

#[derive(PartialEq)]
pub enum AlertLevel {
    Warning,
    Fatal,
}

#[derive(PartialEq)]
#[repr(u8)]
pub enum AlertLevelU8 {
    Warning = 1,
    Fatal = 2,
}
