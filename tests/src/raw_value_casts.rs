//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
//@ [lean] subdir=RawValueCasts
//@ [lean] aeneas-args=-split-files -all-computable

// Deliberate transmute examples, including cases with a safer `as` alternative.
#[allow(unnecessary_transmutes)]
pub mod ext {
    pub fn bool_to_byte(value: bool) -> u8 {
        unsafe { std::mem::transmute(value) }
    }

    /// # Safety
    /// `value` must be zero or one; initialized storage alone is insufficient.
    pub unsafe fn byte_to_bool(value: u8) -> bool {
        std::mem::transmute(value)
    }

    pub fn unsigned_to_signed(value: u32) -> i32 {
        unsafe { std::mem::transmute(value) }
    }

    pub fn signed_to_unsigned(value: i32) -> u32 {
        unsafe { std::mem::transmute(value) }
    }
}

pub fn bool_byte_round_trip(value: bool) -> bool {
    let byte = ext::bool_to_byte(value);
    unsafe { ext::byte_to_bool(byte) }
}

pub fn checked_byte_to_bool(value: u8) -> Option<bool> {
    if value <= 1 {
        Some(unsafe { ext::byte_to_bool(value) })
    } else {
        None
    }
}

pub fn signed_round_trip(value: u32) -> u32 {
    ext::signed_to_unsigned(ext::unsigned_to_signed(value))
}

/// Exclusive access does not justify returning `&mut u8` into a bool:
/// the caller could write 2, making restoration as bool invalid. A by-value
/// byte conversion is safe because it cannot modify the original bool.
pub fn bool_byte_copy(value: &mut bool) -> u8 {
    ext::bool_to_byte(*value)
}

#[test]
fn validity_and_round_trips() {
    for value in [false, true] {
        assert_eq!(bool_byte_round_trip(value), value);
        assert_eq!(ext::bool_to_byte(value), u8::from(value));
        let mut original = value;
        let mut copy = bool_byte_copy(&mut original);
        assert_eq!(copy, u8::from(value));
        copy = 2;
        assert_eq!(copy, 2);
        assert_eq!(original, value);
    }
    for value in u8::MIN..=u8::MAX {
        let expected = match value {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        };
        assert_eq!(checked_byte_to_bool(value), expected);
    }
    for value in [0, 1, i32::MAX as u32, 0x80000000, u32::MAX] {
        assert_eq!(ext::unsigned_to_signed(value), value as i32);
        assert_eq!(signed_round_trip(value), value);
    }
    for value in [i32::MIN, -1, 0, 1, i32::MAX] {
        assert_eq!(ext::signed_to_unsigned(value), value as u32);
    }
}
