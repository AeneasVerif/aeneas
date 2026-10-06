//@ [!lean] skip
//@ charon-args=--rustc-arg=--cfg=miri
// Excerpts of https://github.com/dtolnay/zmij at
// 35355256734db2c69a19aba4cae98c7fd8e14adf (MIT), in its scalar configuration
// (`--cfg miri`).
#![allow(dead_code)]
#![allow(non_camel_case_types, non_snake_case)]
#![allow(
    clippy::blocks_in_conditions,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_ptr_alignment,
    clippy::cast_sign_loss,
    clippy::doc_markdown,
    clippy::incompatible_msrv,
    clippy::items_after_statements,
    clippy::manual_ilog2,
    clippy::many_single_char_names,
    clippy::modulo_one,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::needless_late_init,
    clippy::never_loop,
    clippy::redundant_else,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::unreadable_literal,
    clippy::used_underscore_items,
    clippy::while_immutable_condition,
    clippy::wildcard_imports
)]

#[derive(Copy, Clone)]
#[cfg_attr(test, derive(Debug, PartialEq))]
struct uint128 {
    hi: u64,
    lo: u64,
}

// Use umul128_hi64 for division.
const USE_UMUL128_HI64: bool = cfg!(target_vendor = "apple");

// Computes 128-bit result of multiplication of two 64-bit unsigned integers.
const fn umul128(x: u64, y: u64) -> u128 {
    x as u128 * y as u128
}

#[inline]
const fn umul128_hi64(x: u64, y: u64) -> u64 {
    (umul128(x, y) >> 64) as u64
}

#[rustfmt::skip]
const POW10_MINOR: [u64; 28] = [
    0x8000000000000000, 0xa000000000000000, 0xc800000000000000,
    0xfa00000000000000, 0x9c40000000000000, 0xc350000000000000,
    0xf424000000000000, 0x9896800000000000, 0xbebc200000000000,
    0xee6b280000000000, 0x9502f90000000000, 0xba43b74000000000,
    0xe8d4a51000000000, 0x9184e72a00000000, 0xb5e620f480000000,
    0xe35fa931a0000000, 0x8e1bc9bf04000000, 0xb1a2bc2ec5000000,
    0xde0b6b3a76400000, 0x8ac7230489e80000, 0xad78ebc5ac620000,
    0xd8d726b7177a8000, 0x878678326eac9000, 0xa968163f0a57b400,
    0xd3c21bcecceda100, 0x84595161401484a0, 0xa56fa5b99019a5c8,
    0xcecb8f27f4200f3a,
];

#[rustfmt::skip]
const POW10_MAJOR: [uint128; 23] = [
    uint128 { hi: 0xaf8e5410288e1b6f, lo: 0x07ecf0ae5ee44dda }, // -303
    uint128 { hi: 0xb1442798f49ffb4a, lo: 0x99cd11cfdf41779d }, // -275
    uint128 { hi: 0xb2fe3f0b8599ef07, lo: 0x861fa7e6dcb4aa15 }, // -247
    uint128 { hi: 0xb4bca50b065abe63, lo: 0x0fed077a756b53aa }, // -219
    uint128 { hi: 0xb67f6455292cbf08, lo: 0x1a3bc84c17b1d543 }, // -191
    uint128 { hi: 0xb84687c269ef3bfb, lo: 0x3d5d514f40eea742 }, // -163
    uint128 { hi: 0xba121a4650e4ddeb, lo: 0x92f34d62616ce413 }, // -135
    uint128 { hi: 0xbbe226efb628afea, lo: 0x890489f70a55368c }, // -107
    uint128 { hi: 0xbdb6b8e905cb600f, lo: 0x5400e987bbc1c921 }, //  -79
    uint128 { hi: 0xbf8fdb78849a5f96, lo: 0xde98520472bdd034 }, //  -51
    uint128 { hi: 0xc16d9a0095928a27, lo: 0x75b7053c0f178294 }, //  -23
    uint128 { hi: 0xc350000000000000, lo: 0x0000000000000000 }, //    5
    uint128 { hi: 0xc5371912364ce305, lo: 0x6c28000000000000 }, //   33
    uint128 { hi: 0xc722f0ef9d80aad6, lo: 0x424d3ad2b7b97ef6 }, //   61
    uint128 { hi: 0xc913936dd571c84c, lo: 0x03bc3a19cd1e38ea }, //   89
    uint128 { hi: 0xcb090c8001ab551c, lo: 0x5cadf5bfd3072cc6 }, //  117
    uint128 { hi: 0xcd036837130890a1, lo: 0x36dba887c37a8c10 }, //  145
    uint128 { hi: 0xcf02b2c21207ef2e, lo: 0x94f967e45e03f4bc }, //  173
    uint128 { hi: 0xd106f86e69d785c7, lo: 0xe13336d701beba52 }, //  201
    uint128 { hi: 0xd31045a8341ca07c, lo: 0x1ede48111209a051 }, //  229
    uint128 { hi: 0xd51ea6fa85785631, lo: 0x552a74227f3ea566 }, //  257
    uint128 { hi: 0xd732290fbacaf133, lo: 0xa97c177947ad4096 }, //  285
    uint128 { hi: 0xd94ad8b1c7380874, lo: 0x18375281ae7822bc }, //  313
];

#[rustfmt::skip]
const POW10_FIXUPS: [u32; 20] = [
    0x0a4e363f, 0x00001840, 0x00006400, 0x24200040, 0x00000000,
    0x0c000000, 0x82c81380, 0x5e4ce01f, 0xd730f60f, 0x0000001b,
    0x00000000, 0xcdf7fffc, 0x6e8201d8, 0x40cd3fd1, 0xdb642501,
    0x00000d0d, 0x14042400, 0x53713840, 0x11781db4, 0x00000000,
];

// 128-bit significands of powers of 10 rounded down.
#[repr(C, align(64))]
struct Pow10SignificandTable {
    data: [u64; if Self::COMPRESS {
        0
    } else {
        Self::NUM_POW10S * 2
    }],
}

impl Pow10SignificandTable {
    const COMPRESS: bool = cfg!(opt_level = "s");
    const SPLIT_TABLES: bool = !Self::COMPRESS && cfg!(target_arch = "aarch64");
    const NUM_POW10S: usize = 618;

    // Computes the 128-bit significand of 10**i using method by Dougall Johnson.
    #[inline]
    const fn compute(i: u32) -> uint128 {
        const STRIDE: u32 = POW10_MINOR.len() as u32;
        let m = unsafe { *POW10_MINOR.as_ptr().add(((i + 10) % STRIDE) as usize) };
        let h = unsafe { *POW10_MAJOR.as_ptr().add(((i + 10) / STRIDE) as usize) };

        let h1 = umul128_hi64(h.lo, m);

        let c0 = h.lo.wrapping_mul(m);
        let c1 = h1.wrapping_add(h.hi.wrapping_mul(m));
        let c2 = (c1 < h1) as u64 + umul128_hi64(h.hi, m);

        let mut result = if (c2 >> 63) != 0 {
            uint128 { hi: c2, lo: c1 }
        } else {
            uint128 {
                hi: (c2 << 1) | (c1 >> 63),
                lo: (c1 << 1) | (c0 >> 63),
            }
        };
        result.lo -=
            ((unsafe { *POW10_FIXUPS.as_ptr().add((i >> 5) as usize) } >> (i & 31)) & 1) as u64;
        result
    }

    const fn new() -> Self {
        let mut data = [0; if Self::COMPRESS {
            0
        } else {
            Self::NUM_POW10S * 2
        }];

        let mut i = 0;
        while i < Self::NUM_POW10S && !Self::COMPRESS {
            let result = Self::compute(i as u32);
            if Self::SPLIT_TABLES {
                data[Self::NUM_POW10S - i - 1] = result.hi;
                data[Self::NUM_POW10S * 2 - i - 1] = result.lo;
            } else {
                data[i * 2] = result.hi;
                data[i * 2 + 1] = result.lo;
            }
            i += 1;
        }

        Pow10SignificandTable { data }
    }

    #[inline]
    unsafe fn get_unchecked(&self, dec_exp: i32) -> uint128 {
        const DEC_EXP_MIN: i32 = -293;
        let i = dec_exp - DEC_EXP_MIN;
        if Self::COMPRESS {
            return Self::compute(i as u32);
        }
        if !Self::SPLIT_TABLES {
            let p = unsafe { self.data.as_ptr().add((i * 2) as usize) };
            return uint128 {
                hi: unsafe { *p },
                lo: unsafe { *p.add(1) },
            };
        }

        unsafe {
            // The caller passes -e - 1 as dec_exp, so ~dec_exp recovers e.
            // Picking the base so that e itself is the index lets both loads
            // share sxtw addressing.
            #[cfg_attr(
                not(all(any(target_arch = "x86_64", target_arch = "aarch64"), not(miri))),
                allow(unused_mut)
            )]
            let mut p = self
                .data
                .as_ptr()
                .offset(Self::NUM_POW10S as isize + DEC_EXP_MIN as isize);
            #[cfg(all(any(target_arch = "x86_64", target_arch = "aarch64"), not(miri)))]
            asm!("/*{0}*/", inout(reg) p);
            uint128 {
                hi: *p.offset(!(dec_exp as isize)),
                lo: *p.offset(!(dec_exp as isize) + Self::NUM_POW10S as isize),
            }
        }
    }

    #[cfg(test)]
    fn get(&self, dec_exp: i32) -> uint128 {
        const DEC_EXP_MIN: i32 = -292;
        assert!((DEC_EXP_MIN..DEC_EXP_MIN + Self::NUM_POW10S as i32).contains(&dec_exp));
        unsafe { self.get_unchecked(dec_exp) }
    }
}

// Align data since unaligned access may be slower when crossing a
// hardware-specific boundary.
#[repr(C, align(2))]
struct Digits2([u8; 200]);

static DIGITS2: Digits2 = Digits2(
    *b"0001020304050607080910111213141516171819\
       2021222324252627282930313233343536373839\
       4041424344454647484950515253545556575859\
       6061626364656667686970717273747576777879\
       8081828384858687888990919293949596979899",
);

// Converts value in the range [0, 100) to a string. GCC generates a bit better
// code when value is pointer-size (https://www.godbolt.org/z/5fEPMT1cc).
#[cfg_attr(feature = "no-panic", no_panic)]
unsafe fn digits2(value: usize) -> &'static u16 {
    debug_assert!(value < 100);

    #[allow(clippy::cast_ptr_alignment)]
    unsafe {
        &*DIGITS2.0.as_ptr().cast::<u16>().add(value)
    }
}

unsafe fn read_digits2(value: usize) -> u16 {
    debug_assert!(value < 100);

    #[allow(clippy::cast_ptr_alignment)]
    unsafe {
        *DIGITS2.0.as_ptr().cast::<u16>().add(value)
    }
}

const DIV100_EXP: i32 = 19;
const DIV100_SIG: u32 = (1 << DIV100_EXP) / 100 + 1;

use core::mem::MaybeUninit;
use core::{ptr, slice};

unsafe fn write_digits(buffer: *mut u8, has_extra_digit: bool, digits: u64, last_digit: u8) {
    let bcd_size = 16;
    unsafe {
        buffer
            .add(usize::from(has_extra_digit))
            .cast::<u64>()
            .write_unaligned(digits);
        ptr::write(
            buffer.add(usize::from(has_extra_digit) + bcd_size),
            b'0' + last_digit,
        );
    }
}

unsafe fn write_fixed(buffer: *mut u8, length: usize, dec_exp: i32) -> *mut u8 {
    if length as i32 - 1 <= dec_exp {
        // 1234e7 -> 12340000000.0
        return unsafe {
            ptr::copy(buffer.add(1), buffer, length);
            ptr::write_bytes(buffer.add(length), b'0', dec_exp as usize + 3 - length);
            *buffer.add(dec_exp as usize + 1) = b'.';
            buffer.add(dec_exp as usize + 3)
        };
    } else if 0 <= dec_exp {
        // 1234e-2 -> 12.34
        return unsafe {
            ptr::copy(buffer.add(1), buffer, dec_exp as usize + 1);
            *buffer.add(dec_exp as usize + 1) = b'.';
            buffer.add(length + 1)
        };
    } else {
        // 1234e-6 -> 0.001234
        return unsafe {
            ptr::copy(buffer.add(1), buffer.add((1 - dec_exp) as usize), length);
            ptr::write_bytes(buffer, b'0', (1 - dec_exp) as usize);
            *buffer.add(1) = b'.';
            buffer.add((1 - dec_exp) as usize + length)
        };
    }
}

unsafe fn write_exponent_data(buffer: *mut u8, exp_data: u64) -> *mut u8 {
    let len = (exp_data >> 48) as usize;
    unsafe {
        ptr::copy_nonoverlapping(ptr::addr_of!(exp_data).cast::<u8>(), buffer, 5);
        return buffer.add(len);
    }
}

unsafe fn write_exponent(mut buffer: *mut u8, mut dec_exp: i32) -> *mut u8 {
    let sign_ptr = buffer;
    let e_sign = if dec_exp >= 0 {
        (u16::from(b'+') << 8) | u16::from(b'e')
    } else {
        (u16::from(b'-') << 8) | u16::from(b'e')
    };
    buffer = unsafe { buffer.add(1) };
    dec_exp = if dec_exp >= 0 { dec_exp } else { -dec_exp };
    buffer = unsafe { buffer.add(usize::from(dec_exp >= 10)) };
    // digit = dec_exp / 100
    let digit = if USE_UMUL128_HI64 {
        umul128_hi64(dec_exp as u64, 0x290000000000000) as u32
    } else {
        (dec_exp as u32 * DIV100_SIG) >> DIV100_EXP
    };
    unsafe {
        *buffer = b'0' + digit as u8;
    }
    buffer = unsafe { buffer.add(usize::from(dec_exp >= 100)) };
    dec_exp -= (digit * 100) as i32;
    unsafe {
        buffer
            .cast::<u16>()
            .write_unaligned(read_digits2(dec_exp as usize));
        sign_ptr.cast::<u16>().write_unaligned(e_sign);
        buffer.add(2)
    }
}

const BUFFER_SIZE: usize = 24;

pub struct Buffer {
    bytes: [MaybeUninit<u8>; BUFFER_SIZE],
}

impl Buffer {
    #[inline]
    #[cfg_attr(feature = "no-panic", no_panic)]
    pub fn new() -> Self {
        let bytes = [MaybeUninit::<u8>::uninit(); BUFFER_SIZE];
        Buffer { bytes }
    }

    #[cfg_attr(feature = "no-panic", no_panic)]
    pub fn format_finite<F: Float>(&mut self, f: F) -> &[u8] {
        unsafe {
            let end = f.write_to_zmij_buffer(self.bytes.as_mut_ptr().cast::<u8>());
            let len = end.offset_from(self.bytes.as_ptr().cast::<u8>()) as usize;
            let slice = slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), len);
            slice
        }
    }
}

pub trait Float: private::Sealed {}

mod private {
    pub trait Sealed: Copy {
        unsafe fn write_to_zmij_buffer(self, buffer: *mut u8) -> *mut u8;
    }
}

#[derive(Copy, Clone)]
pub struct Exponent(pub i32);

impl private::Sealed for Exponent {
    unsafe fn write_to_zmij_buffer(self, buffer: *mut u8) -> *mut u8 {
        unsafe { write_exponent(buffer, self.0) }
    }
}

impl Float for Exponent {}

pub fn format_exponent(dec_exp: i32) -> u8 {
    let mut buffer = Buffer::new();
    let s = buffer.format_finite(Exponent(dec_exp));
    s[0]
}
