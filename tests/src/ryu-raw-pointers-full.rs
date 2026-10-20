//@ [!lean] skip
// Excerpts of https://github.com/dtolnay/ryu at
// 22a692e0b27d9ca74231a475eb690a9446ed44af (Apache-2.0 OR BSL-1.0).
#![allow(dead_code)]

mod digit_table {
    // Translated from C to Rust. The original C code can be found at
    // https://github.com/ulfjack/ryu and carries the following license:
    //
    // Copyright 2018 Ulf Adams
    //
    // The contents of this file may be used under the terms of the Apache License,
    // Version 2.0.
    //
    //    (See accompanying file LICENSE-Apache or copy at
    //     http://www.apache.org/licenses/LICENSE-2.0)
    //
    // Alternatively, the contents of this file may be used under the terms of
    // the Boost Software License, Version 1.0.
    //    (See accompanying file LICENSE-Boost or copy at
    //     https://www.boost.org/LICENSE_1_0.txt)
    //
    // Unless required by applicable law or agreed to in writing, this software
    // is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
    // KIND, either express or implied.

    // A table of all two-digit numbers. This is used to speed up decimal digit
    // generation by copying pairs of digits into the final output.
    pub static DIGIT_TABLE: [u8; 200] = *b"\
        0001020304050607080910111213141516171819\
        2021222324252627282930313233343536373839\
        4041424344454647484950515253545556575859\
        6061626364656667686970717273747576777879\
        8081828384858687888990919293949596979899";
}

mod pretty {
    pub use exponent::write_exponent3;

    mod exponent {
        use crate::digit_table::DIGIT_TABLE;
        use core::ptr;

        #[cfg_attr(feature = "no-panic", inline)]
        pub unsafe fn write_exponent3(mut k: isize, mut result: *mut u8) -> usize {
            let sign = k < 0;
            if sign {
                *result = b'-';
                result = result.add(1);
                k = -k;
            }

            debug_assert!(k < 1000);
            if k >= 100 {
                *result = b'0' + (k / 100) as u8;
                k %= 100;
                let d = DIGIT_TABLE.as_ptr().offset(k * 2);
                ptr::copy_nonoverlapping(d, result.add(1), 2);
                sign as usize + 3
            } else if k >= 10 {
                let d = DIGIT_TABLE.as_ptr().offset(k * 2);
                ptr::copy_nonoverlapping(d, result, 2);
                sign as usize + 2
            } else {
                *result = b'0' + k as u8;
                sign as usize + 1
            }
        }

        #[cfg_attr(feature = "no-panic", inline)]
        pub unsafe fn write_exponent2(mut k: isize, mut result: *mut u8) -> usize {
            let sign = k < 0;
            if sign {
                *result = b'-';
                result = result.add(1);
                k = -k;
            }

            debug_assert!(k < 100);
            if k >= 10 {
                let d = DIGIT_TABLE.as_ptr().offset(k * 2);
                ptr::copy_nonoverlapping(d, result, 2);
                sign as usize + 2
            } else {
                *result = b'0' + k as u8;
                sign as usize + 1
            }
        }
    }

    pub unsafe fn format64_zero(sign: bool, result: *mut u8) -> usize {
        let mut index = 0isize;
        if sign {
            *result = b'-';
            index += 1;
        }

        ptr::copy_nonoverlapping(b"0.0".as_ptr(), result.offset(index), 3);
        sign as usize + 3
    }

    pub unsafe fn format64_point(result: *mut u8, index: isize, length: isize, kk: isize) -> usize {
        ptr::copy(result.offset(index + 1), result.offset(index), kk as usize);
        *result.offset(index + kk) = b'.';
        index as usize + length as usize + 1
    }

    pub unsafe fn format64_exp(result: *mut u8, index: isize, length: isize, kk: isize) -> usize {
        *result.offset(index) = *result.offset(index + 1);
        *result.offset(index + 1) = b'.';
        *result.offset(index + length + 1) = b'e';
        index as usize
            + length as usize
            + 2
            + exponent::write_exponent3(kk - 1, result.offset(index + length + 2))
    }

    use core::ptr;
}

mod d2s_intrinsics {
    use core::ptr;

    #[cfg_attr(feature = "no-panic", inline)]
    pub fn mul_shift_64(m: u64, mul: &(u64, u64), j: u32) -> u64 {
        let b0 = m as u128 * mul.0 as u128;
        let b2 = m as u128 * mul.1 as u128;
        (((b0 >> 64) + b2) >> (j - 64)) as u64
    }

    #[cfg_attr(feature = "no-panic", inline)]
    pub unsafe fn mul_shift_all_64(
        m: u64,
        mul: &(u64, u64),
        j: u32,
        vp: *mut u64,
        vm: *mut u64,
        mm_shift: u32,
    ) -> u64 {
        ptr::write(vp, mul_shift_64(4 * m + 2, mul, j));
        ptr::write(vm, mul_shift_64(4 * m - 1 - mm_shift as u64, mul, j));
        mul_shift_64(4 * m, mul, j)
    }
}

mod d2s {
    use crate::d2s_intrinsics::mul_shift_all_64;
    use core::mem::MaybeUninit;

    pub fn mul_shift_all(m2: u64, mul: &(u64, u64), j: u32, mm_shift: u32) -> (u64, u64, u64) {
        let vr: u64;
        let vp: u64;
        let vm: u64;
        let mut vp_uninit: MaybeUninit<u64> = MaybeUninit::uninit();
        let mut vm_uninit: MaybeUninit<u64> = MaybeUninit::uninit();
        vr = unsafe {
            mul_shift_all_64(
                m2,
                mul,
                j,
                vp_uninit.as_mut_ptr(),
                vm_uninit.as_mut_ptr(),
                mm_shift,
            )
        };
        vp = unsafe { vp_uninit.assume_init() };
        vm = unsafe { vm_uninit.assume_init() };
        (vr, vp, vm)
    }
}

mod buffer {
    use core::mem::MaybeUninit;
    use core::slice;

    pub struct Buffer {
        bytes: [MaybeUninit<u8>; 24],
    }

    impl Buffer {
        #[inline]
        #[cfg_attr(feature = "no-panic", no_panic)]
        pub fn new() -> Self {
            let bytes = [MaybeUninit::<u8>::uninit(); 24];
            Buffer { bytes }
        }

        #[inline]
        #[cfg_attr(feature = "no-panic", no_panic)]
        pub fn format_finite<F: Float>(&mut self, f: F) -> &[u8] {
            unsafe {
                let n = f.write_to_ryu_buffer(self.bytes.as_mut_ptr().cast::<u8>());
                debug_assert!(n <= self.bytes.len());
                let slice = slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), n);
                slice
            }
        }
    }

    pub trait Float: Sealed {}

    pub trait Sealed: Copy {
        unsafe fn write_to_ryu_buffer(self, result: *mut u8) -> usize;
    }

    #[derive(Copy, Clone)]
    pub struct Exponent(pub isize);

    impl Sealed for Exponent {
        #[inline]
        unsafe fn write_to_ryu_buffer(self, result: *mut u8) -> usize {
            crate::pretty::write_exponent3(self.0, result)
        }
    }

    impl Float for Exponent {}

    pub fn format_exponent(k: isize) -> u8 {
        let mut buf = Buffer::new();
        let s = buf.format_finite(Exponent(k));
        s[0]
    }
}
