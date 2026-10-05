//@ [!lean] skip
// Verbatim excerpt of https://github.com/dtolnay/ryu at
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
}
