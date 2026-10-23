module
public import Aeneas.Data.Discriminant
public section

open Aeneas.Std

namespace DiscriminantSignedTests

  -- A reduced real consumer: miniz_oxide 0.9.1's #[repr(i8)] TINFLStatus.
  @[discriminant i8 [-4, -3, -2, -1, 0, 1, 2]]
  inductive InflateStatus where
  | failedCannotMakeProgress | badParam | adler32Mismatch | failed
  | done | needsMoreInput | hasMoreOutput

  #guard (read_discriminant InflateStatus.failedCannotMakeProgress).val = -4
  #guard (read_discriminant InflateStatus.badParam).val = -3
  #guard (read_discriminant InflateStatus.adler32Mismatch).val = -2
  #guard (read_discriminant InflateStatus.failed).val = -1
  #guard (read_discriminant InflateStatus.done).val = 0
  #guard (read_discriminant InflateStatus.needsMoreInput).val = 1
  #guard (read_discriminant InflateStatus.hasMoreOutput).val = 2

  -- Rust permits negative discriminants for signed repr types. Exercise the
  -- attribute parser, signed literals at the bounds, and generated instances.
  @[discriminant i8 [-128, -1, 0, 127]]
  inductive SignedI8 where
  | min | negative | zero | max

  @[discriminant i16 [-32768, -1, 0, 32767]]
  inductive SignedI16 where
  | min | negative | zero | max

  @[discriminant i32 [-2147483648, -1, 0, 2147483647]]
  inductive SignedI32 where
  | min | negative | zero | max

  @[discriminant i64 [-9223372036854775808, -1, 0, 9223372036854775807]]
  inductive SignedI64 where
  | min | negative | zero | max

  @[discriminant i128 [-170141183460469231731687303715884105728, -1, 0,
      170141183460469231731687303715884105727]]
  inductive SignedI128 where
  | min | negative | zero | max

  @[discriminant isize [-1, 0, 1]]
  inductive SignedIsize where
  | negative | zero | positive

  #guard (read_discriminant SignedI8.min).val = -128
  #guard (read_discriminant SignedI8.negative).val = -1
  #guard (read_discriminant SignedI8.zero).val = 0
  #guard (read_discriminant SignedI8.max).val = 127
  #guard (read_discriminant SignedI16.min).val = -32768
  #guard (read_discriminant SignedI16.max).val = 32767
  #guard (read_discriminant SignedI32.min).val = -2147483648
  #guard (read_discriminant SignedI32.max).val = 2147483647
  #guard (read_discriminant SignedI64.min).val = -9223372036854775808
  #guard (read_discriminant SignedI64.max).val = 9223372036854775807
  #guard (read_discriminant SignedI128.min).val = -170141183460469231731687303715884105728
  #guard (read_discriminant SignedI128.max).val = 170141183460469231731687303715884105727
  #guard (read_discriminant SignedIsize.negative).val = -1
  #guard (read_discriminant SignedIsize.zero).val = 0
  #guard (read_discriminant SignedIsize.positive).val = 1

  -- The existing unsigned syntax and implicit constructor numbering still work.
  @[discriminant u8 [0, 255]]
  inductive UnsignedBounds where
  | min | max

  @[discriminant u16]
  inductive UnsignedDefault where
  | first | second

  #guard (read_discriminant UnsignedBounds.min).val = 0
  #guard (read_discriminant UnsignedBounds.max).val = 255
  #guard (read_discriminant UnsignedDefault.first).val = 0
  #guard (read_discriminant UnsignedDefault.second).val = 1

  /-- error: Negative discriminant -1 is invalid for an unsigned scalar -/
  #guard_msgs in
  @[discriminant u8 [-1]]
  inductive NegativeUnsigned where
  | value

end DiscriminantSignedTests
