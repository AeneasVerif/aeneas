module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u8>}::fmt", simp]
def core.fmt.num.imp.DisplayU8.fmt : SharedBorrow Std.U8 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u16>}::fmt", simp]
def core.fmt.num.imp.DisplayU16.fmt : SharedBorrow Std.U16 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u32>}::fmt", simp]
def core.fmt.num.imp.DisplayU32.fmt : SharedBorrow Std.U32 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u64>}::fmt", simp]
def core.fmt.num.imp.DisplayU64.fmt : SharedBorrow Std.U64 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u128>}::fmt", simp]
def core.fmt.num.imp.DisplayU128.fmt : SharedBorrow Std.U128 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<usize>}::fmt", simp]
def core.fmt.num.imp.DisplayUsize.fmt : SharedBorrow Std.Usize → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i8>}::fmt", simp]
def core.fmt.num.imp.DisplayI8.fmt : SharedBorrow Std.I8 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i16>}::fmt", simp]
def core.fmt.num.imp.DisplayI16.fmt : SharedBorrow Std.I16 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i32>}::fmt", simp]
def core.fmt.num.imp.DisplayI32.fmt : SharedBorrow Std.I32 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i64>}::fmt", simp]
def core.fmt.num.imp.DisplayI64.fmt : SharedBorrow Std.I64 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i128>}::fmt", simp]
def core.fmt.num.imp.DisplayI128.fmt : SharedBorrow Std.I128 → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<isize>}::fmt", simp]
def core.fmt.num.imp.DisplayIsize.fmt : SharedBorrow Std.Isize → MutBorrow core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt.val)

end Aeneas.Std
