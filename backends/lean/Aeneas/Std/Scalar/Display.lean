import Aeneas.Std.Scalar.Core
import Aeneas.Std.Core.Fmt

namespace Aeneas.Std

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<u8>}::fmt", simp]
def core.fmt.num.imp.DisplayU8.fmt : Std.U8 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<u16>}::fmt", simp]
def core.fmt.num.imp.DisplayU16.fmt : Std.U16 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<u32>}::fmt", simp]
def core.fmt.num.imp.DisplayU32.fmt : Std.U32 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<u64>}::fmt", simp]
def core.fmt.num.imp.DisplayU64.fmt : Std.U64 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<u128>}::fmt", simp]
def core.fmt.num.imp.DisplayU128.fmt : Std.U128 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<usize>}::fmt", simp]
def core.fmt.num.imp.DisplayUsize.fmt : Std.Usize → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<i8>}::fmt", simp]
def core.fmt.num.imp.DisplayI8.fmt : Std.I8 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<i16>}::fmt", simp]
def core.fmt.num.imp.DisplayI16.fmt : Std.I16 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<i32>}::fmt", simp]
def core.fmt.num.imp.DisplayI32.fmt : Std.I32 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<i64>}::fmt", simp]
def core.fmt.num.imp.DisplayI64.fmt : Std.I64 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<i128>}::fmt", simp]
def core.fmt.num.imp.DisplayI128.fmt : Std.I128 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::imp::{core::fmt::Display<isize>}::fmt", simp]
def core.fmt.num.imp.DisplayIsize.fmt : Std.Isize → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

end Aeneas.Std
