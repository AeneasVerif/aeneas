import Aeneas.Std.Scalar.Core
import Aeneas.Std.Core.Fmt

namespace Aeneas.Std

@[rust_fun "core::fmt::num::{core::fmt::LowerHex<u16>}::fmt"]
def core.fmt.num.LowerHexU16.fmt (_ : U16) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<u8>}::fmt"]
def core.fmt.num.DebugU8.fmt (_ : U8) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<u16>}::fmt"]
def core.fmt.num.DebugU16.fmt (_ : U16) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<u32>}::fmt"]
def core.fmt.num.DebugU32.fmt (_ : U32) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<u64>}::fmt"]
def core.fmt.num.DebugU64.fmt (_ : U64) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<u128>}::fmt"]
def core.fmt.num.DebugU128.fmt (_ : U128) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<usize>}::fmt"]
def core.fmt.num.DebugUsize.fmt (_ : Usize) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<u8>"]
def core.fmt.DebugU8 : core.fmt.Debug U8 := {
  fmt := core.fmt.num.DebugU8.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<u16>"]
def core.fmt.DebugU16 : core.fmt.Debug U16 := {
  fmt := core.fmt.num.DebugU16.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<u32>"]
def core.fmt.DebugU32 : core.fmt.Debug U32 := {
  fmt := core.fmt.num.DebugU32.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<u64>"]
def core.fmt.DebugU64 : core.fmt.Debug U64 := {
  fmt := core.fmt.num.DebugU64.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<u128>"]
def core.fmt.DebugU128 : core.fmt.Debug U128 := {
  fmt := core.fmt.num.DebugU128.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<usize>"]
def core.fmt.DebugUsize : core.fmt.Debug Usize := {
  fmt := core.fmt.num.DebugUsize.fmt
}

@[rust_fun "core::fmt::num::{core::fmt::Debug<i8>}::fmt"]
def core.fmt.num.DebugI8.fmt (_ : I8) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<i16>}::fmt"]
def core.fmt.num.DebugI16.fmt (_ : I16) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<i32>}::fmt"]
def core.fmt.num.DebugI32.fmt (_ : I32) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<i64>}::fmt"]
def core.fmt.num.DebugI64.fmt (_ : I64) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<i128>}::fmt"]
def core.fmt.num.DebugI128.fmt (_ : I128) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::num::{core::fmt::Debug<isize>}::fmt"]
def core.fmt.num.DebugIsize.fmt (_ : Isize) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<i8>"]
def core.fmt.DebugI8 : core.fmt.Debug I8 := {
  fmt := core.fmt.num.DebugI8.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<i16>"]
def core.fmt.DebugI16 : core.fmt.Debug I16 := {
  fmt := core.fmt.num.DebugI16.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<i32>"]
def core.fmt.DebugI32 : core.fmt.Debug I32 := {
  fmt := core.fmt.num.DebugI32.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<i64>"]
def core.fmt.DebugI64 : core.fmt.Debug I64 := {
  fmt := core.fmt.num.DebugI64.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<i128>"]
def core.fmt.DebugI128 : core.fmt.Debug I128 := {
  fmt := core.fmt.num.DebugI128.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<isize>"]
def core.fmt.DebugIsize : core.fmt.Debug Isize := {
  fmt := core.fmt.num.DebugIsize.fmt
}

end Aeneas.Std
