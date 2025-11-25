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

end Aeneas.Std
