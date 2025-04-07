import Aeneas.Std.Scalar.Core
import Aeneas.Std.Default
import Aeneas.Std.Scalar.Notations

namespace Aeneas.Std

open Result

/- [core::default::{core::default::Default for u32}::default]:
   Source: '/rustc/library/core/src/default.rs', lines 156:12-156:30
   Name pattern: [core::default::{core::default::Default<u32>}::default] -/
@[simp, scalar_tac_simps] def core.default.DefaultU8.default : U8 := 0#u8
@[simp, scalar_tac_simps] def core.default.DefaultU16.default : U16 := 0#u16
@[simp, scalar_tac_simps] def core.default.DefaultU32.default : U32 := 0#u32
@[simp, scalar_tac_simps] def core.default.DefaultU64.default : U64 := 0#u64
@[simp, scalar_tac_simps] def core.default.DefaultU128.default : U128 := 0#u128
@[simp, scalar_tac_simps] def core.default.DefaultUsize.default : Usize := 0#usize

@[simp, scalar_tac_simps] def core.default.DefaultI8.default : I8 := 0#i8
@[simp, scalar_tac_simps] def core.default.DefaultI16.default : I16 := 0#i16
@[simp, scalar_tac_simps] def core.default.DefaultI32.default : I32 := 0#i32
@[simp, scalar_tac_simps] def core.default.DefaultI64.default : I64 := 0#i64
@[simp, scalar_tac_simps] def core.default.DefaultI128.default : I128 := 0#i128
@[simp, scalar_tac_simps] def core.default.DefaultIsize.default : Isize := 0#isize

/- Trait implementation: [core::default::{core::default::Default for u32}#7]
   Source: '/rustc/library/core/src/default.rs', lines 153:8-153:27
   Name pattern: [core::default::Default<u32>] -/
@[reducible] def core.default.DefaultU8 : core.default.Default U8 := {
  default := ok core.default.DefaultU8.default }

@[reducible] def core.default.DefaultU16 : core.default.Default U16 := {
  default := ok core.default.DefaultU16.default }

@[reducible] def core.default.DefaultU32 : core.default.Default U32 := {
  default := ok core.default.DefaultU32.default }

@[reducible] def core.default.DefaultU64 : core.default.Default U64 := {
  default := ok core.default.DefaultU64.default }

@[reducible] def core.default.DefaultU128 : core.default.Default U128 := {
  default := ok core.default.DefaultU128.default }

@[reducible] def core.default.DefaultUsize : core.default.Default Usize := {
  default := ok core.default.DefaultUsize.default }

@[reducible] def core.default.DefaultI8 : core.default.Default I8 := {
  default := ok core.default.DefaultI8.default }

@[reducible] def core.default.DefaultI16 : core.default.Default I16 := {
  default := ok core.default.DefaultI16.default }

@[reducible] def core.default.DefaultI32 : core.default.Default I32 := {
  default := ok core.default.DefaultI32.default }

@[reducible] def core.default.DefaultI64 : core.default.Default I64 := {
  default := ok core.default.DefaultI64.default }

@[reducible] def core.default.DefaultI128 : core.default.Default I128 := {
  default := ok core.default.DefaultI128.default }

@[reducible] def core.default.DefaultIsize : core.default.Default Isize := {
  default := ok core.default.DefaultIsize.default }


end Aeneas.Std
