-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [builtin]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace builtin

/- [builtin::clone_bool]:
   Source: 'tests/src/builtin.rs', lines 6:0-8:1 -/
def clone_bool (x : Bool) : Result Bool :=
  ok (core.clone.impls.CloneBool.clone x)

/- [builtin::clone_u32]:
   Source: 'tests/src/builtin.rs', lines 10:0-12:1 -/
def clone_u32 (x : U32) : Result U32 :=
  ok (core.clone.impls.CloneU32.clone x)

/- [builtin::into_from]:
   Source: 'tests/src/builtin.rs', lines 14:0-16:1 -/
def into_from
  {T : Type} {U : Type} (coreconvertFromInst : core.convert.From U T) (x : T) :
  Result U
  :=
  core.convert.IntoFrom.into coreconvertFromInst x

/- [builtin::into_same]:
   Source: 'tests/src/builtin.rs', lines 18:0-20:1 -/
def into_same {T : Type} (x : T) : Result T :=
  core.convert.IntoFrom.into (core.convert.FromSame T) x

/- [builtin::from_same]:
   Source: 'tests/src/builtin.rs', lines 22:0-24:1 -/
def from_same {T : Type} (x : T) : Result T :=
  ok (core.convert.FromSame.from_ x)

/- [builtin::copy]:
   Source: 'tests/src/builtin.rs', lines 26:0-28:1 -/
def copy
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) (x : T) : Result T :=
  ok x

/- [builtin::u32_from_le_bytes]:
   Source: 'tests/src/builtin.rs', lines 30:0-32:1 -/
def u32_from_le_bytes (x : Array U8 4#usize) : Result U32 :=
  ok (core.num.U32.from_le_bytes x)

/- [builtin::u32_to_le_bytes]:
   Source: 'tests/src/builtin.rs', lines 34:0-36:1 -/
def u32_to_le_bytes (x : U32) : Result (Array U8 4#usize) :=
  ok (core.num.U32.to_le_bytes x)

/- [builtin::use_debug_clause]:
   Source: 'tests/src/builtin.rs', lines 38:0-38:49 -/
def use_debug_clause
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) (t : T) : Result Unit :=
  ok ()

end builtin
