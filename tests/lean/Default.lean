-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [default]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace default

/- [default::f0]:
   Source: 'tests/src/default.rs', lines 3:0-5:1 -/
def f0 : Result Unit :=
  do
  let _ ← core.default.DefaultArrayEmpty.default U32
  ok ()

/- [default::f1]:
   Source: 'tests/src/default.rs', lines 7:0-9:1 -/
def f1 : Result Unit :=
  do
  let _ ← core.default.DefaultArray.default 1#usize core.default.DefaultU32
  ok ()

/- [default::f2]:
   Source: 'tests/src/default.rs', lines 11:0-13:1 -/
def f2 : Result Unit :=
  do
  let _ ← core.default.DefaultArray.default 2#usize core.default.DefaultU32
  ok ()

end default
