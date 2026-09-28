-- The user-filled copy of [FunsExternal_Template.lean]: the local modules
-- import this file, and re-extraction does not touch it.
--
-- The bucket mixes a transparent external trait decl and an opaque external
-- function, and must still come out as a single file, never a [Part]/[Opaques]
-- chain. Only [macrolib::helper] needs filling in; the trait decl below is
-- copied from the template as is.
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/-- Trait declaration: [core::fmt::Write]
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 123:0-123:15
    Name pattern: [core::fmt::Write]
    Visibility: public -/
@[rust_trait "core::fmt::Write"]
structure core.fmt.Write (Self : Type) where
  write_str : Self → Str → Result ((core.result.Result Unit core.fmt.Error)
    × Self)

/-- [macrolib::helper]:
    Source: 'macrolib/src/lib.rs', lines 22:0-22:28
    Name pattern: [macrolib::helper]
    Visibility: public -/
@[rust_fun "macrolib::helper"]
def macrolib.helper (x : Std.U32) : Result Std.U32 :=
  x + 7#u32
