import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Result
import Aeneas.Std.Array.Array

namespace Aeneas.Std

@[reducible, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/- TODO: -/
@[rust_type "core::fmt::Formatter"]
axiom core.fmt.Formatter : Type

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type u) where
  fmt : T → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

-- TODO: move?
@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

-- TODO: add pattern once we support partial monomorphization
def core.result.Result.unwrap.mut {T E : Type}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result (T × (T → core.result.Result T E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok x)
  | .Err _ => .fail .panic


-- TODO: this is a simplistic model
@[rust_type "core::fmt::Arguments"]
def core.fmt.Arguments : Type := Unit

@[rust_type "core::fmt::rt::Argument"]
def core.fmt.rt.Argument : Type := Unit

@[rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"]
def core.fmt.Arguments.from_str : Str → Result core.fmt.Arguments := fun _ => Result.ok ()

@[rust_fun "core::fmt::{core::fmt::Arguments<'a>}::new"]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (_ : Std.Array Std.U8 N) (_ : Std.Array core.fmt.rt.Argument M) : Result core.fmt.Arguments :=
  -- TODO
  Result.ok ()

@[rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"]
def core.fmt.rt.Argument.new_debug
  {T : Type} (_DebugInst : core.fmt.Debug T) (_ : T) : Result core.fmt.rt.Argument :=
  -- TODO
  Result.ok ()

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (_ : Str) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt
  (fmt : core.fmt.Formatter) (_ : core.fmt.Arguments) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: we should update something in the formatter, once we have a model for it
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  DebugInst.fmt x fmt

@[rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (_ : Bool) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : Unit) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::expect"]
def core.result.Result.expect {T : Type} {E : Type} (_DebugInst : core.fmt.Debug E)
  (r : core.result.Result T E) (_ : Str) : Std.Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ =>
    /- TODO: this is a simplistic model -/
    .fail .panic

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish", simp]
def core.fmt.Formatter.debug_struct_field1_finish
  (fmt : core.fmt.Formatter) (_ : Str) (_ : Str) (_ : Dyn (fun _dyn => core.fmt.Debug _dyn)) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish", simp]
def core.fmt.Formatter.debug_struct_field4_finish :
  core.fmt.Formatter → Str → Str → Dyn (fun _dyn => core.fmt.Debug _dyn)
    → Str → Dyn (fun _dyn => core.fmt.Debug _dyn) → Str →
    Dyn (fun _dyn => core.fmt.Debug _dyn) → Str → Dyn (fun _dyn => core.fmt.Debug _dyn)
    → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model
  fun fmt _ _ _ _ _ _ _ _ _ =>
  .ok (.Ok (), fmt)

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish"]
def core.fmt.Formatter.debug_tuple_field1_finish :
  core.fmt.Formatter → Str → Dyn (fun _dyn => core.fmt.Debug _dyn) →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model
  fun fmt _ _ =>
  .ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<&'0 @T>"]
def core.fmt.DebugShared {T : Type} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug T := {
  fmt := core.fmt.DebugShared.fmt DebugInst
}

@[reducible, rust_trait_impl "core::fmt::Debug<()>"]
def core.fmt.DebugUnit : core.fmt.Debug Unit := {
  fmt := core.fmt.DebugUnit.fmt
}

@[reducible, rust_trait_impl "core::fmt::Debug<bool>"]
def core.fmt.DebugBool : core.fmt.Debug Bool := {
  fmt := core.fmt.DebugBool.fmt
}

@[rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"]
def core.fmt.rt.Argument.new_display
  {T : Type} (_DisplayInst : core.fmt.Display T) :
  T → Result core.fmt.rt.Argument :=
  -- TODO: we should at least call the `fmt` method somewhere
  fun _ => Result.ok ()

end Aeneas.Std
