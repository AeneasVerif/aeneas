module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Core.Ops
@[expose] public section

/-!
# Trait implementations for `Option`, and `PhantomData`
-/

namespace Aeneas.Std

open Result

@[rust_fun "core::option::{core::option::Option<@T>}::map"]
def core.option.Option.map {T U F : Type} (FnOnceInst : core.ops.function.FnOnce F T U)
    (x : Option T) (f : F) : Result (Option U) :=
  match x with
  | none => ok none
  | some v => do ok (some (← FnOnceInst.call_once f v))

@[rust_fun "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone {T : Type}
    (cloneCloneInst : core.clone.Clone T) (x : Option T) : Result (Option T) :=
  match x with
  | none => ok none
  | some v => do ok (some (← cloneCloneInst.clone v))

@[reducible, rust_trait_impl "core::clone::Clone<core::option::Option<@T>>"]
def core.option.Option.Insts.CoreCloneClone {T : Type} (cloneCloneInst : core.clone.Clone T) :
    core.clone.Clone (Option T) := {
  clone := core.option.Option.Insts.CoreCloneClone.clone cloneCloneInst
}

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (x y : Option T) : Result Bool :=
  match x, y with
  | none, none => ok true
  | some a, some b => cmpPartialEqInst.eq a b
  | _, _ => ok false

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>"]
def core.option.Option.Insts.CoreCmpPartialEqOption {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T) (Option T) := {
  eq := core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst
}

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type) (_ : Option Never) : Result (Option T) :=
  ok none

@[reducible, rust_trait_impl
  "core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever (T : Type) :
    core.ops.try_trait.FromResidual (Option T) (Option Never) := {
  from_residual := core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual T
}

@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} (x : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match x with
  | none => ok (.Break none)
  | some v => ok (.Continue v)

@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::from_output"]
def core.option.Option.Insts.CoreOpsTry_traitTry.from_output {T : Type} (v : T) :
    Result (Option T) :=
  ok (some v)

@[reducible, rust_trait_impl "core::ops::try_trait::Try<core::option::Option<@T>>"]
def core.option.Option.Insts.CoreOpsTry_traitTry (T : Type) :
    core.ops.try_trait.Try (Option T) T (Option Never) := {
  FromResidualInst := core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever T
  from_output := core.option.Option.Insts.CoreOpsTry_traitTry.from_output
  branch := core.option.Option.Insts.CoreOpsTry_traitTry.branch
}

/-- Formatting is not modeled: it always succeeds and leaves the formatter
unchanged, like the other `Debug` implementations of the library. -/
@[rust_fun "core::option::{core::fmt::Debug<core::option::Option<@T>>}::fmt"]
def core.option.Option.Insts.CoreFmtDebug.fmt {T : Type} (_fmtDebugInst : core.fmt.Debug T)
    (_ : Option T) (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<core::option::Option<@T>>"]
def core.option.Option.Insts.CoreFmtDebug {T : Type} (fmtDebugInst : core.fmt.Debug T) :
    core.fmt.Debug (Option T) := {
  fmt := core.option.Option.Insts.CoreFmtDebug.fmt fmtDebugInst
}

@[reducible, rust_type "core::marker::PhantomData"]
def core.marker.PhantomData (_T : Type) := Unit

@[rust_fun "core::fmt::{core::fmt::Debug<core::marker::PhantomData<@T>>}::fmt"]
def core.marker.PhantomData.Insts.CoreFmtDebug.fmt {T : Type} (_ : core.marker.PhantomData T)
    (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<core::marker::PhantomData<@T>>"]
def core.marker.PhantomData.Insts.CoreFmtDebug (T : Type) :
    core.fmt.Debug (core.marker.PhantomData T) := {
  fmt := core.marker.PhantomData.Insts.CoreFmtDebug.fmt
}

attribute [step_simps] core.option.Option.map core.option.Option.Insts.CoreCloneClone.clone
  core.option.Option.Insts.CoreCmpPartialEqOption.eq
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
  core.option.Option.Insts.CoreOpsTry_traitTry.branch
  core.option.Option.Insts.CoreOpsTry_traitTry.from_output

end Aeneas.Std
