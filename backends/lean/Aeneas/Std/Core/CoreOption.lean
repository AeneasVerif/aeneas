module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result
public import Aeneas.Std.String
public section

namespace Aeneas.Std

open Result

/-- Returns the contained `some` value. The message is ignored: on `none`, this
    fails with `Error.panic`, which is the same behavior as `unwrap`. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::expect"]
def core.option.Option.expect {T : Type _} (x : Option T) (_msg: Str) : Result T :=
  Result.ofOption x Error.panic

attribute [agrind =] Option.isSome_none Option.isSome_some

theorem core.option.Option.expect.spec {T : Type _} (x : Option T) (msg: Str) (h : x.isSome) :
  expect x msg ⦃ v => x = some v ⦄ := by
  simp only [expect, Result.ofOption]; grind

@[expose, rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type _} (x : Option T) (e : E) :
  Result (core.result.Result T E) :=
  match x with
  | some value => ok (.Ok value)
  | none => ok (.Err e)

@[simp]
theorem core.option.Option.ok_or_some {T E : Type _} (value : T) (error : E) :
  core.option.Option.ok_or (some value) error = ok (.Ok value) := rfl

@[simp]
theorem core.option.Option.ok_or_none {T E : Type _} (error : E) :
  core.option.Option.ok_or (none : Option T) error = ok (.Err error) := rfl

/-- Pure model of `Option::map`: leaves `none` untouched and maps the payload
    of `some` through `fnOnce`. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::map"]
def core.option.Option.map
  {T U F : Type _} (fnOnce : core.ops.function.FnOnce F T U)
  (x : Option T) (f : F) :
  Result (Option U) :=
  match x with
  | some value => do
      let mapped ← fnOnce.call_once f value
      ok (some mapped)
  | none => ok none

@[simp]
theorem core.option.Option.map_some
  {T U F : Type _} (fnOnce : core.ops.function.FnOnce F T U) (value : T) (f : F) :
  core.option.Option.map fnOnce (some value) f = (do
    let mapped ← fnOnce.call_once f value
    ok (some mapped)) := rfl

@[simp]
theorem core.option.Option.map_none
  {T U F : Type _} (fnOnce : core.ops.function.FnOnce F T U) (f : F) :
  core.option.Option.map fnOnce (none : Option T) f = ok (none : Option U) := rfl

/-- Step spec for `Option::map`: `post` is the postcondition of the closure, which
    `step` can infer with `+inferPost`. -/
@[step]
theorem core.option.Option.map.spec {T U F : Type _}
  (fnOnce : core.ops.function.FnOnce F T U) (x : Option T) (f : F) {post : T → U → Prop}
  (hf : ∀ value, x = some value → fnOnce.call_once f value ⦃ post value ⦄) :
  core.option.Option.map fnOnce x f ⦃ y =>
    match x with
    | none => y = none
    | some value => ∃ mapped, y = some mapped ∧ post value mapped ⦄ := by
  cases x with
  | none => simp [core.option.Option.map]
  | some value =>
    simp only [core.option.Option.map]
    apply WP.spec_bind (hf value rfl)
    intro mapped h
    simp [h]

/-- Pure model of `Option::is_some_and`: `false` on `none`, and the result of
    `fnOnce` on the payload of `some`. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::is_some_and"]
def core.option.Option.is_some_and
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F T Bool)
  (x : Option T) (f : F) :
  Result Bool :=
  match x with
  | none => ok false
  | some value => fnOnce.call_once f value

@[simp]
theorem core.option.Option.is_some_and_some
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F T Bool) (value : T) (f : F) :
  core.option.Option.is_some_and fnOnce (some value) f = fnOnce.call_once f value := rfl

@[simp]
theorem core.option.Option.is_some_and_none
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F T Bool) (f : F) :
  core.option.Option.is_some_and fnOnce (none : Option T) f = ok false := rfl

/-- Step spec for `Option::is_some_and`: `post` is the postcondition of the closure,
    which `step` can infer with `+inferPost`. -/
@[step]
theorem core.option.Option.is_some_and.spec {T F : Type _}
  (fnOnce : core.ops.function.FnOnce F T Bool) (x : Option T) (f : F)
  {post : T → Bool → Prop}
  (hf : ∀ value, x = some value → fnOnce.call_once f value ⦃ post value ⦄) :
  core.option.Option.is_some_and fnOnce x f ⦃ b =>
    match x with
    | none => b = false
    | some value => post value b ⦄ := by
  cases x with
  | none => simp [core.option.Option.is_some_and]
  | some value =>
    simp only [core.option.Option.is_some_and]
    exact hf value rfl

/-- Pure model of `bool::then`: `none` on `false`, and on `true` the result of
    `fnOnce` wrapped in `some`. -/
@[expose, rust_fun "core::bool::{bool}::then"]
def core.bool.Bool.then
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F Unit T)
  (b : Bool) (f : F) :
  Result (Option T) :=
  if b then do
    let value ← fnOnce.call_once f ()
    ok (some value)
  else ok none

@[simp]
theorem core.bool.Bool.then_true
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F Unit T) (f : F) :
  core.bool.Bool.then fnOnce true f = (do
    let value ← fnOnce.call_once f ()
    ok (some value)) := rfl

@[simp]
theorem core.bool.Bool.then_false
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F Unit T) (f : F) :
  core.bool.Bool.then fnOnce false f = ok (none : Option T) := rfl

/-- Step spec for `bool::then`: `post` is the postcondition of the closure, which
    `step` can infer with `+inferPost`. -/
@[step]
theorem core.bool.Bool.then.spec {T F : Type _}
  (fnOnce : core.ops.function.FnOnce F Unit T) (b : Bool) (f : F) {post : T → Prop}
  (hf : b = true → fnOnce.call_once f () ⦃ post ⦄) :
  core.bool.Bool.then fnOnce b f ⦃ y =>
    if b then ∃ value, y = some value ∧ post value else y = none ⦄ := by
  cases b with
  | false => simp [core.bool.Bool.then]
  | true =>
    simp only [core.bool.Bool.then]
    apply WP.spec_bind (hf rfl)
    intro value h
    simp [h]

end Aeneas.Std
