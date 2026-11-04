module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Array.Array
public import Aeneas.Std.StringDef
public section

namespace Aeneas.Std

@[reducible, expose, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/- TODO: -/
@[rust_type "core::fmt::Formatter"]
noncomputable opaque core.fmt.Formatter : Type

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type u) where
  fmt : SharedBorrow T → MutBorrow core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

-- TODO: move?
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

@[step]
theorem core.result.Result.unwrap.step_spec
    {T E : Type _} (inst : core.fmt.Debug E)
    (r : core.result.Result T E)
    (h : ∃ v, r = core.result.Result.Ok v) :
    core.result.Result.unwrap inst r
    ⦃ (result : T) => r = core.result.Result.Ok result ⦄ := by
  match r, h with
  | .Ok v, ⟨_, rfl⟩ =>
    simp [core.result.Result.unwrap, WP.spec_ok]

-- TODO: add pattern once we support partial monomorphization
def core.result.Result.unwrap.mut {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result (T × (T → core.result.Result T E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok x)
  | .Err _ => .fail .panic

/-- Same as `core.result.Result.unwrap.mut` but for the case where the `Ok` type is a
    mutable borrow: the backward function receives the borrowed value. -/
def core.result.Result.unwrap.mut_borrow {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result (MutBorrow T) E) :
  Std.Result (MutBorrow T × (T → core.result.Result (MutBorrow T) E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok (MutBorrow.mk x))
  | .Err _ => .fail .panic


-- TODO: this is a simplistic model
@[expose, rust_type "core::fmt::Arguments"]
def core.fmt.Arguments : Type := Unit

@[expose, rust_type "core::fmt::rt::Argument"]
def core.fmt.rt.Argument : Type := Unit

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"]
def core.fmt.Arguments.from_str : SharedBorrow Str → Result core.fmt.Arguments := fun _ => Result.ok ()

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::new"]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (_ : SharedBorrow (Std.Array Std.U8 N))
  (_ : SharedBorrow (Std.Array core.fmt.rt.Argument M)) : Result core.fmt.Arguments :=
  -- TODO
  Result.ok ()

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"]
def core.fmt.rt.Argument.new_debug
  {T : Type _} (_DebugInst : core.fmt.Debug T) (_ : SharedBorrow T) :
  Result core.fmt.rt.Argument :=
  -- TODO
  Result.ok ()

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type _) where
  fmt : SharedBorrow Self → MutBorrow core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type _) where
  fmt : SharedBorrow Self → MutBorrow core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_lower_hex"]
def core.fmt.rt.Argument.new_lower_hex
  {T : Type _} (_LowerHexInst : core.fmt.LowerHex T) (_ : SharedBorrow T) :
  Result core.fmt.rt.Argument :=
  -- TODO
  .ok ()

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : MutBorrow core.fmt.Formatter) (_ : SharedBorrow Str) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt
  (fmt : MutBorrow core.fmt.Formatter) (_ : core.fmt.Arguments) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: we should update something in the formatter, once we have a model for it
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type _} (DebugInst : core.fmt.Debug T)
  (x : SharedBorrow (SharedBorrow T)) (fmt : MutBorrow core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  DebugInst.fmt x.val fmt

@[expose, rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (_ : SharedBorrow Bool) (fmt : MutBorrow core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : SharedBorrow Unit) (fmt : MutBorrow core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::expect"]
def core.result.Result.expect {T : Type _} {E : Type _} (_DebugInst : core.fmt.Debug E)
  (r : core.result.Result T E) (_ : SharedBorrow Str) : Std.Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ =>
    /- TODO: this is a simplistic model -/
    .fail .panic

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish", simp]
def core.fmt.Formatter.debug_struct_field1_finish
  (fmt : MutBorrow core.fmt.Formatter) (_ : SharedBorrow Str) (_ : SharedBorrow Str)
  (_ : SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn))) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish", simp]
def core.fmt.Formatter.debug_struct_field2_finish (fmt : MutBorrow core.fmt.Formatter)
  (_ : SharedBorrow Str)
  (_ : SharedBorrow Str) (_ : SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)))
  (_ : SharedBorrow Str) (_ : SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn))) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field3_finish", simp]
def core.fmt.Formatter.debug_struct_field3_finish (fmt : MutBorrow core.fmt.Formatter)
  (_ : SharedBorrow Str) :
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun _ _ _ _ _ _ =>
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish", simp]
def core.fmt.Formatter.debug_struct_field4_finish (fmt : MutBorrow core.fmt.Formatter)
  (_ : SharedBorrow Str) :
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun _ _ _ _ _ _ _ _ =>
  .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field5_finish", simp]
def core.fmt.Formatter.debug_struct_field5_finish (fmt : MutBorrow core.fmt.Formatter)
  (_ : SharedBorrow Str) :
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  SharedBorrow Str → SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ _ _ _ _ _ _ _ _ _ => .ok (.Ok (), fmt.val)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish", simp]
def core.fmt.Formatter.debug_tuple_field1_finish :
  MutBorrow core.fmt.Formatter → SharedBorrow Str →
  SharedBorrow (Dyn (fun dyn => core.fmt.Debug dyn)) →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun fmt _ _ =>
  .ok (.Ok (), fmt.val)

@[expose, reducible, rust_trait_impl "core::fmt::Debug<&'0 @T>"]
def core.fmt.DebugShared {T : Type _} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug (SharedBorrow T) := {
  fmt := core.fmt.DebugShared.fmt DebugInst
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<()>"]
def core.fmt.DebugUnit : core.fmt.Debug Unit := {
  fmt := core.fmt.DebugUnit.fmt
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<bool>"]
def core.fmt.DebugBool : core.fmt.Debug Bool := {
  fmt := core.fmt.DebugBool.fmt
}

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"]
def core.fmt.rt.Argument.new_display
  {T : Type _} (_DisplayInst : core.fmt.Display T) :
  SharedBorrow T → Result core.fmt.rt.Argument :=
  -- TODO: we should at least call the `fmt` method somewhere
  fun _ => Result.ok ()

end Aeneas.Std
