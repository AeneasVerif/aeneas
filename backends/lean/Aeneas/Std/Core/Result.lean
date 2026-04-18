import Aeneas.Extract
import Aeneas.Std.Primitives
import Aeneas.Tactic.Step.Init
import Aeneas.Std.Core.Ops

namespace Aeneas.Std

@[rust_type "core::result::Result"]
inductive core.result.Result (T : Type u) (E : Type v) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

open Aeneas.Std.Result

/-! ## `Result<T, E>` methods

Pinned to Rust `1.85.0` (Charon pin `nightly-2026-02-07` — these methods are
stable and unchanged across recent versions). -/

/-- `Result::is_ok`: `true` when `self` is `Ok`, `false` when `Err`.

- Docs: https://doc.rust-lang.org/core/result/enum.Result.html#method.is_ok
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[simp, step_simps,
  rust_fun "core::result::{core::result::Result<@T, @E>}::is_ok" -canFail -lift]
def core.result.Result.is_ok {T E : Type}
    (self : core.result.Result T E) : Bool :=
  match self with
  | .Ok _ => true
  | .Err _ => false

/-- `Result::is_err`: `true` when `self` is `Err`. Dual of `is_ok`.

- Docs: https://doc.rust-lang.org/core/result/enum.Result.html#method.is_err
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[simp, step_simps,
  rust_fun "core::result::{core::result::Result<@T, @E>}::is_err" -canFail -lift]
def core.result.Result.is_err {T E : Type}
    (self : core.result.Result T E) : Bool :=
  match self with
  | .Ok _ => false
  | .Err _ => true

/-- `Result::unwrap_or`: returns the contained `Ok` value, or a provided default.

- Docs: https://doc.rust-lang.org/core/result/enum.Result.html#method.unwrap_or
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[step_pure_def,
  rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or" -canFail]
def core.result.Result.unwrap_or {T E : Type}
    (self : core.result.Result T E) (default : T) : T :=
  match self with
  | .Ok v => v
  | .Err _ => default

@[simp] theorem core.result.Result.unwrap_or_ok {T E : Type} (v : T) (default : T) :
    (core.result.Result.Ok v : core.result.Result T E).unwrap_or default = v := by rfl

@[simp] theorem core.result.Result.unwrap_or_err {T E : Type} (e : E) (default : T) :
    (core.result.Result.Err e : core.result.Result T E).unwrap_or default = default := by rfl

/-- `Result::map`: applies a function to the contained `Ok` value.

- Docs: https://doc.rust-lang.org/core/result/enum.Result.html#method.map
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map {T E U F : Type}
    (FnOnceInst : core.ops.function.FnOnce F T U)
    (self : core.result.Result T E) (op : F) :
    Aeneas.Std.Result (core.result.Result U E) :=
  match self with
  | .Ok v => do
    let u ← FnOnceInst.call_once op v
    .ok (.Ok u)
  | .Err e => .ok (.Err e)

/-- `Result::map_err`: applies a function to the contained `Err` value.

- Docs: https://doc.rust-lang.org/core/result/enum.Result.html#method.map_err
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/result.rs
-/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err {T E F' F : Type}
    (FnOnceInst : core.ops.function.FnOnce F E F')
    (self : core.result.Result T E) (op : F) :
    Aeneas.Std.Result (core.result.Result T F') :=
  match self with
  | .Ok v => .ok (.Ok v)
  | .Err e => do
    let f' ← FnOnceInst.call_once op e
    .ok (.Err f')

-- Note: `Try::branch` for `Result<T, E>` (the `?`-operator implementation) is
-- defined in Convert.lean because it references `core::convert::Infallible`,
-- which is declared in that file.

end Aeneas.Std
