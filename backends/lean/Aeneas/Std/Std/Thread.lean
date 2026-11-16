/- `std::thread` -/
module
public import Aeneas.Std.Core.Any
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result
public import Aeneas.Tactic.Step.Init
public section

namespace Aeneas.Std

open Result

/-- Model of `JoinHandle<T>` (<https://doc.rust-lang.org/std/thread/struct.JoinHandle.html>): the
thread has already run to completion when it is spawned (see `std.thread.functions.spawn`), and the
handle holds its result. -/
@[rust_type "std::thread::join_handle::JoinHandle"]
structure std.thread.join_handle.JoinHandle (T : Type _) where
  result : T

/-- Model of `thread::spawn` (<https://doc.rust-lang.org/std/thread/fn.spawn.html>): the closure runs
to completion when the thread is spawned, and `join` returns its result.

This is sound when the threads don't communicate: the closure only reads immutable data and writes
data it owns. Then every interleaving of the threads is equivalent to this sequential execution (the
actions of two threads on disjoint data commute), so the result does not depend on the schedule.
Threads communicate through types with interior mutability (`Mutex`, atomics, channels...), which
Aeneas rejects (see issue #1525): this model is wrong for programs using them.

Failures: a panic in the closure fails the whole computation (`join` never returns `Err`), and
spawning a thread never fails. The functions which observe the progress of a thread (`is_finished`,
`park`, `Thread::unpark`...) are not modelled. -/
@[expose, rust_fun "std::thread::functions::spawn"]
def std.thread.functions.spawn {F T : Type _} (fnOnce : core.ops.function.FnOnce F Unit T)
  (f : F) : Result (std.thread.join_handle.JoinHandle T) := do
  let result ← fnOnce.call_once f ()
  ok ⟨result⟩

/-- Model of `JoinHandle::join` (<https://doc.rust-lang.org/std/thread/struct.JoinHandle.html#method.join>):
the result of the closure. The `Err` case (the thread panicked) is not modelled: a panic is a failure
of `spawn`. The universe levels of `Dyn` are fixed so that they can be inferred in the generated code. -/
@[expose, rust_fun "std::thread::join_handle::{std::thread::join_handle::JoinHandle<@T>}::join"]
def std.thread.join_handle.JoinHandle.join {T : Type _}
  (h : std.thread.join_handle.JoinHandle T) :
  Result (core.result.Result T (Dyn.{0, 0} (fun (_dyn : Type) => core.any.Any _dyn))) :=
  ok (.Ok h.result)

@[simp]
theorem std.thread.join_handle.JoinHandle.join_mk {T : Type _} (result : T) :
  std.thread.join_handle.JoinHandle.join ⟨result⟩ = ok (.Ok result) := rfl

/-- Step spec for `thread::spawn`: `post` is the postcondition of the closure, which `step` can infer
with `+inferPost`. -/
@[step]
theorem std.thread.functions.spawn.spec {F T : Type _}
  (fnOnce : core.ops.function.FnOnce F Unit T) (f : F) {post : T → Prop}
  (hf : fnOnce.call_once f () ⦃ post ⦄) :
  std.thread.functions.spawn fnOnce f ⦃ h => post h.result ⦄ := by
  unfold std.thread.functions.spawn
  apply WP.spec_bind hf
  intro result hresult
  simp [hresult]

/-- Step spec for `JoinHandle::join`: the result is `Ok` of the result of the closure. -/
@[step]
theorem std.thread.join_handle.JoinHandle.join.spec {T : Type _}
  (h : std.thread.join_handle.JoinHandle T) :
  std.thread.join_handle.JoinHandle.join h ⦃ r => r = .Ok h.result ⦄ := by
  simp [std.thread.join_handle.JoinHandle.join]

/-! ## Scoped threads -/

/-- Model of `Scope` (<https://doc.rust-lang.org/std/thread/struct.Scope.html>): nothing. The
threads spawned in a scope run to completion when they are spawned, so the scope has no state. -/
@[rust_type "std::thread::scoped::Scope"]
structure std.thread.scoped.Scope where

/-- Model of `ScopedJoinHandle<T>`
(<https://doc.rust-lang.org/std/thread/struct.ScopedJoinHandle.html>): as for `JoinHandle`, the
handle holds the result of the thread. -/
@[rust_type "std::thread::scoped::ScopedJoinHandle"]
structure std.thread.scoped.ScopedJoinHandle (T : Type _) where
  result : T

/-- Model of `thread::scope` (<https://doc.rust-lang.org/std/thread/fn.scope.html>): the closure is
called with a scope, and the threads it spawns have already run to completion (and are joined) when
it returns. As for `std.thread.functions.spawn`, this is sound when the threads do not communicate:
they read shared immutable data and write disjoint data which they own. A thread which panics makes
`scope` panic, as in Rust. -/
@[expose, rust_fun "std::thread::scoped::scope"]
def std.thread.scoped.scope {F T : Type _}
  (fnOnce : core.ops.function.FnOnce F std.thread.scoped.Scope T) (f : F) : Result T :=
  fnOnce.call_once f ⟨⟩

/-- Model of `Scope::spawn` (<https://doc.rust-lang.org/std/thread/struct.Scope.html#method.spawn>):
the closure runs to completion when the thread is spawned (see `std.thread.functions.spawn`). -/
@[expose, rust_fun "std::thread::scoped::{std::thread::scoped::Scope<'scope, 'env>}::spawn"]
def std.thread.scoped.Scope.spawn {F T : Type _} (fnOnce : core.ops.function.FnOnce F Unit T)
  (_s : std.thread.scoped.Scope) (f : F) : Result (std.thread.scoped.ScopedJoinHandle T) := do
  let result ← fnOnce.call_once f ()
  ok ⟨result⟩

/-- Model of `ScopedJoinHandle::join`
(<https://doc.rust-lang.org/std/thread/struct.ScopedJoinHandle.html#method.join>): the result of the
closure, see `std.thread.join_handle.JoinHandle.join`. -/
@[expose, rust_fun
  "std::thread::scoped::{std::thread::scoped::ScopedJoinHandle<'scope, @T>}::join"]
def std.thread.scoped.ScopedJoinHandle.join {T : Type _}
  (h : std.thread.scoped.ScopedJoinHandle T) :
  Result (core.result.Result T (Dyn.{0, 0} (fun (_dyn : Type) => core.any.Any _dyn))) :=
  ok (.Ok h.result)

@[simp]
theorem std.thread.scoped.ScopedJoinHandle.join_mk {T : Type _} (result : T) :
  std.thread.scoped.ScopedJoinHandle.join ⟨result⟩ = ok (.Ok result) := rfl

/-- Step spec for `thread::scope`: `post` is the postcondition of the closure, which `step` can infer
with `+inferPost`. -/
@[step]
theorem std.thread.scoped.scope.spec {F T : Type _}
  (fnOnce : core.ops.function.FnOnce F std.thread.scoped.Scope T) (f : F) {post : T → Prop}
  (hf : fnOnce.call_once f ⟨⟩ ⦃ post ⦄) :
  std.thread.scoped.scope fnOnce f ⦃ r => post r ⦄ := hf

/-- Step spec for `Scope::spawn`. -/
@[step]
theorem std.thread.scoped.Scope.spawn.spec {F T : Type _}
  (fnOnce : core.ops.function.FnOnce F Unit T) (s : std.thread.scoped.Scope) (f : F)
  {post : T → Prop} (hf : fnOnce.call_once f () ⦃ post ⦄) :
  std.thread.scoped.Scope.spawn fnOnce s f ⦃ h => post h.result ⦄ := by
  unfold std.thread.scoped.Scope.spawn
  apply WP.spec_bind hf
  intro result hresult
  simp [hresult]

/-- Step spec for `ScopedJoinHandle::join`. -/
@[step]
theorem std.thread.scoped.ScopedJoinHandle.join.spec {T : Type _}
  (h : std.thread.scoped.ScopedJoinHandle T) :
  std.thread.scoped.ScopedJoinHandle.join h ⦃ r => r = .Ok h.result ⦄ := by
  simp [std.thread.scoped.ScopedJoinHandle.join]

end Aeneas.Std
