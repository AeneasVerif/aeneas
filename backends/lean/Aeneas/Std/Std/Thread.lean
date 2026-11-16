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

end Aeneas.Std
