module
public meta import Aeneas.Extract.Extract
public meta import Aeneas.Tactic.Step.Init
public import Aeneas.Std.Primitives
public import Aeneas.Std.Core.Pin
public section

namespace Aeneas.Std

open Result

/-!
# `Future`, `Poll`, `Context` and `Waker`

Models of the parts of `core::future` and `core::task` that hand-written `Future`
implementations use.

`Future::poll` takes a `Pin<&mut Self>` and a `&mut Context`, which Aeneas translates to
`Pin Self` and `Context` (see `core.pin.Pin`): `poll` returns the updated future and
context along with the result.

## What is (not) modelled

* A `Waker` has no observable behavior: waking is a no-op. This is the behavior of
  `Waker::noop()`. Wakers built from a `RawWaker` and its vtable are not modelled.
* A `Context` is a wrapper around a `Waker` (`Context::from_waker`, `Context::waker`). The
  unstable `Context::ext` (which holds a `&mut dyn Any`) is not modelled: this is why
  `Context` has no mutable region here, whereas Charon conservatively reports one.
* `Future.block_on` is not a Rust function: it is a specification helper, see its
  documentation for the assumption it relies on.
-/

/-- Model of `core::task::Poll` (<https://doc.rust-lang.org/std/task/enum.Poll.html>). -/
@[rust_type "core::task::poll::Poll"]
inductive core.task.poll.Poll (T : Type _) where
| Ready : T → core.task.poll.Poll T
| Pending : core.task.poll.Poll T

/-- Model of `Poll::is_ready` (<https://doc.rust-lang.org/std/task/enum.Poll.html#method.is_ready>). -/
@[expose, rust_fun "core::task::poll::{core::task::poll::Poll<@T>}::is_ready"]
def core.task.poll.Poll.is_ready {T : Type _} (self : core.task.poll.Poll T) : Result Bool :=
  match self with
  | .Ready _ => ok true
  | .Pending => ok false

@[step]
theorem core.task.poll.Poll.is_ready.spec {T : Type _} (self : core.task.poll.Poll T) :
    core.task.poll.Poll.is_ready self ⦃ b => (b = true ↔ ∃ v, self = .Ready v) ⦄ := by
  cases self <;> simp [core.task.poll.Poll.is_ready]

/-- Model of `Poll::is_pending` (<https://doc.rust-lang.org/std/task/enum.Poll.html#method.is_pending>). -/
@[expose, rust_fun "core::task::poll::{core::task::poll::Poll<@T>}::is_pending"]
def core.task.poll.Poll.is_pending {T : Type _} (self : core.task.poll.Poll T) : Result Bool :=
  match self with
  | .Ready _ => ok false
  | .Pending => ok true

@[step]
theorem core.task.poll.Poll.is_pending.spec {T : Type _} (self : core.task.poll.Poll T) :
    core.task.poll.Poll.is_pending self ⦃ b => (b = true ↔ self = .Pending) ⦄ := by
  cases self <;> simp [core.task.poll.Poll.is_pending]

/-- Model of `core::task::Waker` (<https://doc.rust-lang.org/std/task/struct.Waker.html>):
    waking has no effect, as for `Waker::noop()`. -/
@[rust_type "core::task::wake::Waker" (body := .opaque)]
structure core.task.wake.Waker where

/-- Model of `Waker::noop` (<https://doc.rust-lang.org/std/task/struct.Waker.html#method.noop>). -/
@[expose, rust_fun "core::task::wake::{core::task::wake::Waker}::noop"]
def core.task.wake.Waker.noop : Result core.task.wake.Waker :=
  ok ⟨⟩

@[step]
theorem core.task.wake.Waker.noop.spec :
    core.task.wake.Waker.noop ⦃ w => w = ⟨⟩ ⦄ := by
  simp [core.task.wake.Waker.noop]

/-- Model of `Waker::wake_by_ref` (<https://doc.rust-lang.org/std/task/struct.Waker.html#method.wake_by_ref>):
    a no-op. -/
@[expose, rust_fun "core::task::wake::{core::task::wake::Waker}::wake_by_ref"]
def core.task.wake.Waker.wake_by_ref (_self : core.task.wake.Waker) : Result Unit :=
  ok ()

@[step]
theorem core.task.wake.Waker.wake_by_ref.spec (self : core.task.wake.Waker) :
    core.task.wake.Waker.wake_by_ref self ⦃ _ => True ⦄ := by
  simp [core.task.wake.Waker.wake_by_ref]

/-- Model of `core::task::Context` (<https://doc.rust-lang.org/std/task/struct.Context.html>). -/
@[rust_type "core::task::wake::Context" (body := .opaque)]
structure core.task.wake.Context where
  currentWaker : core.task.wake.Waker

/-- Model of `Context::from_waker` (<https://doc.rust-lang.org/std/task/struct.Context.html#method.from_waker>). -/
@[expose, rust_fun "core::task::wake::{core::task::wake::Context<'a>}::from_waker"]
def core.task.wake.Context.from_waker (waker : core.task.wake.Waker) :
  Result core.task.wake.Context :=
  ok ⟨waker⟩

@[step]
theorem core.task.wake.Context.from_waker.spec (waker : core.task.wake.Waker) :
    core.task.wake.Context.from_waker waker ⦃ cx => cx.currentWaker = waker ⦄ := by
  simp [core.task.wake.Context.from_waker]

/-- Model of `Context::waker` (<https://doc.rust-lang.org/std/task/struct.Context.html#method.waker>). -/
@[expose, rust_fun "core::task::wake::{core::task::wake::Context<'a>}::waker"]
def core.task.wake.Context.waker (self : core.task.wake.Context) :
  Result core.task.wake.Waker :=
  ok self.currentWaker

@[step]
theorem core.task.wake.Context.waker.spec (self : core.task.wake.Context) :
    core.task.wake.Context.waker self ⦃ w => w = self.currentWaker ⦄ := by
  simp [core.task.wake.Context.waker]

/-- Model of the `Future` trait (<https://doc.rust-lang.org/std/future/trait.Future.html>).

    `poll` takes the future (`Pin<&mut Self>`) and the context (`&mut Context`) and returns
    the result of the poll with their new values. -/
@[rust_trait "core::future::future::Future"]
structure core.future.future.Future (Self : Type _) (Self_Output : Type _) where
  poll : core.pin.Pin Self → core.task.wake.Context →
    Result ((core.task.poll.Poll Self_Output) × (core.pin.Pin Self) × core.task.wake.Context)

/-- Run a future to completion: poll it until it returns `Ready`.

    This has no Rust counterpart; it is the Lean model of a single-task executor, like the
    `block_on` of the `futures` crate with a no-op waker. It relies on the following
    assumption, which is what makes it sound to use it as a specification of an `async`
    function: *nothing observable happens between two polls of the same future* (no other task
    runs and changes the state that the future reads, the waker has no effect). Under this
    assumption, `.await` is sequential composition and cooperative scheduling does not matter.

    The result diverges if the future stays pending forever. -/
@[expose]
def core.future.future.Future.block_on {Self Output : Type _}
  (inst : core.future.future.Future Self Output)
  (fut : core.pin.Pin Self) (cx : core.task.wake.Context) :
  Result (Output × core.pin.Pin Self) := do
  let (r, fut', cx') ← inst.poll fut cx
  match r with
  | .Ready v => ok (v, fut')
  | .Pending => core.future.future.Future.block_on inst fut' cx'
partial_fixpoint

/-- If the first poll returns `Ready`, `block_on` returns its result. -/
theorem core.future.future.Future.block_on_ready {Self Output : Type _}
  (inst : core.future.future.Future Self Output)
  {fut fut' : core.pin.Pin Self} {cx cx' : core.task.wake.Context} {v : Output}
  (h : inst.poll fut cx = ok (.Ready v, fut', cx')) :
  inst.block_on fut cx = ok (v, fut') := by
  rw [core.future.future.Future.block_on]
  simp [h]

/-- If the first poll returns `Pending`, `block_on` goes on with the updated future and context. -/
theorem core.future.future.Future.block_on_pending {Self Output : Type _}
  (inst : core.future.future.Future Self Output)
  {fut fut' : core.pin.Pin Self} {cx cx' : core.task.wake.Context}
  (h : inst.poll fut cx = ok (.Pending, fut', cx')) :
  inst.block_on fut cx = inst.block_on fut' cx' := by
  rw [core.future.future.Future.block_on]
  simp [h]

/-- `inst.Completes fut cx v fut'`: polling `fut` returns `Ready v` after finitely many `Pending`,
    and leaves the future in the state `fut'`. This is the inductive characterization of the
    terminating executions of `block_on`; it is the way to reason about `.await`: awaiting a
    future which completes is the same as running it. -/
inductive core.future.future.Future.Completes {Self Output : Type _}
  (inst : core.future.future.Future Self Output) :
  core.pin.Pin Self → core.task.wake.Context → Output → core.pin.Pin Self → Prop where
| ready {fut fut' : core.pin.Pin Self} {cx cx' : core.task.wake.Context} {v : Output} :
    inst.poll fut cx = ok (.Ready v, fut', cx') → Completes inst fut cx v fut'
| pending {fut fut1 fut' : core.pin.Pin Self} {cx cx1 : core.task.wake.Context} {v : Output} :
    inst.poll fut cx = ok (.Pending, fut1, cx1) → Completes inst fut1 cx1 v fut' →
    Completes inst fut cx v fut'

/-- A future which completes is run to completion by `block_on`. -/
theorem core.future.future.Future.Completes.block_on {Self Output : Type _}
  {inst : core.future.future.Future Self Output}
  {fut fut' : core.pin.Pin Self} {cx : core.task.wake.Context} {v : Output}
  (h : inst.Completes fut cx v fut') :
  inst.block_on fut cx = ok (v, fut') := by
  induction h with
  | ready hp => exact core.future.future.Future.block_on_ready inst hp
  | pending hp _ ih =>
    rw [core.future.future.Future.block_on_pending inst hp]
    exact ih

end Aeneas.Std
