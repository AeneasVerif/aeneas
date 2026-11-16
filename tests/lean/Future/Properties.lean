module
public import Aeneas
public import Future.Future
public section

open Aeneas Aeneas.Std Result core.future.future core.task.poll core.task.wake

/-! Proofs about the futures of `tests/src/future.rs`, and about running them to completion. -/

namespace future

/-- A successful spec gives an equation. -/
theorem spec_ok_exists {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret y => exact ⟨y, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

/-! ## The documentation examples of `Poll::is_ready` and `Poll::is_pending` -/

theorem is_ready_spec (poll : core.task.poll.Poll Std.Usize) :
    is_ready poll ⦃ b => (b = true ↔ ∃ v, poll = .Ready v) ⦄ := by
  unfold is_ready; step*

theorem is_pending_spec (poll : core.task.poll.Poll Std.Usize) :
    is_pending poll ⦃ b => (b = true ↔ poll = .Pending) ⦄ := by
  unfold is_pending; step*

/-! ## `Ready` -/

/-- A `Ready` future which holds a value returns it, and is empty afterwards. -/
theorem ready_poll_spec {T : Type _} (self : core.pin.Pin (Ready T)) (cx : Context) (v : T)
    (h : self.pointer = some v) :
    Ready.Insts.CoreFutureFutureFuture.poll self cx ⦃ r =>
      r = (.Ready v, ⟨none⟩, cx) ⦄ := by
  unfold Ready.Insts.CoreFutureFutureFuture.poll
  simp [h, core.option.Option.take, core.option.Option.unwrap, Result.ofOption]

/-- Polling a `Ready` future which was already polled panics. -/
theorem ready_poll_fail {T : Type _} (self : core.pin.Pin (Ready T)) (cx : Context)
    (h : self.pointer = none) :
    Ready.Insts.CoreFutureFutureFuture.poll self cx = fail .panic := by
  unfold Ready.Insts.CoreFutureFutureFuture.poll
  simp [h, core.option.Option.take, core.option.Option.unwrap, Result.ofOption]

/-! ## `Countdown` -/

/-- The poll of a `Countdown`: it is ready (with `42`) when the counter is `0`, and otherwise it
decrements the counter and is pending. -/
theorem countdown_poll_spec (self : core.pin.Pin Countdown) (cx : Context) :
    Countdown.Insts.CoreFutureFutureFutureU32.poll self cx ⦃ r fut' cx' =>
      (self.pointer.val = 0 ∧ r = .Ready 42#u32 ∧ fut' = self ∧ cx' = cx) ∨
      (self.pointer.val ≠ 0 ∧ r = .Pending ∧ fut'.pointer.val + 1 = self.pointer.val ∧ cx' = cx) ⦄ := by
  unfold Countdown.Insts.CoreFutureFutureFutureU32.poll
  dsimp only
  split
  · rename_i h
    simp [h]
  · rename_i h
    step*

/-- A `Countdown` future which is pending `n` times is run to completion by `block_on`, and returns
`42`. This is a proof by induction on the number of polls. -/
theorem countdown_block_on (k : Nat) : ∀ (n : Std.U32) (cx : Context), n.val = k →
    Future.block_on Countdown.Insts.CoreFutureFutureFutureU32 ⟨n⟩ cx ⦃ r _ => r = 42#u32 ⦄ := by
  induction k with
  | zero =>
    intro n cx hn
    rw [Future.block_on]
    step with countdown_poll_spec as ⟨ r, hr ⟩
    rcases hr with ⟨_, h1, _⟩ | ⟨hne, _⟩
    · simp [h1]
    · omega
  | succ k ih =>
    intro n cx hn
    rw [Future.block_on]
    step with countdown_poll_spec as ⟨ r, hr ⟩
    rcases hr with ⟨h0, _⟩ | ⟨_, h1, h2, _⟩
    · omega
    · simp only [h1]
      exact ih r.2.1.pointer r.2.2 (by omega)


/-- The same, with the characterization of the terminating executions of `block_on`. -/
theorem countdown_completes (k : Nat) : ∀ (n : Std.U32) (cx : Context), n.val = k →
    Countdown.Insts.CoreFutureFutureFutureU32.Completes ⟨n⟩ cx 42#u32 ⟨0#u32⟩ := by
  induction k with
  | zero =>
    intro n cx hn
    obtain ⟨⟨r, fut', cx'⟩, heq, hr⟩ := spec_ok_exists (countdown_poll_spec ⟨n⟩ cx)
    rcases hr with ⟨_, h1, h2, h3⟩ | ⟨hne, _⟩
    · have hn0 : n = 0#u32 := by scalar_tac
      subst hn0 h1 h2 h3
      exact .ready heq
    · simp at hne
      omega
  | succ k ih =>
    intro n cx hn
    obtain ⟨⟨r, fut', cx'⟩, heq, hr⟩ := spec_ok_exists (countdown_poll_spec ⟨n⟩ cx)
    rcases hr with ⟨h0, _⟩ | ⟨_, h1, h2, h3⟩
    · simp at h0
      omega
    · subst h1 h3
      exact .pending heq (ih fut'.pointer cx' (by simp at h2 ⊢; omega))

/-! ## `YieldNow` -/

/-- The first poll of a `YieldNow` future asks to be polled again (a no-op for the waker, see the
model of `Waker`) and is pending. -/
theorem yield_now_poll_pending (self : core.pin.Pin YieldNow) (cx : Context)
    (h : self.pointer = false) :
    YieldNow.Insts.CoreFutureFutureFutureTuple.poll self cx = ok (.Pending, ⟨true⟩, cx) := by
  unfold YieldNow.Insts.CoreFutureFutureFutureTuple.poll
  simp [h, core.task.wake.Context.waker, core.task.wake.Waker.wake_by_ref]

theorem yield_now_poll_ready (self : core.pin.Pin YieldNow) (cx : Context)
    (h : self.pointer = true) :
    YieldNow.Insts.CoreFutureFutureFutureTuple.poll self cx = ok (.Ready (), self, cx) := by
  unfold YieldNow.Insts.CoreFutureFutureFutureTuple.poll
  simp [h]

/-- A `YieldNow` future is pending once, then ready: it completes. -/
theorem yield_now_completes (cx : Context) :
    YieldNow.Insts.CoreFutureFutureFutureTuple.Completes ⟨false⟩ cx () ⟨true⟩ :=
  .pending (yield_now_poll_pending ⟨false⟩ cx rfl) (.ready (yield_now_poll_ready ⟨true⟩ cx rfl))

/-! ## `AddOne`: awaiting is sequential composition -/

/-- If the inner future is ready, `AddOne` is ready with the value plus one. -/
theorem add_one_poll_ready {F : Type _} (inst : Future F Std.U32)
    {p p' : core.pin.Pin F} {cx cx' : Context} {v : Std.U32}
    (hp : inst.poll p cx = ok (.Ready v, p', cx')) (hv : v.val + 1 ≤ Std.U32.max) :
    ∃ w : Std.U32, w.val = v.val + 1 ∧
      AddOne.Insts.CoreFutureFutureFutureU32.poll inst ⟨⟨p.pointer⟩⟩ cx =
        ok (.Ready w, ⟨⟨p'.pointer⟩⟩, cx') := by
  obtain ⟨w, hw, hw'⟩ := spec_ok_exists (show v + 1#u32 ⦃ w => w.val = v.val + 1 ⦄ by step*)
  refine ⟨w, hw', ?_⟩
  unfold AddOne.Insts.CoreFutureFutureFutureU32.poll
  simp [hp, hw]

/-- If the inner future is pending, `AddOne` is pending. -/
theorem add_one_poll_pending {F : Type _} (inst : Future F Std.U32)
    {p p' : core.pin.Pin F} {cx cx' : Context}
    (hp : inst.poll p cx = ok (.Pending, p', cx')) :
    AddOne.Insts.CoreFutureFutureFutureU32.poll inst ⟨⟨p.pointer⟩⟩ cx =
      ok (.Pending, ⟨⟨p'.pointer⟩⟩, cx') := by
  unfold AddOne.Insts.CoreFutureFutureFutureU32.poll
  simp [hp]

/-- `async { inner.await + 1 }`: if the inner future completes with `v` (and `v + 1` does not
overflow), so does `AddOne`, with the same number of polls, and with `v + 1`. -/
theorem add_one_completes {F : Type _} (inst : Future F Std.U32)
    {p p' : core.pin.Pin F} {cx : Context} {v : Std.U32}
    (h : inst.Completes p cx v p') (hv : v.val + 1 ≤ Std.U32.max) :
    ∃ w : Std.U32, w.val = v.val + 1 ∧
      (AddOne.Insts.CoreFutureFutureFutureU32 inst).Completes
        ⟨⟨p.pointer⟩⟩ cx w ⟨⟨p'.pointer⟩⟩ := by
  induction h with
  | ready hp =>
    obtain ⟨w, hw, hpoll⟩ := add_one_poll_ready inst hp hv
    exact ⟨w, hw, .ready hpoll⟩
  | pending hp _ ih =>
    obtain ⟨w, hw, hc⟩ := ih hv
    exact ⟨w, hw, .pending (add_one_poll_pending inst hp) hc⟩

/-- Running `AddOne` to completion is running the inner future to completion, then adding one. -/
theorem add_one_block_on {F : Type _} (inst : Future F Std.U32)
    {p p' : core.pin.Pin F} {cx : Context} {v : Std.U32}
    (h : inst.Completes p cx v p') (hv : v.val + 1 ≤ Std.U32.max) :
    ∃ w : Std.U32, w.val = v.val + 1 ∧
      (AddOne.Insts.CoreFutureFutureFutureU32 inst).block_on ⟨⟨p.pointer⟩⟩ cx =
        ok (w, ⟨⟨p'.pointer⟩⟩) := by
  obtain ⟨w, hw, hc⟩ := add_one_completes inst h hv
  exact ⟨w, hw, hc.block_on⟩

/-- `async { countdown.await + 1 }` returns `43`, whatever the initial value of the counter. -/
theorem add_one_countdown (n : Std.U32) (cx : Context) :
    ∃ w : Std.U32, w.val = 43 ∧
      (AddOne.Insts.CoreFutureFutureFutureU32 Countdown.Insts.CoreFutureFutureFutureU32).block_on
        ⟨⟨n⟩⟩ cx = ok (w, ⟨⟨0#u32⟩⟩) := by
  obtain ⟨w, hw, h⟩ := add_one_block_on Countdown.Insts.CoreFutureFutureFutureU32
    (countdown_completes n.val n cx rfl) (by scalar_tac)
  exact ⟨w, by simpa using hw, h⟩

/-! ## The executor loop `block_on` -/

/-- The loop of the executor of the Rust code runs a future which completes to completion. -/
theorem block_on_loop_of_completes {F Output : Type _} (inst : Future F Output)
    {p p' : core.pin.Pin F} {cx : Context} {v : Output}
    (h : inst.Completes p cx v p') :
    block_on_loop inst cx p.pointer = ok (v, p'.pointer) := by
  induction h with
  | ready hp =>
    unfold block_on_loop
    rw [loop]
    simp [block_on_loop.body, hp]
  | pending hp _ ih =>
    unfold block_on_loop at *
    rw [loop]
    simp [block_on_loop.body, hp]
    exact ih

/-- The executor of the Rust code returns the result of a future which completes. -/
theorem block_on_of_completes {F Output : Type _} (inst : Future F Output)
    {p p' : core.pin.Pin F} {v : Output}
    (h : inst.Completes p ⟨⟨⟩⟩ v p') :
    block_on inst p.pointer = ok (v, p'.pointer) := by
  unfold block_on
  simp [core.task.wake.Waker.noop, core.task.wake.Context.from_waker, block_on_loop_of_completes inst h]

end future
