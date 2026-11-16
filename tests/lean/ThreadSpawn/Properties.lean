module
public import Aeneas
public import ThreadSpawn.ThreadSpawn
public section

open Aeneas Aeneas.Std Result

/-! Specifications of the examples of the models of `thread::spawn` and `JoinHandle::join`. -/

namespace thread_spawn

attribute [local step_simps]
  computation.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once
  fork_join.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once
  fork_join.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32.call_once
  fill.closure.Insts.CoreOpsFunctionFnOnceTupleVecU32.call_once
  join_match.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once
  overflow.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once

/-- The example of the documentation of `thread::spawn`. The closure has no step, so its
postcondition is given. -/
theorem computation_spec : computation ⦃ r => r = 42#u32 ⦄ := by
  unfold computation
  let* ⟨ h, h_post ⟩ ← std.thread.functions.spawn.spec (post := fun (r : U32) => r = 42#u32)
  · simp [computation.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once]
  step*

/-- `moved.closure` is a pair, which `step` can't unify with the type of the argument of `spawn`
(only the closure types with at most one field are reducible): we unfold `spawn` instead. -/
theorem moved_spec (x y : U32) (h : x.val + y.val ≤ U32.max) :
    moved x y ⦃ r => r.val = x.val + y.val ⦄ := by
  unfold moved
  simp only [std.thread.functions.spawn, moved.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once,
    Std.bind_tc_eq, Std.bind_assoc, Std.bind_ok, std.thread.join_handle.JoinHandle.join_mk]
  step*

@[step]
theorem double_spec (x : U32) (h : x.val * 2 ≤ U32.max) :
    double x ⦃ r => r.val = x.val * 2 ⦄ := by
  unfold double
  step*

theorem fork_join_spec (x y : U32) (hx : x.val * 2 ≤ U32.max) (hy : y.val * 2 ≤ U32.max)
    (h : x.val * 2 + y.val * 2 ≤ U32.max) :
    fork_join x y ⦃ r => r.val = x.val * 2 + y.val * 2 ⦄ := by
  unfold fork_join
  step* +inferPost
  all_goals first | scalar_tac | simp_all

theorem fill_spec (v : alloc.vec.Vec U32) (h : v.length < Usize.max) :
    fill v ⦃ r => r.val = v.val ++ [7#u32] ⦄ := by
  unfold fill
  step* +inferPost

theorem join_match_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    join_match x ⦃ r => r.val = x.val + 1 ⦄ := by
  unfold join_match
  step* +inferPost

/-- A panic in the thread (here an overflow) is a failure of the whole computation. -/
theorem overflow_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    overflow x ⦃ r => r.val = x.val + 1 ⦄ := by
  unfold overflow
  step* +inferPost

end thread_spawn
