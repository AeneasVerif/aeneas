module
public import Aeneas
public import ThreadScope.ThreadScope
public section

open Aeneas Aeneas.Std Result

/-! Specifications of the examples of the models of `thread::scope`, `Scope::spawn` and
`ScopedJoinHandle::join`.

The closure of `scope` calls `spawn` with closures, and `step*` can't infer the postconditions of
the nested closures: we unfold the models of `scope`, `spawn` and `join`, which run the closures. -/

namespace thread_scope

theorem first_two_spec (a : Slice U32) (h : 2 ≤ a.length)
    (hs : a.val[0]!.val + a.val[1]!.val ≤ U32.max) :
    first_two a ⦃ r => r.val = a.val[0]!.val + a.val[1]!.val ⦄ := by
  unfold first_two
  simp only [std.thread.scoped.scope, std.thread.scoped.Scope.spawn,
    first_two.closure.Insts.CoreOpsFunctionFnOnceTupleShared2ScopeU32.call_once,
    first_two.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once,
    first_two.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32.call_once,
    std.thread.scoped.ScopedJoinHandle.join_mk, core.result.Result.unwrap_Ok,
    Std.bind_tc_eq, Std.bind_assoc, Std.bind_ok]
  step*
  all_goals grind

/-- The thread which is not joined runs: its panic (here, `a` is empty) makes `scope` panic. -/
theorem not_joined_spec (a : Slice U32) (h : 1 ≤ a.length) :
    not_joined a ⦃ r => r = 5#u32 ⦄ := by
  unfold not_joined
  simp only [std.thread.scoped.scope, std.thread.scoped.Scope.spawn,
    not_joined.closure.Insts.CoreOpsFunctionFnOnceTupleShared2ScopeU32.call_once,
    not_joined.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32.call_once,
    Std.bind_tc_eq, Std.bind_assoc, Std.bind_ok]
  step*

theorem borrowed_len_spec (a : Slice U32) :
    borrowed_len a ⦃ r => r.val = a.length ⦄ := by
  unfold borrowed_len
  simp only [std.thread.scoped.scope, std.thread.scoped.Scope.spawn,
    borrowed_len.closure.Insts.CoreOpsFunctionFnOnceTupleShared2ScopeUsize.call_once,
    borrowed_len.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsize.call_once,
    std.thread.scoped.ScopedJoinHandle.join_mk, core.result.Result.unwrap_Ok,
    Std.bind_tc_eq, Std.bind_ok]
  step*

end thread_scope
