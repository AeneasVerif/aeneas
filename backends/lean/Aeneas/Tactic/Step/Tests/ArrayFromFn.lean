module
import Aeneas.Std.Array.FromFn
import Aeneas.Tactic.Step

/-! Tests that the specs of `core::array::from_fn` apply to code shaped like what Aeneas generates
(the closures below have the shape of the closures in the extraction of
`tests/src/array-constructors.rs`). As in
`HigherOrderOption.lean`, the closure functions are marked with `step_simps` so that `step` can go
through them. -/

open Aeneas Aeneas.Std Result

namespace array_from_fn

/-! ## A closure which doesn't update its state: `from_fn(|i| (i * i) as u32)` -/

@[reducible] def squares.closure := Unit

@[step_simps]
def squares.closure.call_mut (c : squares.closure) (tupled_args : Usize) :
    Result (U32 × squares.closure) := do
  let i ← tupled_args * tupled_args
  let i1 ← lift (UScalar.cast .U32 i)
  ok (i1, c)

def squares.closure.call_once (c : squares.closure) (i : Usize) : Result U32 := do
  let (i1, _) ← squares.closure.call_mut c i
  ok i1

@[reducible] def squares.closure.FnOnce : core.ops.function.FnOnce squares.closure Usize U32 :=
  { call_once := squares.closure.call_once }

@[reducible] def squares.closure.FnMut : core.ops.function.FnMut squares.closure Usize U32 :=
  { FnOnceInst := squares.closure.FnOnce, call_mut := squares.closure.call_mut }

def squares : Result (Array U32 4#usize) :=
  core.array.from_fn 4#usize squares.closure.FnMut ()

example : squares ⦃ a => ∀ j (hj : j < a.val.length), (a.val[j]).val = j * j ⦄ := by
  unfold squares
  step* +inferPost
  -- `step*` stops after the first bind of the closure body: step through the rest of it
  on_goal 2 => step* +inferPost
  obtain ⟨i, hi, x, hx, rfl, ha⟩ := a_post j j_post
  simp only [Prod.mk.injEq, and_true] at ha
  have hi' : i.val < 4 := by simpa using hi
  have hx' : x.val < 2 ^ UScalarTy.U32.numBits := by
    have : i.val * i.val < 16 := by nlinarith
    simp only [UScalarTy.U32_numBits_eq]; omega
  rw [ha, UScalar.cast_val_eq, Nat.mod_eq_of_lt hx', hx]

/-! ## A closure which updates its state: a counter `c`, with `from_fn(|i| { c += 1; c * 100 + i })` -/

@[reducible] def stateful.closure := U32

@[step_simps]
def stateful.closure.call_mut (c : stateful.closure) (tupled_args : Usize) :
    Result (U32 × stateful.closure) := do
  let i ← c + 1#u32
  let i1 ← i * 100#u32
  let i2 ← lift (UScalar.cast .U32 tupled_args)
  let i3 ← i1 + i2
  ok (i3, i)

def stateful.closure.call_once (c : stateful.closure) (i : Usize) : Result U32 := do
  let (i1, _) ← stateful.closure.call_mut c i
  ok i1

@[reducible] def stateful.closure.FnOnce : core.ops.function.FnOnce stateful.closure Usize U32 :=
  { call_once := stateful.closure.call_once }

@[reducible] def stateful.closure.FnMut : core.ops.function.FnMut stateful.closure Usize U32 :=
  { FnOnceInst := stateful.closure.FnOnce, call_mut := stateful.closure.call_mut }

def stateful : Result (Array U32 4#usize) :=
  core.array.from_fn 4#usize stateful.closure.FnMut 0#u32

/- The counter's invariant: before the call on index `i`, the counter is `i`. -/
example : stateful ⦃ a => ∀ j (hj : j < a.val.length), (a.val[j]).val = (j + 1) * 100 + j ⦄ := by
  unfold stateful
  apply core.array.from_fn.spec _ _ _ (post := fun j (v : U32) => v.val = (j + 1) * 100 + j)
    (fun i (g : stateful.closure) => g.val = i) (by simp)
  intro i g hi hg
  step*

end array_from_fn
