module
import Aeneas.Std.Core.CoreOption
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace higher_order_option

/-! The closures below have the shape Aeneas generates: a type, a `call_once` function and an
`FnOnce` instance. Marking `call_once` with `step_simps` lets `step` go through it. -/

/- `x.map(|v| v + 1)` -/
@[reducible] def incr.closure := Unit

@[step_simps]
def incr.closure.call_once (_ : incr.closure) (v : U32) : Result U32 := v + 1#u32

@[reducible] def incr.closure.FnOnceInst :
  core.ops.function.FnOnce incr.closure U32 U32 := { call_once := incr.closure.call_once }

def incr (x : Option U32) : Result (Option U32) :=
  core.option.Option.map incr.closure.FnOnceInst x ()

example (x : Option U32) (h : ∀ v, x = some v → v.val + 1 ≤ U32.max) :
  incr x ⦃ y => ∀ v, x = some v → ∃ w, y = some w ∧ w.val = v.val + 1 ⦄ := by
  unfold incr
  step* +inferPost

/- `x.is_some_and(|v| v + 1 > 3)` -/
@[reducible] def big.closure := Unit

@[step_simps]
def big.closure.call_once (_ : big.closure) (v : U32) : Result Bool := do
  let w ← v + 1#u32
  ok (w > 3#u32)

@[reducible] def big.closure.FnOnceInst :
  core.ops.function.FnOnce big.closure U32 Bool := { call_once := big.closure.call_once }

def big (x : Option U32) : Result Bool :=
  core.option.Option.is_some_and big.closure.FnOnceInst x ()

example (x : Option U32) (h : ∀ v, x = some v → v.val + 1 ≤ U32.max) :
  big x ⦃ b => b = true ↔ ∃ v, x = some v ∧ v.val + 1 > 3 ⦄ := by
  unfold big
  let* ⟨ b, b_post ⟩ ← [ +inferPost ] core.option.Option.is_some_and.spec
  case hf =>
    intros value _
    let* ⟨ w, w_post ⟩ ← [ +inferPost ] U32.add_spec
    exact ⟨‹_›, w, w_post, rfl⟩
  cases x <;> agrind

/- `x.is_some_and(|v| v > 3)`: the closure has no step, so its postcondition is given -/
@[reducible] def gt3.closure := Unit

@[step_simps]
def gt3.closure.call_once (_ : gt3.closure) (v : U32) : Result Bool := ok (v > 3#u32)

@[reducible] def gt3.closure.FnOnceInst :
  core.ops.function.FnOnce gt3.closure U32 Bool := { call_once := gt3.closure.call_once }

def gt3 (x : Option U32) : Result Bool :=
  core.option.Option.is_some_and gt3.closure.FnOnceInst x ()

example (x : Option U32) :
  gt3 x ⦃ b => b = true ↔ ∃ v, x = some v ∧ v.val > 3 ⦄ := by
  unfold gt3
  let* ⟨ b, b_post ⟩ ← core.option.Option.is_some_and.spec
    (post := fun v b => b = decide (v > 3#u32))
  case hf =>
    intros value _
    step*
  cases x <;> agrind

/- `b.then(|| c + 1)`, with a closure capturing `c` -/
@[reducible] def succ.closure := U32

@[step_simps]
def succ.closure.call_once (c : succ.closure) (_ : Unit) : Result U32 := c + 1#u32

@[reducible] def succ.closure.FnOnceInst :
  core.ops.function.FnOnce succ.closure Unit U32 := { call_once := succ.closure.call_once }

def succ (b : Bool) (c : U32) : Result (Option U32) :=
  core.bool.Bool.then succ.closure.FnOnceInst b c

example (b : Bool) (c : U32) (h : c.val + 1 ≤ U32.max) :
  succ b c ⦃ y => if b then ∃ w, y = some w ∧ w.val = c.val + 1 else y = none ⦄ := by
  unfold succ
  step* +inferPost
  cases b <;> agrind

end higher_order_option
