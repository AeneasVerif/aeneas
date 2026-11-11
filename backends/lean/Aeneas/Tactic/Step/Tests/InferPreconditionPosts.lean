module
import Aeneas.Std.Core.CoreOption
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

/-!
# Tests for inferring the unknown postconditions of preconditions

When a precondition is a specification whose postcondition is unknown (e.g. the postcondition
`post` of the closure in the specification of `Option.map`), `step*` infers it by stepping through
the precondition. If it can't prove the precondition completely, it leaves it untouched.
-/

namespace infer_precondition_posts

/- `x.map(|v| v + 1)` -/
@[reducible] def incr.closure := Unit

@[step_simps]
def incr.closure.call_once (_ : incr.closure) (v : U32) : Result U32 := v + 1#u32

@[reducible] def incr.closure.FnOnceInst :
  core.ops.function.FnOnce incr.closure U32 U32 := { call_once := incr.closure.call_once }

def incr (x : Option U32) : Result (Option U32) :=
  core.option.Option.map incr.closure.FnOnceInst x ()

/- The script: only the steps inside the precondition need `+inferPost`. -/
/--
info: Try this:

  [apply]     let* ⟨ y, y_post, v, x_post ⟩ ← core.option.Option.map.spec
    case hf =>
      intros value _
      let* ⟨ _, _ ⟩ ← [ +inferPost ] U32.add_spec
      agrind
    agrind
-/
#guard_msgs in
example (x : Option U32) (h : ∀ v, x = some v → v.val + 1 ≤ U32.max) :
    incr x ⦃ y => ∀ v, x = some v → ∃ w, y = some w ∧ w.val = v.val + 1 ⦄ := by
  unfold incr
  step*?

/-- The script replays. -/
example (x : Option U32) (h : ∀ v, x = some v → v.val + 1 ≤ U32.max) :
    incr x ⦃ y => ∀ v, x = some v → ∃ w, y = some w ∧ w.val = v.val + 1 ⦄ := by
  unfold incr
  let* ⟨ y, y_post, v, x_post ⟩ ← core.option.Option.map.spec
  case hf =>
    intros value _
    let* ⟨ _, _ ⟩ ← [ +inferPost ] U32.add_spec
    agrind
  agrind

/- `x.map(|v| mystery v)`, where nothing is known about `mystery`: the inference fails. -/
opaque mystery : U32 → Result U32

@[reducible] def opaque.closure := Unit

@[step_simps]
def opaque.closure.call_once (_ : opaque.closure) (v : U32) : Result U32 := mystery v

@[reducible] def opaque.closure.FnOnceInst :
  core.ops.function.FnOnce opaque.closure U32 U32 := { call_once := opaque.closure.call_once }

def opaque_map (x : Option U32) : Result (Option U32) :=
  core.option.Option.map opaque.closure.FnOnceInst x ()

/-- What we know about `mystery`, in a form `step` can't use. -/
def MysterySpec : Prop := ∀ v, mystery v ⦃ r => r = v ⦄

/-- The inference fails: the precondition is left untouched (its postcondition is still unknown),
for the user to prove. -/
example (x : Option U32) (hm : MysterySpec) : opaque_map x ⦃ y => y = x ⦄ := by
  unfold opaque_map
  step*
  case post => exact fun v r => r = v
  case hf =>
    intro v _
    exact hm v
  cases x <;> simp_all

end infer_precondition_posts
