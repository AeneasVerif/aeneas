module
public import Aeneas.NonPos.Tests.Result

@[expose] public section
-- as in the files Aeneas generates: the named instance binders of trait methods are unused
set_option linter.unusedVariables false
/-!
# Tests over `Result`: the examples of `nonpos/main/Test.lean` and `nonpos/tests/fix_pred`
-/
namespace NonPos.TestR
open NonPos NonPos.Tests

nonpos_structure Measure (Self : Type) : Type 1 where
  size : Self → Result Nat
  combine : ∀ {Other : Type} (MeasureInst : Measure Other), Other → Self → Result Nat

/-- An instance that uses the effects: `size` reads an input, `combine` may fail. -/
def NatMeasure.combine {Other : Type} (MeasureInst : Measure Other) (o : Other) (s : Nat) : Result Nat := do
  let x ← MeasureInst.size o
  if x = 0 then Result.fail "zero" else pure (x + s)

def NatMeasure : Measure Nat :=
  Measure.mk (fun s => Result.input fun n => Result.ok (n + s))
    (fun {Other} (MeasureInst : Measure Other) => NatMeasure.combine MeasureInst) (by nonpos_cont)

/-- The continuation of an effect may itself use the dictionary. -/
example {O : Type} (o : O) :
    Cont (fun (MeasureInst : Measure O) => Result.input (fun n => (MeasureInst.size o).bind fun x => pure (x + n))) := by
  nonpos_cont

/-! ## `sumNum`: a `partial_fixpoint` with `do` notation -/

def sumNum {T : Type} (meas : Measure T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 0
  let x ← meas.size a
  let r ← sumNum meas a (n - 1)
  return x + r
partial_fixpoint

theorem cont_sumNum {T : Type} (a : T) (n : Nat) : Cont fun (meas : Measure T) => sumNum meas a n := by
  nonpos_cont

/-! ## A mutual `partial_fixpoint`: the fixpoint is over a `PProd` -/

mutual
def evenT {T : Type} (meas : Measure T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 0
  let x ← meas.size a
  let r ← oddT meas a (n - 1)
  return x + r
partial_fixpoint
def oddT {T : Type} (meas : Measure T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 1
  let r ← evenT meas a (n - 1)
  return r
partial_fixpoint
end

theorem cont_evenT {T : Type} (a : T) (n : Nat) : Cont fun (meas : Measure T) => evenT meas a n := by
  nonpos_cont
theorem cont_oddT {T : Type} (a : T) (n : Nat) : Cont fun (meas : Measure T) => oddT meas a n := by
  nonpos_cont

/-! ## A nested loop: `fix` inside `bind` inside another `fix` -/

def nested {T : Type} (meas : Measure T) (a : T) (n m : Nat) : Result Nat := do
  if m = 0 then return 0
  let x ← sumNum meas a n
  let r ← nested meas a n (m - 1)
  return x + r
partial_fixpoint

theorem cont_nested {T : Type} (a : T) (n m : Nat) : Cont fun (meas : Measure T) => nested meas a n m := by
  nonpos_cont

-- Modularity: with `cont_sumNum` tagged, the inner loop is not unfolded.
attribute [nonpos_continuous] cont_sumNum
theorem cont_nested' {T : Type} (a : T) (n m : Nat) : Cont fun (meas : Measure T) => nested meas a n m := by
  nonpos_cont

/-! ## `rec_id`-style recursion, with `Result.bind` written explicitly and a `match` -/

def recId {T : Type} (meas : Measure T) (a : T) : Nat → Result Nat
  | 0 => Result.ok 0
  | n + 1 => (meas.size a).bind fun x => (recId meas a n).bind fun r => Result.ok (x + r)
partial_fixpoint

theorem cont_recId {T : Type} (a : T) (n : Nat) : Cont fun (meas : Measure T) => recId meas a n := by
  nonpos_cont

/-! ## Using the structure: `mk` and the projections compute -/

example (s : Nat) : Measure.size NatMeasure s = Result.input fun n => Result.ok (n + s) := by simp [NatMeasure]
example {O : Type} (inst : Measure O) (o : O) (s : Nat) : Measure.combine NatMeasure inst o s = NatMeasure.combine inst o s := by
  simp [NatMeasure]

end NonPos.TestR
