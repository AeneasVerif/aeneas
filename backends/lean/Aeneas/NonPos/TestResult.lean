module
public import Aeneas.NonPos.Result

@[expose] public section
/-!
# Tests over `Result`: the examples of `nonpos/main/Test.lean` and `nonpos/tests/fix_pred`
-/
namespace NonPos.TestR
open NonPos

nonpos_structure Bla (Self : Type) : Type 1 where
  to_num : Self → Result Nat
  add : ∀ {Other : Type} (BlaInst : Bla Other), Other → Self → Result Nat

/-- An instance that uses the effects: `to_num` reads an input, `add` may fail. -/
def NatBla.add {Other : Type} (BlaInst : Bla Other) (o : Other) (s : Nat) : Result Nat := do
  let x ← BlaInst.to_num o
  if x = 0 then Result.fail "zero" else pure (x + s)

def NatBla : Bla Nat :=
  Bla.mk (fun s => Result.input fun n => Result.ok (n + s))
    (fun {Other} (BlaInst : Bla Other) => NatBla.add BlaInst) (by nonpos_cont)

/-- The continuation of an effect may itself use the dictionary. -/
example {O : Type} (o : O) :
    Cont (fun (BlaInst : Bla O) => Result.input (fun n => (BlaInst.to_num o).bind fun x => pure (x + n))) := by
  nonpos_cont

/-! ## `sumNum`: a `partial_fixpoint` with `do` notation -/

def sumNum {T : Type} (bla : Bla T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 0
  let x ← bla.to_num a
  let r ← sumNum bla a (n - 1)
  return x + r
partial_fixpoint

theorem cont_sumNum {T : Type} (a : T) (n : Nat) : Cont fun (bla : Bla T) => sumNum bla a n := by
  nonpos_cont

/-! ## A mutual `partial_fixpoint`: the fixpoint is over a `PProd` -/

mutual
def evenT {T : Type} (bla : Bla T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 0
  let x ← bla.to_num a
  let r ← oddT bla a (n - 1)
  return x + r
partial_fixpoint
def oddT {T : Type} (bla : Bla T) (a : T) (n : Nat) : Result Nat := do
  if n = 0 then return 1
  let r ← evenT bla a (n - 1)
  return r
partial_fixpoint
end

theorem cont_evenT {T : Type} (a : T) (n : Nat) : Cont fun (bla : Bla T) => evenT bla a n := by
  nonpos_cont
theorem cont_oddT {T : Type} (a : T) (n : Nat) : Cont fun (bla : Bla T) => oddT bla a n := by
  nonpos_cont

/-! ## A nested loop: `fix` inside `bind` inside another `fix` -/

def nested {T : Type} (bla : Bla T) (a : T) (n m : Nat) : Result Nat := do
  if m = 0 then return 0
  let x ← sumNum bla a n
  let r ← nested bla a n (m - 1)
  return x + r
partial_fixpoint

theorem cont_nested {T : Type} (a : T) (n m : Nat) : Cont fun (bla : Bla T) => nested bla a n m := by
  nonpos_cont

-- Modularity: with `cont_sumNum` tagged, the inner loop is not unfolded.
attribute [nonpos_continuous] cont_sumNum
theorem cont_nested' {T : Type} (a : T) (n m : Nat) : Cont fun (bla : Bla T) => nested bla a n m := by
  nonpos_cont

/-! ## `rec_id`-style recursion, with `Result.bind` written explicitly and a `match` -/

def recId {T : Type} (bla : Bla T) (a : T) : Nat → Result Nat
  | 0 => Result.ok 0
  | n + 1 => (bla.to_num a).bind fun x => (recId bla a n).bind fun r => Result.ok (x + r)
partial_fixpoint

theorem cont_recId {T : Type} (a : T) (n : Nat) : Cont fun (bla : Bla T) => recId bla a n := by
  nonpos_cont

/-! ## Using the structure: `mk` and the projections compute -/

example (s : Nat) : Bla.to_num NatBla s = Result.input fun n => Result.ok (n + s) := by simp [NatBla]
example {O : Type} (inst : Bla O) (o : O) (s : Nat) : Bla.add NatBla inst o s = NatBla.add inst o s := by
  simp [NatBla]

end NonPos.TestR
