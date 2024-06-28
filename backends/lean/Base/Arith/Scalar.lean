import Base.Arith.Int
import Base.Primitives.Scalar

/- Automation for scalars - TODO: not sure it is worth having two files (Int.lean and Scalar.lean) -/
namespace Arith

open Lean Lean.Elab Lean.Meta
open Primitives

def scalarTacExtraPreprocess : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Inroduce the bounds for the isize/usize types
  let add (e : Expr) : Tactic.TacticM Unit := do
    let ty ← inferType e
    let _ ← Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) e ty (asLet := false)
  add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Isize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Usize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Isize []])
  -- Reveal the concrete bounds, simplify calls to [ofInt]
  Utils.simpAt true {}
               -- Simprocs
               intTacSimpRocs
               -- Unfoldings
               [``Scalar.min, ``Scalar.max, ``Scalar.cMin, ``Scalar.cMax,
                ``I8.min, ``I16.min, ``I32.min, ``I64.min, ``I128.min,
                ``I8.max, ``I16.max, ``I32.max, ``I64.max, ``I128.max,
                ``U8.min, ``U16.min, ``U32.min, ``U64.min, ``U128.min,
                ``U8.max, ``U16.max, ``U32.max, ``U64.max, ``U128.max,
                ``Usize.min
                ]
                -- Simp lemmas
                [``Scalar.ofInt_val_eq, ``Scalar.neq_to_neq_val,
                 ``Scalar.lt_equiv, ``Scalar.le_equiv, ``Scalar.eq_equiv]
                -- Hypotheses
                [] .wildcard

elab "scalar_tac_preprocess" : tactic =>
  intTacPreprocess scalarTacExtraPreprocess

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac (splitGoalConjs : Bool) : Tactic.TacticM Unit := do
  intTac "scalar_tac" splitGoalConjs scalarTacExtraPreprocess

elab "scalar_tac" : tactic =>
  scalarTac false

@[scalar_tac x]
theorem Scalar.bounds {ty : ScalarTy} (x : Scalar ty) :
  Scalar.min ty ≤ x.val ∧ x.val ≤ Scalar.max ty :=
  And.intro x.hmin x.hmax

example (x _y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac_preprocess
  simp [*]

example (x _y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac

-- Checking that we explore the goal *and* projectors correctly
example (x : U32 × U32) : 0 ≤ x.fst.val := by
  scalar_tac

-- Checking that we properly handle [ofInt]
example : U32.ofInt 1 ≤ U32.max := by
  scalar_tac

example (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ U32.max) :
  U32.ofIntCore x (by constructor <;> scalar_tac) ≤ U32.max := by
  scalar_tac_preprocess
  scalar_tac

-- Not equal
example (x : U32) (h0 : ¬ x = U32.ofInt 0) : 0 < x.val := by
  scalar_tac

/- See this: https://aeneas-verif.zulipchat.com/#narrow/stream/349819-general/topic/U64.20trouble/near/444049757

   We solved it by removing the instance `OfNat` for `Scalar`.
   Note however that we could also solve it with a simplification lemma.
   However, after testing, we noticed we could only apply such a lemma with
   the rewriting tactic (not the simplifier), probably because of the use
   of typeclasses. -/
example {u: U64} (h1: (u : Int) < 2): (u : Int) = 0 ∨ (u : Int) = 1 := by
  scalar_tac

example (x : I32) : -100000000000 < x.val := by
  scalar_tac

example : (Usize.ofInt 2).val ≠ 0 := by
  scalar_tac

end Arith
