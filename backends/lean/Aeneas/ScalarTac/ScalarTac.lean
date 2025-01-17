import Aeneas.ScalarTac.IntTac
import Aeneas.Std.ScalarBase

namespace Aeneas

/- Automation for scalars - TODO: not sure it is worth having two files (Int.lean and Scalar.lean) -/
namespace ScalarTac

open Lean Lean.Elab Lean.Meta
open Std

def scalarTacSimpLemmas :=
  [``Scalar.ofInt_val_eq, ``Scalar.neq_to_neq_val,
   ``Scalar.lt_equiv, ``Scalar.le_equiv, ``Scalar.eq_equiv]

def scalarTacExtraPrePreprocess : Tactic.TacticM Unit :=
  Tactic.withMainContext do
  -- First get rid of [ofInt] (if there are dependent arguments, we may not
  -- manage to simplify the context)
  Utils.simpAt true {dsimp := false, failIfUnchanged := false}
               -- Simprocs
               intTacSimpRocs
               -- Unfoldings
               []
                -- Simp lemmas
                scalarTacSimpLemmas
                -- Hypotheses
                [] .wildcard

def scalarTacExtraPreprocess : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Inroduce the bounds for the isize/usize types
  let add (e : Expr) : Tactic.TacticM Unit := do
    let ty ← inferType e
    let _ ← Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) e ty (asLet := false)
  add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Isize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Usize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Isize []])
  Utils.simpAt true {failIfUnchanged := false}
               -- Simprocs
               intTacSimpRocs
               -- Unfoldings
               [``Scalar.min, ``Scalar.max, ``Scalar.cMin, ``Scalar.cMax,
                ``I8.min, ``I16.min, ``I32.min, ``I64.min, ``I128.min,
                ``I8.max, ``I16.max, ``I32.max, ``I64.max, ``I128.max,
                ``U8.min, ``U16.min, ``U32.min, ``U64.min, ``U128.min,
                ``U8.max, ``U16.max, ``U32.max, ``U64.max, ``U128.max,
                ``Usize.min,
                ``Scalar.in_bounds,
                ``Scalar.toNat, ``Isize.toNat, ``USize.toNat,
                ``I8.toNat, ``I16.toNat, ``I32.toNat, ``I64.toNat, ``I128.toNat,
                ``U8.toNat, ``U16.toNat, ``U32.toNat, ``U64.toNat, ``U128.toNat,
                ``U8.unsigned_ofNat_toNat, ``U16.unsigned_ofNat_toNat,
                ``U32.unsigned_ofNat_toNat, ``U64.unsigned_ofNat_toNat,
                ``U128.unsigned_ofNat_toNat, ``Usize.unsigned_ofNat_toNat,
                ]
                -- Simp lemmas
                scalarTacSimpLemmas
                -- Hypotheses
                [] .wildcard
  trace[ScalarTac] "scalarTacExtraPreprocess: after simp: {(← Tactic.getMainGoal)}"

elab "scalar_tac_preprocess" : tactic =>
  intTacPreprocess scalarTacExtraPrePreprocess scalarTacExtraPreprocess

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac (splitAllDisjs splitGoalConjs : Bool) : Tactic.TacticM Unit := do
  intTac "scalar_tac" splitAllDisjs splitGoalConjs scalarTacExtraPrePreprocess scalarTacExtraPreprocess

elab "scalar_tac" : tactic =>
  scalarTac true false

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

example (x y : Nat) (z : Int) (h : Int.subNatNat x y + z = 0) : (x : Int) - (y : Int) + z = 0 := by
  scalar_tac_preprocess
  omega

example (x : U32) (h : 16 * ↑x ≤ U32.max) :
  4 * U32.ofInt (4 * x.val) (by scalar_tac) ≤ U32.max := by
  scalar_tac

example (b : Bool) (x y : Int) (h : if b then P ∧ x + y < 3 else x + y < 4) : x + y < 5 := by
  scalar_tac

example
  (xi yi : U32)
  (c0 : U8)
  (hCarryLe : c0.val ≤ 1)
  (c0u : U32)
  (_ : c0u.val = c0.val)
  (s1 : U32)
  (c1 : Bool)
  (hConv1 : if ↑xi + ↑c0u > U32.max then ↑s1 = ↑xi + ↑c0u - U32.max - 1 ∧ c1 = true else s1 = xi.val + c0u ∧ c1 = false)
  (s2 : U32)
  (c2 : Bool)
  (hConv2 : if ↑s1 + ↑yi > U32.max then ↑s2 = ↑s1 + ↑yi - U32.max - 1 ∧ c2 = true else s2 = s1.val + yi ∧ c2 = false)
  (c1u : U8)
  (_ : c1u.val = if c1 = true then 1 else 0)
  (c2u : U8)
  (_ : c2u.val = if c2 = true then 1 else 0)
  (c3 : U8)
  (_ : c3.val = c1u.val + c2u.val):
  c3.val ≤ 1 := by
  scalar_tac

end ScalarTac

end Aeneas
