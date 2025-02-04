import Aeneas.ScalarTac.IntTac
import Aeneas.Std.ScalarCore

namespace Aeneas

/- Automation for scalars - TODO: not sure it is worth having two files (Int.lean and Scalar.lean) -/
namespace ScalarTac

open Lean Lean.Elab Lean.Meta
open Std

def scalarTacSimpLemmas :=
  [``UScalar.ofNat_val_eq, ``UScalar.neq_to_neq_val,
   ``IScalar.ofInt_val_eq, ``IScalar.neq_to_neq_val,
   ``UScalar.bv_toNat_eq,
   ``U8.bv_toNat_eq, ``U16.bv_toNat_eq, ``U32.bv_toNat_eq, ``U64.bv_toNat_eq, ``U128.bv_toNat_eq, ``Usize.bv_toNat_eq,
   ``IScalar.bv_toInt_eq,
   ``I8.bv_toInt_eq, ``I16.bv_toInt_eq, ``I32.bv_toInt_eq, ``I64.bv_toInt_eq, ``I128.bv_toInt_eq, ``Isize.bv_toInt_eq,
   ``UScalar.lt_equiv, ``UScalar.le_equiv, ``UScalar.eq_equiv,
   ``IScalar.lt_equiv, ``IScalar.le_equiv, ``IScalar.eq_equiv]

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
  add (← mkAppM ``IScalar.cMin_bound #[.const ``IScalarTy.Isize []])
  add (← mkAppM ``UScalar.cMax_bound #[.const ``UScalarTy.Usize []])
  add (← mkAppM ``IScalar.cMax_bound #[.const ``IScalarTy.Isize []])
  Utils.simpAt true {failIfUnchanged := false}
               -- Simprocs
               intTacSimpRocs
               -- Unfoldings
               [``IScalar.min, ``UScalar.max, ``IScalar.max, ``IScalar.cMin, ``UScalar.cMax, ``IScalar.cMax,
                ``I8.min, ``I16.min, ``I32.min, ``I64.min, ``I128.min,
                ``I8.max, ``I16.max, ``I32.max, ``I64.max, ``I128.max,
                ``U8.max, ``U16.max, ``U32.max, ``U64.max, ``U128.max,
                ``UScalar.inBounds, ``IScalar.inBounds,
                ``Isize.toNat, ``I8.toNat, ``I16.toNat, ``I32.toNat, ``I64.toNat, ``I128.toNat,
                ``U8.ofNat_val_eq, ``U16.ofNat_val_eq,
                ``U32.ofNat_val_eq, ``U64.ofNat_val_eq,
                ``U128.ofNat_val_eq, ``Usize.ofNat_val_eq,
                ]
                -- Simp lemmas
                scalarTacSimpLemmas
                -- Hypotheses
                [] .wildcard
  trace[ScalarTac] "scalarTacExtraPreprocess: after simp: {(← Tactic.getMainGoal)}"

elab "scalar_tac_preprocess" : tactic =>
  intTacPreprocess scalarTacExtraPrePreprocess scalarTacExtraPreprocess

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac (config : Config) : Tactic.TacticM Unit := do
  intTac "scalar_tac" config scalarTacExtraPrePreprocess scalarTacExtraPreprocess

elab "scalar_tac" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTac config

@[scalar_tac x]
theorem UScalar.bounds {ty : UScalarTy} (x : UScalar ty) :
  x.val ≤ UScalar.max ty :=
  x.hBounds

@[scalar_tac x]
theorem IScalar.bounds {ty : IScalarTy} (x : IScalar ty) :
  IScalar.min ty ≤ x.val ∧ x.val ≤ IScalar.max ty :=
  x.hBounds

example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac_preprocess
  simp [*]

example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac

-- Checking that we explore the goal *and* projectors correctly
example (x : U32 × U32) : 0 ≤ x.fst.val := by
  scalar_tac

-- Checking that we properly handle [ofInt]
example : (U32.ofNat 1).val ≤ U32.max := by
  scalar_tac

example (x : Nat) (h1 : x ≤ U32.max) :
  (U32.ofNatCore x (by scalar_tac)).val ≤ U32.max := by
  scalar_tac_preprocess
  scalar_tac

-- Not equal
example (x : U32) (h0 : ¬ x = U32.ofNat 0) : 0 < x.val := by
  scalar_tac

/- See this: https://aeneas-verif.zulipchat.com/#narrow/stream/349819-general/topic/U64.20trouble/near/444049757

   We solved it by removing the instance `OfNat` for `Scalar`.
   Note however that we could also solve it with a simplification lemma.
   However, after testing, we noticed we could only apply such a lemma with
   the rewriting tactic (not the simplifier), probably because of the use
   of typeclasses. -/
example {u: U64} (h1: (u : Nat) < 2): (u : Nat) = 0 ∨ (u : Nat) = 1 := by
  scalar_tac

example (x : I32) : -100000000000 < x.val := by
  scalar_tac

example : (Usize.ofNat 2).val ≠ 0 := by
  scalar_tac

example (x y : Nat) (z : Int) (h : Int.subNatNat x y + z = 0) : (x : Int) - (y : Int) + z = 0 := by
  scalar_tac_preprocess
  omega

example (x : U32) (h : 16 * x.val ≤ U32.max) :
  4 * (U32.ofNat (4 * x.val) (by scalar_tac)).val ≤ U32.max := by
  scalar_tac

example (b : Bool) (x y : Int) (h : if b then P ∧ x + y < 3 else x + y < 4) : x + y < 5 := by
  scalar_tac +split

open Utils

/- Some tests which introduce big constants (those sometimes cause issues when reducing expressions) -/
example (x y : Nat) (h : x = y + 2^32) : 0 ≤ x := by
  scalar_tac

example (x y : Nat) (h : x = y - 2^32) : 0 ≤ x := by
  scalar_tac

example
  (xi yi : U32)
  (c0 : U8)
  (hCarryLe : c0.val ≤ 1)
  (c0u : U32)
  (_ : c0u.val = c0.val)
  (s1 : U32)
  (c1 : Bool)
  (hConv1 : if xi.val + c0u.val > U32.max then s1.val = ↑xi + ↑c0u - U32.max - 1 ∧ c1 = true else s1 = xi.val + c0u ∧ c1 = false)
  (s2 : U32)
  (c2 : Bool)
  (hConv2 : if s1.val + yi.val > U32.max then s2.val = ↑s1 + ↑yi - U32.max - 1 ∧ c2 = true else s2 = s1.val + yi ∧ c2 = false)
  (c1u : U8)
  (_ : c1u.val = if c1 = true then 1 else 0)
  (c2u : U8)
  (_ : c2u.val = if c2 = true then 1 else 0)
  (c3 : U8)
  (_ : c3.val = c1u.val + c2u.val):
  c3.val ≤ 1 := by
  scalar_tac +split

end ScalarTac

end Aeneas
