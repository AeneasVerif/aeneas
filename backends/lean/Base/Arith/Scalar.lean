import Base.Arith.Int
import Base.Primitives.Scalar

/- Automation for scalars - TODO: not sure it is worth having two files (Int.lean and Scalar.lean) -/
namespace Arith

open Lean Lean.Elab Lean.Meta
open Primitives

def scalarTacExtraPreprocess (simp_only : Bool) : Tactic.TacticM Unit := do
   Tactic.withMainContext do
   -- Inroduce the bounds for the isize/usize types
   let add (e : Expr) : Tactic.TacticM Unit := do
     let ty ← inferType e
     let _ ← Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) e ty (asLet := false)
   add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Isize []])
   add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Usize []])
   add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Isize []])
   -- Reveal the concrete bounds, simplify calls to [ofInt]
   -- TODO: we could even try [simpAll]
   let decls_to_unfold :=
     [``Scalar.min, ``Scalar.max, ``Scalar.cMin, ``Scalar.cMax,
      ``I8.min, ``I16.min, ``I32.min, ``I64.min, ``I128.min,
      ``I8.max, ``I16.max, ``I32.max, ``I64.max, ``I128.max,
      ``U8.min, ``U16.min, ``U32.min, ``U64.min, ``U128.min,
      ``U8.max, ``U16.max, ``U32.max, ``U64.max, ``U128.max,
      ``Usize.min
      ]
   let thms := [``Scalar.ofInt_val_eq, ``Scalar.neq_to_neq_val]
   let hyps := []
   Utils.simpAt simp_only decls_to_unfold thms hyps .wildcard

elab "scalar_tac_preprocess" : tactic =>
  intTacPreprocess (scalarTacExtraPreprocess false)

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac (simp_only : Bool) (splitGoalConjs : Bool) : Tactic.TacticM Unit := do
  intTac splitGoalConjs (scalarTacExtraPreprocess simp_only)

elab "scalar_tac" : tactic =>
  scalarTac false false

instance (ty : ScalarTy) : HasIntProp (Scalar ty) where
  -- prop_ty is inferred
  prop := λ x => And.intro x.hmin x.hmax

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  intro_has_int_prop_instances
  simp [*]

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac

-- Checking that we explore the goal *and* projectors correctly
example (x : U32 × U32) : 0 ≤ x.fst.val := by
  scalar_tac

-- Checking that we properly handle [ofInt]
example : U32.ofInt 1 ≤ U32.max := by
  scalar_tac

example (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ U32.max) :
  U32.ofInt x (by constructor <;> scalar_tac) ≤ U32.max := by
  scalar_tac

-- Not equal
example (x : U32) (h0 : ¬ x = U32.ofInt 0) : 0 < x.val := by
  scalar_tac

end Arith
