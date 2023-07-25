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
     let _ ← Utils.addDeclTac (← mkFreshUserName `h) e ty (asLet := false)
   add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Isize []])
   add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Usize []])
   add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Isize []])
   -- Reveal the concrete bounds
   Utils.simpAt [``Scalar.min, ``Scalar.max, ``Scalar.cMin, ``Scalar.cMax,
                 ``I8.min, ``I16.min, ``I32.min, ``I64.min, ``I128.min,
                 ``I8.max, ``I16.max, ``I32.max, ``I64.max, ``I128.max,
                 ``U8.min, ``U16.min, ``U32.min, ``U64.min, ``U128.min,
                 ``U8.max, ``U16.max, ``U32.max, ``U64.max, ``U128.max,
                 ``Usize.min
                 ] [] [] .wildcard

elab "scalar_tac_preprocess" : tactic =>
  intTacPreprocess scalarTacExtraPreprocess

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac (splitGoalConjs : Bool) : Tactic.TacticM Unit := do
  intTac splitGoalConjs scalarTacExtraPreprocess

elab "scalar_tac" : tactic =>
  scalarTac false

instance (ty : ScalarTy) : HasIntProp (Scalar ty) where
  -- prop_ty is inferred
  prop := λ x => And.intro x.hmin x.hmax

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  intro_has_int_prop_instances
  simp [*]

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac

end Arith
