import Lean
import Aeneas.CryptoSolver.Init

/-!
# CryptoSolver internal expression representation

This module defines `AExpr`, an internal representation of arithmetic expressions
used for meta-level interval analysis. This is NOT a reflected type — it is used
only within the `MetaM` monad for analysis and proof planning.
-/

namespace Aeneas.CryptoSolver

open Lean

/-- Internal arithmetic expression for interval analysis.
    Variables are referenced by their Lean `FVarId`.
    This representation is used at the meta level only. -/
inductive AExpr where
  | lit   : Int → AExpr
  | var   : FVarId → AExpr
  | add   : AExpr → AExpr → AExpr
  | sub   : AExpr → AExpr → AExpr
  | mul   : AExpr → AExpr → AExpr
  | div   : AExpr → AExpr → AExpr
  | mod   : AExpr → AExpr → AExpr
  | neg   : AExpr → AExpr
  | pow   : AExpr → Nat → AExpr
  | shl   : AExpr → Nat → AExpr
  | shr   : AExpr → Nat → AExpr
  | band  : AExpr → AExpr → AExpr
  | bor   : AExpr → AExpr → AExpr
  | bxor  : AExpr → AExpr → AExpr
  /-- Opaque subexpression we can't analyze further -/
  | unknown : Expr → AExpr
  deriving Inhabited

/-- Does this expression contain any multiplication or non-linear operations? -/
def AExpr.isNonLinear : AExpr → Bool
  | .mul _ _ | .div _ _ | .mod _ _ | .pow _ _ => true
  | .add a b | .sub a b => a.isNonLinear || b.isNonLinear
  | .neg a => a.isNonLinear
  | .shl a _ | .shr a _ => a.isNonLinear
  | .band a b | .bor a b | .bxor a b => a.isNonLinear || b.isNonLinear
  | _ => false

/-- Collect all free variable IDs referenced in the expression -/
def AExpr.fvarIds : AExpr → List FVarId
  | .lit _ | .unknown _ => []
  | .var fv => [fv]
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .band a b | .bor a b | .bxor a b => a.fvarIds ++ b.fvarIds
  | .neg a | .pow a _ | .shl a _ | .shr a _ => a.fvarIds

end Aeneas.CryptoSolver
