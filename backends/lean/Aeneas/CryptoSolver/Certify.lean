import Lean
import Aeneas.CryptoSolver.Init
import Aeneas.CryptoSolver.Expr
import Aeneas.CryptoSolver.Interval
import Aeneas.CryptoSolver.IntervalAnalysis
import Aeneas.CryptoSolver.Reflect

namespace Aeneas.CryptoSolver

open Lean Meta Elab Tactic

/-- Information about a multiplication subexpression and its computed bound -/
structure MulBound where
  lhsExpr : Expr
  rhsExpr : Expr
  lhsUpper : Int
  rhsUpper : Int
  lhsNonneg : Bool
  rhsNonneg : Bool

/-- Walk an `AExpr` and collect all multiplication subexpressions with their bounds. -/
partial def collectMulBounds (env : IntervalEnv) (leanExpr : Expr) (aexpr : AExpr)
    : MetaM (List MulBound) := do
  match aexpr with
  | .mul lhs rhs =>
    let lhsIvl := propagate env lhs
    let rhsIvl := propagate env rhs
    let args := leanExpr.getAppArgs
    if h : args.size == 6 then
      let lhsE := args[4]!
      let rhsE := args[5]!
      let bound : MulBound := {
        lhsExpr := lhsE, rhsExpr := rhsE,
        lhsUpper := lhsIvl.hi, rhsUpper := rhsIvl.hi,
        lhsNonneg := lhsIvl.isNonneg, rhsNonneg := rhsIvl.isNonneg
      }
      let lhsBounds ← collectMulBounds env lhsE lhs
      let rhsBounds ← collectMulBounds env rhsE rhs
      return [bound] ++ lhsBounds ++ rhsBounds
    else return []
  | .add lhs rhs | .sub lhs rhs =>
    let args := leanExpr.getAppArgs
    if h : args.size == 6 then
      let lb ← collectMulBounds env args[4]! lhs
      let rb ← collectMulBounds env args[5]! rhs
      return lb ++ rb
    else return []
  | .neg inner =>
    let args := leanExpr.getAppArgs
    if h : args.size == 3 then
      return ← collectMulBounds env args[2]! inner
    else return []
  | _ => return []

/-- Create a Lean expression for a natural number literal -/
def mkNatLitExpr (n : Nat) : Expr :=
  mkRawNatLit n

end Aeneas.CryptoSolver
