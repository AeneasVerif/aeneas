import Lean
import Aeneas.CryptoSolver.Init
import Aeneas.CryptoSolver.Expr
import Aeneas.CryptoSolver.Reflect

namespace Aeneas.CryptoSolver

open Lean Meta

/-- Classification of a goal -/
inductive GoalKind where
  | boundsLt  : Expr → Expr → GoalKind   -- expr < bound
  | boundsLe  : Expr → Expr → GoalKind   -- expr ≤ bound
  | boundsGe  : Expr → Expr → GoalKind   -- bound ≤ expr
  | boundsGt  : Expr → Expr → GoalKind   -- bound < expr
  | equality  : Expr → Expr → GoalKind   -- expr₁ = expr₂
  | linear    : GoalKind                  -- Pure linear arithmetic
  | unknown   : GoalKind                  -- Can't classify
  deriving Inhabited

/-- Classify a goal expression -/
def classifyGoal (goal : MVarId) : MetaM GoalKind := do
  goal.withContext do
    let tgt ← goal.getType
    let tgt ← whnfD tgt
    let fn := tgt.getAppFn
    let args := tgt.getAppArgs
    -- LT.lt α inst a b (4 args)
    if args.size == 4 && fn.isConstOf ``LT.lt then
      return .boundsLt args[2]! args[3]!
    -- LE.le α inst a b (4 args)
    if args.size == 4 && fn.isConstOf ``LE.le then
      return .boundsLe args[2]! args[3]!
    -- Eq α a b (3 args)
    if args.size == 3 && fn.isConstOf ``Eq then
      return .equality args[1]! args[2]!
    -- GE/GT aren't primitive in Lean; they desugar to LE/LT
    -- Check for Not (LT/LE) patterns
    return .unknown

/-- Does this goal involve non-linear arithmetic? -/
def isNonLinear (goal : MVarId) : MetaM Bool := do
  let kind ← classifyGoal goal
  match kind with
  | .boundsLt lhs _ | .boundsLe lhs _ =>
    let aexpr ← toAExpr lhs
    return aexpr.isNonLinear
  | .boundsGe _ rhs | .boundsGt _ rhs =>
    let aexpr ← toAExpr rhs
    return aexpr.isNonLinear
  | .equality lhs rhs =>
    let al ← toAExpr lhs
    let ar ← toAExpr rhs
    return al.isNonLinear || ar.isNonLinear
  | _ => return false

end Aeneas.CryptoSolver
