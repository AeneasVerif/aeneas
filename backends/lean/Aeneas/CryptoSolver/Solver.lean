import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Aeneas.CryptoSolver.Init
import Aeneas.CryptoSolver.Expr
import Aeneas.CryptoSolver.Interval
import Aeneas.CryptoSolver.IntervalAnalysis
import Aeneas.CryptoSolver.Reflect
import Aeneas.CryptoSolver.Certify
import Aeneas.CryptoSolver.Preprocess
import Aeneas.CryptoSolver.Dispatch
import Aeneas.CryptoSolver.ModRing

namespace Aeneas.CryptoSolver

open Lean Meta Elab Tactic

/-- Info about a strict upper bound hypothesis: `lhsExpr < rhsExpr`. -/
structure StrictBound where
  hypName : Name
  lhsExpr : Expr   -- the bounded expression
  rhsExpr : Expr   -- the upper bound
  deriving Inhabited

/-- Collect strict upper bound hypotheses (`_ < _`) from the local context. -/
private def collectStrictBounds : TacticM (Array StrictBound) := do
  let goal ← getMainGoal
  goal.withContext do
    let ctx ← getLCtx
    let mut result : Array StrictBound := #[]
    for decl in ctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      let fn := ty.getAppFn
      let args := ty.getAppArgs
      if args.size >= 4 && fn.isConstOf ``LT.lt then
        result := result.push { hypName := decl.userName,
                                lhsExpr := args[2]!, rhsExpr := args[3]! }
    return result

/-- Run a tactic and return true only if it closes all current goals. -/
private def tryCloseWith (tac : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic tac
    if (← getGoals).isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- For Int goals with multiplication, try nlinarith with sq_nonneg hints.
    sq_nonneg (x+y) and sq_nonneg (x-y) provide quadratic witnesses that
    help nlinarith bound signed products. -/
private def trySqNonnegHints : TacticM Bool := do
  let goal ← getMainGoal
  goal.withContext do
    let ctx ← getLCtx
    let mut varNames : Array Name := #[]
    let mut varStxs : Array (TSyntax `term) := #[]
    for decl in ctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      let fn := ty.getAppFn
      let args := ty.getAppArgs
      if args.size >= 4 && (fn.isConstOf ``LT.lt || fn.isConstOf ``LE.le) then
        let lhs := args[2]!
        if lhs.isFVar then
          let name := (ctx.get! lhs.fvarId!).userName
          if !varNames.contains name then
            varNames := varNames.push name
            varStxs := varStxs.push (mkIdent name)
    if varStxs.size < 2 then return false
    -- Build sq_nonneg hints
    let mut hints : Array (TSyntax `term) := #[]
    for v in varStxs do
      hints := hints.push (← `(sq_nonneg $v))
    for i in [:varStxs.size] do
      for j in [i+1:varStxs.size] do
        let vi := varStxs[i]!
        let vj := varStxs[j]!
        hints := hints.push (← `(sq_nonneg ($vi + $vj)))
        hints := hints.push (← `(sq_nonneg ($vi - $vj)))
    tryCloseWith (← `(tactic| nlinarith [$[$hints],*]))

/-- The core solving loop for a single goal. Tries multiple strategies. -/
def solveSingleGoal : TacticM Unit := do
  -- Fast path: omega for linear goals
  if ← tryCloseWith (← `(tactic| omega)) then return
  -- Mod bound: _ % n < n
  if ← tryCloseWith (← `(tactic| exact Nat.mod_lt _ (by omega))) then return
  -- Division bound: a / d * d ≤ a
  if ← tryCloseWith (← `(tactic| exact Nat.div_mul_le_self _ _)) then return
  -- nlinarith for non-linear goals (degree ≤ 2)
  if ← tryCloseWith (← `(tactic| nlinarith)) then return
  -- Signed multiplication: try nlinarith with sq_nonneg hints
  if ← trySqNonnegHints then return
  -- Multiplication saturation: introduce product bounds one at a time,
  -- trying to close the goal after each introduction
  for _ in [:3] do  -- up to 3 rounds of saturation
    let bounds ← collectStrictBounds
    if bounds.size < 2 then break
    let mut madeProgress := false
    for i in [:bounds.size] do
      for j in [i+1:bounds.size] do
        let bi := bounds[i]!
        let bj := bounds[j]!
        let saved ← saveState
        try
          let (prodLhsStx, prodRhsStx, hiStx, hjStx, nameStx) ←
            withMainContext do
              let prodLhs ← mkAppM ``HMul.hMul #[bi.lhsExpr, bj.lhsExpr]
              let prodRhs ← mkAppM ``HMul.hMul #[bi.rhsExpr, bj.rhsExpr]
              let s1 ← PrettyPrinter.delab prodLhs
              let s2 ← PrettyPrinter.delab prodRhs
              let freshName ← mkFreshUserName `_hprod
              return (s1, s2, mkIdent bi.hypName, mkIdent bj.hypName,
                      mkIdent freshName)
          evalTactic (← `(tactic|
            have $nameStx : $prodLhsStx < $prodRhsStx := by nlinarith [$hiStx, $hjStx]))
          madeProgress := true
          -- After each new hypothesis, try to close the goal
          if ← tryCloseWith (← `(tactic| omega)) then return
          if ← tryCloseWith (← `(tactic| nlinarith)) then return
        catch _ =>
          saved.restore
    if !madeProgress then break
  -- Final attempts
  if ← tryCloseWith (← `(tactic| linarith)) then return
  throwError "crypto_solver: could not solve goal"

/-- Main `crypto_solver` tactic -/
elab "crypto_solver" : tactic => withMainContext do
  trace[CryptoSolver] "Starting crypto_solver"
  let goal ← getMainGoal
  let goals ← preprocessGoal goal
  let mut remaining : List MVarId := []
  for g in goals do
    setGoals [g]
    let saved ← saveState
    try
      solveSingleGoal
      if !(← getGoals).isEmpty then
        saved.restore
        remaining := remaining ++ [g]
    catch _ =>
      saved.restore
      remaining := remaining ++ [g]
  if remaining.isEmpty then
    setGoals []
  else
    setGoals remaining
    throwError "crypto_solver: could not solve {remaining.length} subgoal(s)"

end Aeneas.CryptoSolver
