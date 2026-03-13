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
import Aeneas.CryptoSolver.CryptoRules

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

/-- Try to simplify bitwise operations to arithmetic equivalents.
    Rewrites: `x >>> k → x / 2^k`, `x <<< k → x * 2^k`,
    `x &&& (2^k - 1) → x % 2^k`, and applies bitwise bound lemmas. -/
private def tryBitwiseSimp : TacticM Bool := do
  let saved ← saveState
  try
    -- First: norm_num to normalize numeric literals (e.g., 0xFF → 255)
    -- Then: simp to rewrite bitwise ops to arithmetic
    evalTactic (← `(tactic|
      simp only [
        Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq,
        Nat.and_two_pow_sub_one_eq_mod
      ] at *))
    -- Check if this made progress (goal changed)
    if (← getGoals).isEmpty then return true
    return true  -- progress made, continue with simplified goal
  catch _ =>
    saved.restore; return false

/-- Try to close a bitwise bound by introducing AND/OR/XOR bound lemmas.
    Scans the goal for bitwise ops and introduces their bounds as hypotheses.
    Returns true if the goal is closed; false otherwise (bounds may still have been introduced). -/
private def tryBitwiseBoundLemmas : TacticM Bool := do
  -- Try exact lemmas first
  if ← tryCloseWith (← `(tactic|
    first
    | exact Nat.and_le_left
    | exact Nat.and_le_right)) then return true
  -- Try Nat.and_lt_two_pow for `x &&& y < 2^n` patterns
  if ← tryCloseWith (← `(tactic| (apply Nat.and_lt_two_pow; assumption))) then return true
  -- Scan goal for AND subexpressions and introduce bounds
  let goal ← getMainGoal
  let tgt ← goal.getType >>= instantiateMVars
  let andExprs ← goal.withContext do collectAndExprs tgt #[]
  if andExprs.isEmpty then return false
  try
    for (n, m) in andExprs do
      withMainContext do
        let nStx ← PrettyPrinter.delab n
        let mStx ← PrettyPrinter.delab m
        let freshName ← mkFreshUserName `_hand
        let nameStx := mkIdent freshName
        introduceAndBound nameStx nStx mStx
    -- Try to close with omega or nlinarith after all introductions
    if ← tryCloseWith (← `(tactic| omega)) then return true
    if ← tryCloseWith (← `(tactic| nlinarith)) then return true
    -- Don't restore state — keep the introduced bounds for later stages
    return false
  catch _ =>
    return false
where
  /-- Try to introduce a strict or non-strict AND bound. -/
  introduceAndBound (nameStx : Ident) (nStx mStx : Term) : TacticM Unit := do
    try
      evalTactic (← `(tactic|
        have $nameStx : $nStx &&& $mStx < $mStx + 1 := by
          have := @Nat.and_le_right $nStx $mStx; omega))
    catch _ =>
      try
        evalTactic (← `(tactic|
          have $nameStx : $nStx &&& $mStx ≤ $mStx := Nat.and_le_right))
      catch _ => pure ()
  /-- Collect all `HAnd.hAnd n m` subexpressions using a worklist. -/
  collectAndExprs (root : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let mut result := acc
    let mut worklist : Array Expr := #[root.consumeMData]
    let mut fuel := 50
    while fuel > 0 do
      fuel := fuel - 1
      match worklist.back? with
      | none => break
      | some e =>
        worklist := worklist.pop
        let e := e.consumeMData
        let fn := e.getAppFn
        let args := e.getAppArgs
        if args.size == 6 && fn.isConstOf ``HAnd.hAnd then
          result := result.push (args[4]!, args[5]!)
        for arg in args do
          if arg.isApp then
            worklist := worklist.push arg
    return result

/-- Try to use interval analysis to guide bound introduction.
    Reflects the goal, computes intervals, and if the interval proves the goal,
    introduces explicit `have` statements with the computed bounds. -/
private def tryIntervalGuidedBounds : TacticM Bool := do
  let goal ← getMainGoal
  goal.withContext do
    -- Collect bounds from context
    let env ← collectBounds
    trace[CryptoSolver] "Interval env has {env.map.length} entries"
    for (fv, ivl) in env.map do
      let name := (← fv.getDecl).userName
      trace[CryptoSolver] "  {name}: [{ivl.lo}, {ivl.hi}]"
    -- Parse the goal as a comparison
    let tgt ← goal.getType >>= instantiateMVars
    let some (lhs, rhs, _isStrict) ← parseComparison tgt | return false
    -- Reflect the LHS expression
    let aexpr ← toAExpr lhs
    -- Compute interval
    let ivl := propagate env aexpr
    trace[CryptoSolver] "Interval analysis: {repr ivl} for goal"
    -- Check if the interval directly proves the bound
    if let some bound ← extractIntLit rhs then
      if ivl.hi < bound then
        trace[CryptoSolver] "Interval analysis proves goal: hi={ivl.hi} < {bound}"
        -- The interval analysis says this should be provable.
        -- Try to introduce intermediate bounds for subexpressions
        -- to help omega/nlinarith close the goal.
        return ← tryIntroduceSubexprBounds aexpr env
    return false
where
  /-- Introduce `have` statements for division and modular subexpression bounds
      discovered by interval analysis. -/
  tryIntroduceSubexprBounds (expr : AExpr) (env : IntervalEnv) : TacticM Bool := do
    match expr with
    | .div a b =>
      -- For `a / b`, if we know `a < N` and `b = 2^k`, try introducing `a / b < N / 2^k`
      let aIvl := propagate env a
      let bIvl := propagate env b
      if bIvl.lo > 0 then
        let divHi := aIvl.hi / bIvl.lo
        trace[CryptoSolver] "Division subexpr: a in {repr aIvl}, b in {repr bIvl}, div bound: {divHi}"
        -- Try to close with omega (which handles division natively)
        if ← tryCloseWith (← `(tactic| omega)) then return true
      -- Recurse on the numerator
      let _ ← tryIntroduceSubexprBounds a env
      if ← tryCloseWith (← `(tactic| omega)) then return true
      return false
    | .mul a b =>
      -- For `a * b`, if we know bounds, try saturation
      let _ ← tryIntroduceSubexprBounds a env
      let _ ← tryIntroduceSubexprBounds b env
      return false
    | _ => return false

/-- Scan the goal for `_ % n` subexpressions and introduce `_ % n < n` as hypotheses.
    Returns true if the goal is closed; false otherwise (bounds may still have been introduced). -/
private def tryModSubexprBounds : TacticM Bool := do
  let goal ← getMainGoal
  let tgt ← goal.getType >>= instantiateMVars
  let modExprs ← goal.withContext do collectModExprs tgt #[]
  if modExprs.isEmpty then return false
  try
    for (x, n) in modExprs do
      withMainContext do
        let xStx ← PrettyPrinter.delab x
        let nStx ← PrettyPrinter.delab n
        let freshName ← mkFreshUserName `_hmod
        let nameStx := mkIdent freshName
        try
          evalTactic (← `(tactic|
            have $nameStx : $xStx % $nStx < $nStx := Nat.mod_lt _ (by omega)))
        catch _ => pure ()
    if ← tryCloseWith (← `(tactic| omega)) then return true
    if ← tryCloseWith (← `(tactic| nlinarith)) then return true
    return false
  catch _ => return false
where
  /-- Collect all `HMod.hMod x n` subexpressions using a worklist. -/
  collectModExprs (root : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let mut result := acc
    let mut worklist : Array Expr := #[root.consumeMData]
    let mut fuel := 50
    while fuel > 0 do
      fuel := fuel - 1
      match worklist.back? with
      | none => break
      | some e =>
        worklist := worklist.pop
        let e := e.consumeMData
        let fn := e.getAppFn
        let args := e.getAppArgs
        if args.size == 6 && fn.isConstOf ``HMod.hMod then
          result := result.push (args[4]!, args[5]!)
        for arg in args do
          if arg.isApp then
            worklist := worklist.push arg
    return result

/-- Compute the smallest power of 2 that is ≥ n. -/
private def nextPow2 (n : Nat) : Nat :=
  loop 1 64
where
  loop (p : Nat) : Nat → Nat
    | 0 => p
    | fuel + 1 => if p >= n then p else loop (p * 2) fuel

/-- Try to introduce `have nameStx : divExpr < boundVal` by solving the proof obligation
    using omega or nlinarith.

    Uses syntax-level `have ... := by omega` so that the elaborator creates expressions
    with the same structure that omega expects (e.g., `@OfNat.ofNat` wrappers around
    numeric literals, rather than raw `Expr.lit`). Meta-level expression construction
    via `mkAppM` + `mkRawNatLit` produces structurally different (though defEq)
    expressions that omega cannot match against hypotheses.

    Detects failure via message-log count: `evalTactic` with `have ... := by omega`
    does not throw when the proof tactic fails; instead it logs an error message.
    We detect the message count increase and restore state on failure. -/
private def tryIntroduceDivHave (divExpr : Expr) (boundVal : Nat) : TacticM Bool := do
  let saved ← saveState
  try
    let goal ← getMainGoal
    goal.withContext do
      let divStx ← PrettyPrinter.delab divExpr
      let boundStx := Syntax.mkNumLit (toString boundVal)
      let freshName ← mkFreshUserName `_hdiv
      let nameStx := mkIdent freshName
      -- Try omega first (handles div by constants well)
      let msgsBefore := (← Core.getMessageLog).toList.length
      evalTactic (← `(tactic| have $nameStx : $divStx < $boundStx := by omega))
      let msgsAfter := (← Core.getMessageLog).toList.length
      if msgsAfter > msgsBefore then
        -- omega failed (error logged but not thrown); try nlinarith
        saved.restore
        let saved2 ← saveState
        let msgsBefore2 := (← Core.getMessageLog).toList.length
        evalTactic (← `(tactic| have $nameStx : $divStx < $boundStx := by nlinarith))
        let msgsAfter2 := (← Core.getMessageLog).toList.length
        if msgsAfter2 > msgsBefore2 then
          saved2.restore
          return false
      trace[CryptoSolver] "tryIntroduceDivHave: succeeded for bound {boundVal}"
      return true
  catch _ =>
    saved.restore
    return false

/-- Try to automate nested mul+div patterns like `(a * b / 2^k) * c / 2^k`.
    Scans the goal for division subexpressions and introduces bounds as `have` statements.
    Processes inner divisions first so outer bounds can use the inner ones. -/
private def tryNestedDivBounds : TacticM Bool := do
  trace[CryptoSolver] "tryNestedDivBounds: entering"
  let goal ← getMainGoal
  goal.withContext do
    let env ← collectBounds
    let tgt ← goal.getType >>= instantiateMVars
    let some (lhs, _rhs, _isStrict) ← parseComparison tgt | return false
    let aexpr ← toAExpr lhs
    -- Find division subexpressions and try to introduce bounds for them
    let divExprs ← collectDivSubexprs lhs
    trace[CryptoSolver] "tryNestedDivBounds: found {divExprs.size} div subexprs"
    if divExprs.isEmpty then return false
    -- Process innermost first (reverse: outer divs are collected first)
    let divExprs := divExprs.reverse
    let mut madeProgress := false
    for (divExpr, divAExpr) in divExprs do
      let ivl := propagate env divAExpr
      if ivl.hi > 0 && !ivl.isTop then
        let tightBound := (ivl.hi + 1).toNat
        let looseBound := nextPow2 tightBound
        trace[CryptoSolver] "tryNestedDivBounds: ivl.hi={ivl.hi}, trying bound {looseBound}"
        if ← tryIntroduceDivHave divExpr looseBound then
          madeProgress := true
          if ← tryCloseWith (← `(tactic| omega)) then return true
          if ← tryCloseWith (← `(tactic| nlinarith)) then return true
        else if looseBound != tightBound then
          trace[CryptoSolver] "tryNestedDivBounds: falling back to tight bound {tightBound}"
          if ← tryIntroduceDivHave divExpr tightBound then
            madeProgress := true
            if ← tryCloseWith (← `(tactic| omega)) then return true
            if ← tryCloseWith (← `(tactic| nlinarith)) then return true
    return madeProgress
where
  /-- Collect all division subexpressions from the LHS Lean expression. -/
  collectDivSubexprs (lhsExpr : Expr) : TacticM (Array (Expr × AExpr)) := do
    let goal ← getMainGoal
    goal.withContext do
      let mut result : Array (Expr × AExpr) := #[]
      result ← collectDivsFromExpr lhsExpr result
      return result
  collectDivsFromExpr (e : Expr) (acc : Array (Expr × AExpr)) : (fuel : Nat := 20) →
      TacticM (Array (Expr × AExpr))
    | 0 => return acc
    | fuel + 1 => do
      let e := e.consumeMData
      let fn := e.getAppFn
      let args := e.getAppArgs
      if args.size == 6 && fn.isConstOf ``HDiv.hDiv then
        -- This is a division; also recurse into numerator
        let aexpr ← toAExpr e
        let acc := acc.push (e, aexpr)
        collectDivsFromExpr args[4]! acc fuel
      else if args.size == 6 then
        -- Binary op: recurse into both operands
        let acc ← collectDivsFromExpr args[4]! acc fuel
        collectDivsFromExpr args[5]! acc fuel
      else
        return acc

/-- Collect all `HMul.hMul` subexpressions from an expression using a worklist.
    Returns pairs of (left operand, right operand). -/
private def collectMulSubexprs (root : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut result : Array (Expr × Expr) := #[]
  let mut worklist : Array Expr := #[root.consumeMData]
  let mut fuel := 100
  while fuel > 0 do
    fuel := fuel - 1
    match worklist.back? with
    | none => break
    | some e =>
      worklist := worklist.pop
      let e := e.consumeMData
      let fn := e.getAppFn
      let args := e.getAppArgs
      if args.size == 6 && fn.isConstOf ``HMul.hMul then
        result := result.push (args[4]!, args[5]!)
      for arg in args do
        if arg.isApp then
          worklist := worklist.push arg
  return result

/-- Find a strict bound hypothesis whose LHS is definitionally equal to `e`. -/
private def findBoundFor (e : Expr) (bounds : Array StrictBound) : MetaM (Option StrictBound) := do
  for b in bounds do
    if ← isDefEq b.lhsExpr e then
      return some b
  return none

/-- Run one round of goal-directed multiplication saturation.
    Scans the goal for `*` subexpressions, finds bounds for their operands,
    and introduces product bounds. Only targets products in the goal. -/
private def doMulSaturationRound : TacticM Bool := do
  let goal ← getMainGoal
  let tgt ← goal.getType >>= instantiateMVars
  trace[CryptoSolver] "doMulSaturationRound: goal type = {tgt}"
  let mulExprs ← goal.withContext do collectMulSubexprs tgt
  trace[CryptoSolver] "doMulSaturationRound: found {mulExprs.size} mul subexprs"
  if mulExprs.isEmpty then return false
  let bounds ← collectStrictBounds
  trace[CryptoSolver] "doMulSaturationRound: found {bounds.size} strict bounds"
  if bounds.isEmpty then return false
  let mut madeProgress := false
  for (lhsE, rhsE) in mulExprs do
    let pair ← withMainContext do
      let lb ← findBoundFor lhsE bounds
      let rb ← findBoundFor rhsE bounds
      match lb, rb with
      | some bi, some bj => return some (bi, bj)
      | _, _ => return none
    match pair with
    | none => continue
    | some (bi, bj) =>
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
        let msgsBefore := (← Core.getMessageLog).toList.length
        evalTactic (← `(tactic|
          have $nameStx : $prodLhsStx < $prodRhsStx := by nlinarith [$hiStx, $hjStx]))
        let msgsAfter := (← Core.getMessageLog).toList.length
        if msgsAfter > msgsBefore then
          -- nlinarith failed silently; restore
          saved.restore
          continue
        madeProgress := true
        if ← tryCloseWith (← `(tactic| omega)) then return true
        if ← tryCloseWith (← `(tactic| nlinarith)) then return true
      catch _ =>
        saved.restore
  return madeProgress

/-- The core solving loop for a single goal. Tries multiple strategies. -/
def solveSingleGoal : TacticM Unit := do
  -- Step 0: Simplify bitwise operations to arithmetic
  let _ ← tryBitwiseSimp
  if (← getGoals).isEmpty then return
  -- Fast path: omega for linear goals
  if ← tryCloseWith (← `(tactic| omega)) then return
  -- Bitwise bound lemmas (after simp, some AND/OR/XOR may remain)
  if ← tryBitwiseBoundLemmas then return
  -- Mod bounds: for `_ % n` subexpressions, introduce `_ % n < n`
  if ← tryModSubexprBounds then return
  -- Simple exact lemmas
  if ← tryCloseWith (← `(tactic| exact Nat.mod_lt _ (by omega))) then return
  if ← tryCloseWith (← `(tactic| exact Nat.div_mul_le_self _ _)) then return
  -- nlinarith for non-linear goals (degree ≤ 2)
  if ← tryCloseWith (← `(tactic| nlinarith)) then return
  -- Signed multiplication: try nlinarith with sq_nonneg hints (Int goals only)
  let tgtForNatCheck ← (← getMainGoal).getType >>= instantiateMVars
  let goalIsNat := tgtForNatCheck.getAppArgs.size >= 1 &&
                   tgtForNatCheck.getAppArgs[0]!.isConstOf ``Nat
  if !goalIsNat then
    if ← trySqNonnegHints then return
  -- Try interval-guided bound introduction
  if ← tryIntervalGuidedBounds then return
  -- Saturation loop: alternate mul saturation ↔ div bound introduction
  trace[CryptoSolver] "Entering saturation loop"
  for round in [:3] do
    trace[CryptoSolver] "Saturation round {round}"
    -- Multiplication saturation
    let mulProgress ← doMulSaturationRound
    if (← getGoals).isEmpty then return
    if ← tryCloseWith (← `(tactic| omega)) then return
    if ← tryCloseWith (← `(tactic| nlinarith)) then return
    -- Division bound introduction (uses mul bounds from above)
    let divProgress ← tryNestedDivBounds
    if (← getGoals).isEmpty then return
    if ← tryCloseWith (← `(tactic| omega)) then return
    if ← tryCloseWith (← `(tactic| nlinarith)) then return
    if !mulProgress && !divProgress then break
  -- Final attempts with all accumulated hypotheses
  if ← tryCloseWith (← `(tactic| omega)) then return
  if ← tryCloseWith (← `(tactic| nlinarith)) then return
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
