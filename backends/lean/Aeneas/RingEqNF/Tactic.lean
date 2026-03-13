/-
Copyright (c) 2024 Aeneas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Mathlib.Tactic.Ring.RingNF

/-!
# `ring_eq_nf` Tactic

The `ring_eq_nf` tactic normalizes equalities over (semi)ring expressions by
canceling common additive terms between the left and right sides.

For example, `ring_eq_nf` transforms:
- `3 * x + 2 * y = x + 3 * y`  →  `2 * x = y`
- `x + y = y`                   →  `x = 0`
- `a + b = a + b`               →  closes the goal

## Algorithm
1. Apply `ring_nf` to normalize both sides into a canonical polynomial form
2. Parse each side as a sum of `coefficient * monomial` pairs
3. For each monomial appearing on both sides, subtract the minimum coefficient
4. Reconstruct the simplified equality, using `ring` to prove the decomposition
-/

open Lean Meta Elab Tactic

namespace Aeneas.RingEqNF

/-! ## Helper theorems -/

/-- Transform a goal: if `a = a' + c` and `b = b' + c` (provable by `ring`),
    then `a' = b'` implies `a = b`. No cancellation typeclass needed. -/
theorem goal_cancel_right {α : Type*} [Add α]
    {a b a' b' c : α}
    (hlhs : a = a' + c) (hrhs : b = b' + c) (heq : a' = b') : a = b := by
  rw [hlhs, hrhs, heq]

/-- Transform a hypothesis: if `a = a' + c` and `b = b' + c` (provable by `ring`),
    and `a = b`, then `a' = b'`. Requires additive right cancellation. -/
theorem hyp_cancel_right {α : Type*} [Add α] [IsRightCancelAdd α]
    {a b a' b' c : α}
    (hlhs : a = a' + c) (hrhs : b = b' + c) (hab : a = b) : a' = b' := by
  have h : a' + c = b' + c := by rw [← hlhs, hab, hrhs]
  exact add_right_cancel h

/-! ## Expression parsing utilities -/

/-- Extract a natural number from an expression. Handles both `OfNat.ofNat`
    patterns and raw `Nat` literals. -/
private def exprToNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if let some n := e.nat? then some n
  else if let some n := e.rawNatLit? then some n
  else none

/-- Flatten a left-associated addition tree into a list of additive terms.
    After `ring_nf`, addition is left-associated: `((a + b) + c) + d`. -/
private partial def flattenAdd (e : Expr) : List Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs]) =>
    flattenAdd lhs ++ [rhs]
  | _ => [e]

/-- A monomial with its coefficient: represents `coeff * base`. -/
private structure CMonomial where
  coeff : Nat
  base : Option Expr  -- `none` for pure constant (numeric) terms
  deriving Inhabited

/-- Extract `(coefficient, monomial_base)` from a normalized additive term.
    Handles both `n * m` and `m * n` forms since `ring_nf` may place the coefficient
    on either side (typically `variable * coefficient`).
    - `n * m` or `m * n` where one is a numeral → `(n, some m)`
    - `m` (non-numeral)                        → `(1, some m)`
    - `n` (numeral)                             → `(n, none)` -/
private def parseTerm (e : Expr) : CMonomial :=
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    -- Try coefficient on the left: n * m
    match exprToNat? a with
    | some n => { coeff := n, base := some b }
    | none =>
      -- Try coefficient on the right: m * n (ring_nf convention)
      match exprToNat? b with
      | some n => { coeff := n, base := some a }
      | none => { coeff := 1, base := some e }
  | _ =>
    match exprToNat? e with
    | some n => { coeff := n, base := none }
    | none => { coeff := 1, base := some e }

/-- Parse a normalized expression into a list of coefficient-monomial pairs. -/
private def parseNormExpr (e : Expr) : List CMonomial :=
  (flattenAdd e).map parseTerm

/-! ## Cancellation algorithm -/

/-- Check if two monomial bases match (using definitional equality). -/
private def sameBase (a b : CMonomial) : MetaM Bool :=
  match a.base, b.base with
  | none,   none   => return true
  | some x, some y => isDefEq x y
  | _,      _      => return false

/-- Result of the cancellation: remaining terms on each side plus common terms. -/
private structure CancelResult where
  lhsRem : List CMonomial
  rhsRem : List CMonomial
  common : List CMonomial

/-- Cancel common monomials between LHS and RHS term lists.
    For each monomial appearing on both sides, subtracts `min(coeff_lhs, coeff_rhs)`. -/
private def cancelCommon (lhs rhs : List CMonomial) : MetaM CancelResult := do
  let mut lhsRem : List CMonomial := []
  let mut rhsRem := rhs
  let mut common : List CMonomial := []
  for lm in lhs do
    let mut found := false
    let mut newRhsRem : List CMonomial := []
    for rm in rhsRem do
      if !found && (← sameBase lm rm) then
        found := true
        let minC := min lm.coeff rm.coeff
        if minC > 0 then
          common := common ++ [{ coeff := minC, base := lm.base }]
        if lm.coeff > minC then
          lhsRem := lhsRem ++ [{ coeff := lm.coeff - minC, base := lm.base }]
        if rm.coeff > minC then
          newRhsRem := newRhsRem ++ [{ coeff := rm.coeff - minC, base := rm.base }]
      else
        newRhsRem := newRhsRem ++ [rm]
    if found then
      rhsRem := newRhsRem
    else
      lhsRem := lhsRem ++ [lm]
  return { lhsRem, rhsRem, common }

/-! ## Expression construction -/

/-- Create a well-typed numeral `(n : ty)`. -/
private def mkOfNat (ty : Expr) (n : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some ty, some (mkNatLit n), none]

/-- Build the expression for a single monomial.
    Uses `base * coeff` ordering to match `ring_nf`'s convention. -/
private def buildMonomialExpr (ty : Expr) (m : CMonomial) : MetaM Expr := do
  match m.base with
  | none => mkOfNat ty m.coeff
  | some base =>
    if m.coeff == 1 then
      return base
    else
      let coeffExpr ← mkOfNat ty m.coeff
      mkAppM ``HMul.hMul #[base, coeffExpr]

/-- Build a sum expression from a list of monomials.
    Returns `0` for an empty list. -/
private def buildSumExpr (ty : Expr) (terms : List CMonomial) : MetaM Expr := do
  match terms with
  | [] => mkOfNat ty 0
  | [t] => buildMonomialExpr ty t
  | t :: ts =>
    let first ← buildMonomialExpr ty t
    ts.foldlM (fun acc m => do
      let mExpr ← buildMonomialExpr ty m
      mkAppM ``HAdd.hAdd #[acc, mExpr]) first

/-! ## Core tactic implementations -/

/-- Run `ring_nf` targeting a specific hypothesis, working around location syntax construction. -/
private def evalRingNfAtHyp (hName : Name) : TacticM Unit := do
  let env ← getEnv
  let stx ← ofExcept <| Lean.Parser.runParserCategory env `tactic s!"ring_nf at {hName}"
  evalTactic stx

/-- Run `ring` on a specific goal (metavariable). -/
private def closeByRing (mvarId : MVarId) : TacticM Unit := do
  let saved ← getGoals
  setGoals [mvarId]
  try
    evalTactic (← `(tactic| ring))
  finally
    setGoals saved

/-- Core implementation of `ring_eq_nf` on the goal. -/
private def ringEqNfGoal : TacticM Unit := do
  -- Step 1: Normalize with ring_nf
  try evalTactic (← `(tactic| ring_nf))
  catch _ => return
  -- Step 2: Get the current goal
  let goals ← getGoals
  if goals.isEmpty then return
  let mvarId := goals.head!
  let restGoals := goals.tail!
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    -- Step 3: Must be an equality
    let some (ty, lhs, rhs) := target.eq?
      | return
    -- Step 4: Parse both sides into coefficient-monomial lists
    let lhsTerms := parseNormExpr lhs
    let rhsTerms := parseNormExpr rhs
    -- Step 5: Cancel common terms
    let result ← cancelCommon lhsTerms rhsTerms
    if result.common.isEmpty then return
    -- Step 6: If everything cancels, try closing the goal with ring
    if result.lhsRem.isEmpty && result.rhsRem.isEmpty then
      let saved ← saveState
      try
        setGoals [mvarId]
        evalTactic (← `(tactic| ring))
        setGoals restGoals
        return
      catch _ =>
        restoreState saved
        return
    -- Step 7: Build the simplified expressions
    let newLhs ← buildSumExpr ty result.lhsRem
    let newRhs ← buildSumExpr ty result.rhsRem
    let common ← buildSumExpr ty result.common
    -- Step 8: Construct the proof via goal_cancel_right
    --   hlhs : lhs = newLhs + common     (proved by ring)
    --   hrhs : rhs = newRhs + common     (proved by ring)
    --   heq  : newLhs = newRhs           (new goal for the user)
    let newLhsPlusCommon ← mkAppM ``HAdd.hAdd #[newLhs, common]
    let newRhsPlusCommon ← mkAppM ``HAdd.hAdd #[newRhs, common]
    let hlhsType ← mkEq lhs newLhsPlusCommon
    let hrhsType ← mkEq rhs newRhsPlusCommon
    let heqType ← mkEq newLhs newRhs
    let hlhsMVar ← mkFreshExprMVar (some hlhsType)
    let hrhsMVar ← mkFreshExprMVar (some hrhsType)
    let heqMVar ← mkFreshExprMVar (some heqType)
    let proof ← mkAppM ``goal_cancel_right #[hlhsMVar, hrhsMVar, heqMVar]
    let saved ← saveState
    try
      mvarId.assign proof
      closeByRing hlhsMVar.mvarId!
      closeByRing hrhsMVar.mvarId!
      setGoals (heqMVar.mvarId! :: restGoals)
    catch _ =>
      restoreState saved

/-- Core implementation of `ring_eq_nf` on a hypothesis. -/
private def ringEqNfAtHyp (hName : Name) : TacticM Unit := do
  -- Step 1: Normalize with ring_nf at h
  try evalRingNfAtHyp hName
  catch _ => return
  -- Step 2: Get the hypothesis
  let mvarId ← getMainGoal
  mvarId.withContext do
    let hDecl ← getLocalDeclFromUserName hName
    let hType ← instantiateMVars hDecl.type
    -- Step 3: Must be an equality
    let some (ty, lhs, rhs) := hType.eq?
      | return
    -- Step 4: Parse and cancel
    let lhsTerms := parseNormExpr lhs
    let rhsTerms := parseNormExpr rhs
    let result ← cancelCommon lhsTerms rhsTerms
    if result.common.isEmpty then return
    if result.lhsRem.isEmpty && result.rhsRem.isEmpty then return
    -- Step 5: Build simplified expressions
    let newLhs ← buildSumExpr ty result.lhsRem
    let newRhs ← buildSumExpr ty result.rhsRem
    let common ← buildSumExpr ty result.common
    -- Step 6: Construct the proof via hyp_cancel_right
    let newLhsPlusCommon ← mkAppM ``HAdd.hAdd #[newLhs, common]
    let newRhsPlusCommon ← mkAppM ``HAdd.hAdd #[newRhs, common]
    let hlhsType ← mkEq lhs newLhsPlusCommon
    let hrhsType ← mkEq rhs newRhsPlusCommon
    let hlhsMVar ← mkFreshExprMVar (some hlhsType)
    let hrhsMVar ← mkFreshExprMVar (some hrhsType)
    let newHType ← mkEq newLhs newRhs
    let newHProof ← mkAppM ``hyp_cancel_right #[hlhsMVar, hrhsMVar, hDecl.toExpr]
    let saved ← saveState
    try
      closeByRing hlhsMVar.mvarId!
      closeByRing hrhsMVar.mvarId!
      -- Replace hypothesis: assert new, clear old
      let mvarId ← mvarId.assert hName newHType newHProof
      let (_, mvarId) ← mvarId.intro1P
      let mvarId ← mvarId.clear hDecl.fvarId
      replaceMainGoal [mvarId]
    catch _ =>
      restoreState saved

/-! ## Tactic syntax -/

syntax "ring_eq_nf" : tactic
syntax "ring_eq_nf" " at " ident : tactic
syntax "ring_eq_nf" " at " "*" : tactic

elab_rules : tactic
  | `(tactic| ring_eq_nf) => ringEqNfGoal

elab_rules : tactic
  | `(tactic| ring_eq_nf at $h:ident) => ringEqNfAtHyp h.getId

elab_rules : tactic
  | `(tactic| ring_eq_nf at *) => do
    -- Collect hypothesis names that are equalities
    let mvarId ← getMainGoal
    let hypNames ← mvarId.withContext do
      let ctx ← getLCtx
      let mut names : Array Name := #[]
      for decl in ctx do
        if !decl.isImplementationDetail then
          let ty ← instantiateMVars decl.type
          if ty.eq?.isSome then
            names := names.push decl.userName
      return names
    -- Apply to each hypothesis (ignoring failures)
    for hName in hypNames do
      try ringEqNfAtHyp hName catch _ => pure ()
    -- Apply to the goal
    try ringEqNfGoal catch _ => pure ()

end Aeneas.RingEqNF
