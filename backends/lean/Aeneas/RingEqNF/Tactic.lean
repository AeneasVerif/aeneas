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
- `a + b = a + b`               →  `True`

## Implementation
`ring_eq_nf` is implemented as a `simproc` that triggers on equalities.
The tactic combines `ring_nf` (to normalize both sides) with the simproc
(to cancel common terms). Because it is a simproc, `simp` naturally handles
applying it to goals, hypotheses, and inside sub-expressions.
-/

open Lean Meta Elab Tactic

namespace Aeneas.RingEqNF

/-! ## Helper theorems -/

/-- If `a = a' + c` and `b = b' + c` (provable by `ring`),
    then `(a = b) ↔ (a' = b')`. -/
theorem eq_cancel_right_iff {α : Type*} [AddRightCancelMonoid α]
    {a b a' b' c : α}
    (hlhs : a = a' + c) (hrhs : b = b' + c) : (a = b) ↔ (a' = b') := by
  constructor
  · intro h; exact add_right_cancel (by rw [← hlhs, h, hrhs])
  · intro h; rw [hlhs, hrhs, h]

/-! ## Expression parsing utilities -/

private def exprToNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if let some n := e.nat? then some n
  else if let some n := e.rawNatLit? then some n
  else none

/-- Flatten a left-associated addition tree into a list of additive terms. -/
private partial def flattenAdd (e : Expr) : List Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs]) =>
    flattenAdd lhs ++ [rhs]
  | _ => [e]

/-- A monomial with its coefficient and original coefficient expression. -/
private structure CMonomial where
  coeff : Nat
  coeffExpr : Option Expr
  base : Option Expr
  deriving Inhabited

private def parseTerm (e : Expr) : CMonomial :=
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    match exprToNat? a with
    | some n => { coeff := n, coeffExpr := some a, base := some b }
    | none =>
      match exprToNat? b with
      | some n => { coeff := n, coeffExpr := some b, base := some a }
      | none => { coeff := 1, coeffExpr := none, base := some e }
  | _ =>
    match exprToNat? e with
    | some n => { coeff := n, coeffExpr := some e, base := none }
    | none => { coeff := 1, coeffExpr := none, base := some e }

private def parseNormExpr (e : Expr) : List CMonomial :=
  (flattenAdd e).map parseTerm

/-! ## Cancellation algorithm -/

private def sameBase (a b : CMonomial) : MetaM Bool :=
  match a.base, b.base with
  | none,   none   => return true
  | some x, some y => isDefEq x y
  | _,      _      => return false

private structure CancelResult where
  lhsRem : List CMonomial
  rhsRem : List CMonomial
  common : List CMonomial

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
          let cExpr := if lm.coeff ≤ rm.coeff then lm.coeffExpr else rm.coeffExpr
          common := common ++ [{ coeff := minC, coeffExpr := cExpr, base := lm.base }]
        if lm.coeff > minC then
          lhsRem := lhsRem ++ [{ coeff := lm.coeff - minC, coeffExpr := none, base := lm.base }]
        if rm.coeff > minC then
          newRhsRem := newRhsRem ++ [{ coeff := rm.coeff - minC, coeffExpr := none, base := rm.base }]
      else
        newRhsRem := newRhsRem ++ [rm]
    if found then
      rhsRem := newRhsRem
    else
      lhsRem := lhsRem ++ [lm]
  return { lhsRem, rhsRem, common }

/-! ## Expression construction -/

private def mkOfNat (ty : Expr) (n : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some ty, some (mkRawNatLit n), none]

private def getCoeffExpr (ty : Expr) (m : CMonomial) : MetaM Expr :=
  match m.coeffExpr with
  | some e => return e
  | none => mkOfNat ty m.coeff

private def buildMonomialExpr (ty : Expr) (m : CMonomial) : MetaM Expr := do
  match m.base with
  | none => getCoeffExpr ty m
  | some base =>
    if m.coeff == 1 then return base
    else
      let coeffExpr ← getCoeffExpr ty m
      mkAppM ``HMul.hMul #[base, coeffExpr]

private def buildSumExpr (ty : Expr) (terms : List CMonomial) : MetaM Expr := do
  match terms with
  | [] => mkOfNat ty 0
  | [t] => buildMonomialExpr ty t
  | t :: ts =>
    let first ← buildMonomialExpr ty t
    ts.foldlM (fun acc m => do
      let mExpr ← buildMonomialExpr ty m
      mkAppM ``HAdd.hAdd #[acc, mExpr]) first

/-! ## Simproc core -/

/-- Close a goal by `ring`. Returns the proof term or `none` on failure. -/
private def proveByRing (goalType : Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar (some goalType)
  let (goals, _) ← Elab.runTactic mvar.mvarId!
    (← `(tactic| ring)) {} {}
  if goals.isEmpty then
    return some (← instantiateMVars mvar)
  else
    return none

/-- Core cancellation logic, operating on a `ring_nf`-normalized equality expression.
    Returns a `Simp.Result` rewriting the equality to a simpler one. -/
private def cancelEq (e : Expr) : MetaM Simp.Result := do
  let some (ty, lhs, rhs) := e.eq?
    | return { expr := e }
  let lhsTerms := parseNormExpr lhs
  let rhsTerms := parseNormExpr rhs
  let result ← cancelCommon lhsTerms rhsTerms
  if result.common.isEmpty then return { expr := e }
  -- Build simplified expressions
  let newLhs ← buildSumExpr ty result.lhsRem
  let newRhs ← buildSumExpr ty result.rhsRem
  let common ← buildSumExpr ty result.common
  let newLhsPlusCommon ← mkAppM ``HAdd.hAdd #[newLhs, common]
  let newRhsPlusCommon ← mkAppM ``HAdd.hAdd #[newRhs, common]
  -- Prove lhs = newLhs + common and rhs = newRhs + common by ring
  let hlhsType ← mkEq lhs newLhsPlusCommon
  let hrhsType ← mkEq rhs newRhsPlusCommon
  let some hlhsProof ← proveByRing hlhsType | return { expr := e }
  let some hrhsProof ← proveByRing hrhsType | return { expr := e }
  -- Build: (lhs = rhs) = (newLhs = newRhs) via propext + eq_cancel_right_iff
  let newEq ← mkEq newLhs newRhs
  let iffProof ← mkAppM ``eq_cancel_right_iff #[hlhsProof, hrhsProof]
  let proof ← mkAppM ``propext #[iffProof]
  return { expr := newEq, proof? := some proof }

/-! ## Simproc definition -/

/-- Simproc that cancels common additive terms in equalities over `Nat`.
    Not registered in the default simp set — use `ring_eq_nf` or
    `simp only [ringEqNfNat]` to invoke. -/
simproc_decl ringEqNfNat (@Eq Nat _ _) := fun e => do
  let r ← cancelEq e
  if r.expr == e then return .continue
  return .visit r

/-- Simproc that cancels common additive terms in equalities over `Int`.
    Not registered in the default simp set — use `ring_eq_nf` or
    `simp only [ringEqNfInt]` to invoke. -/
simproc_decl ringEqNfInt (@Eq Int _ _) := fun e => do
  let r ← cancelEq e
  if r.expr == e then return .continue
  return .visit r

/-! ## Tactic -/

syntax "ring_eq_nf" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ring_eq_nf $[$loc]?) =>
    `(tactic| (ring_nf $[$loc]?; try simp (config := {failIfUnchanged := false}) only [ringEqNfNat, ringEqNfInt] $[$loc]?))

end Aeneas.RingEqNF
