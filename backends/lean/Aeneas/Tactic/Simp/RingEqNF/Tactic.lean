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

`ring_eq_nf` works in two phases, composed as a single tactic:

1. **`ring_nf`** — Mathlib's ring-normal-form tactic normalises both sides of every
   equality in the target (or hypotheses). After this step, sums are left-associated
   and each summand has the form `n * base` with `n` a numeric literal and `base` a
   product of atoms. If the two sides are already equal after normalisation, `ring_nf`
   closes the goal outright and the second phase is skipped.

2. **`simp only [ringEqNfNat, ringEqNfInt]`** — invokes two custom `simproc`s (one
   for `Nat`, one for `Int`) that perform common-term cancellation:
   a. Parse each side of the equality into a list of `CMonomial`s (coefficient + base).
   b. Pair up monomials with the same base and subtract the minimum coefficient.
   c. Build simplified LHS' and RHS' from the remainders, and a common sum `C`.
   d. Use `ring` to prove `LHS = LHS' + C` and `RHS = RHS' + C`.
   e. Apply `eq_cancel_right_iff` (additive right-cancellation) + `propext` to
      rewrite `(LHS = RHS)` to `(LHS' = RHS')`.

   Because the cancellation is a `simproc`, `simp` automatically applies it inside
   goals, hypotheses, and nested sub-expressions.
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

/-- Flatten a left-associated addition tree into a list of additive terms
  (e.g., `((x₀ + x₁) + ... xₙ)` to `[x₀, x₁, ..., xₙ]` -/
private partial def flattenAdd (e : Expr) : List Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs]) =>
    flattenAdd lhs ++ [rhs]
  | _ => [e]

/-- A parsed monomial of the form `coeff * base` extracted from a `ring_nf`-normalized
    additive term.

    - `coeff` — the natural-number coefficient.
    - `coeffExpr` — the original `Expr` for the coefficient when it was present in the
      input expression. `none` when the coefficient is implicit (the term is just `base`
      with coefficient 1) or was computed during cancellation rather than read from the
      input.
    - `base` — the non-coefficient factor, i.e.\ the "variable part". `none` for pure
      numeric literals that have no variable part.

    Examples (showing how `parseTerm` produces `CMonomial`s):
    - `3 * x`  →  `{ coeff := 3, coeffExpr := some ‹3›, base := some ‹x› }`
    - `x * 5`  →  `{ coeff := 5, coeffExpr := some ‹5›, base := some ‹x› }`
    - `x * y`  →  `{ coeff := 1, coeffExpr := none,     base := some ‹x * y› }`
    - `7`      →  `{ coeff := 7, coeffExpr := some ‹7›, base := none }`
    - `x`      →  `{ coeff := 1, coeffExpr := none,     base := some ‹x› }` -/
private structure CMonomial where
  coeff : Nat
  coeffExpr : Option Expr
  base : Option Expr
  deriving Inhabited

/-- Parse a single additive term (as produced by `ring_nf`) into a `CMonomial`.

    `ring_nf` normalises products so that the numeric coefficient is on the left
    (`n * base`). We also handle the `base * n` case for robustness. When no
    numeric factor is found, the coefficient defaults to 1. -/
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

/-- Flatten a `ring_nf`-normalized expression (a left-associated sum) and parse each
    summand into a `CMonomial`. -/
private def parseNormExpr (e : Expr) : List CMonomial :=
  (flattenAdd e).map parseTerm

/-! ## Cancellation algorithm -/

/-- Check whether two `CMonomial`s have the same base expression. Uses structural
    equality (`==`), which is safe here because both expressions come from the same
    `ring_nf` pass and are therefore already in a canonical form. -/
private def sameBase (a b : CMonomial) : MetaM Bool :=
  match a.base, b.base with
  | none,   none   => return true
  | some x, some y => return x == y
  | _,      _      => return false

private structure CancelResult where
  lhsRem : List CMonomial
  rhsRem : List CMonomial
  common : List CMonomial

/-- Cancel common additive monomials between two parsed sides of an equality.

    Given `lhs = [3x, 2y]` and `rhs = [x, 3y]`, finds the common part `[x, 2y]`
    (taking the minimum coefficient for each matching base) and returns the remainders
    `lhsRem = [2x]`, `rhsRem = [y]`, `common = [x, 2y]`.

    The algorithm iterates over each LHS monomial and searches for a matching base in
    the (shrinking) RHS remainder. When a match is found, the minimum coefficient is
    moved to `common` and any excess stays in the respective remainder. -/
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
        -- Move the shared portion to `common`
        if minC > 0 then
          -- Reuse the original coefficient expr from whichever side had the smaller
          -- (or equal) coefficient, so the proof term stays close to the input.
          let cExpr := if lm.coeff ≤ rm.coeff then lm.coeffExpr else rm.coeffExpr
          common := common ++ [{ coeff := minC, coeffExpr := cExpr, base := lm.base }]
        -- Keep the excess on the LHS
        if lm.coeff > minC then
          lhsRem := lhsRem ++ [{ coeff := lm.coeff - minC, coeffExpr := none, base := lm.base }]
        -- Keep the excess on the RHS
        if rm.coeff > minC then
          newRhsRem := newRhsRem ++ [{ coeff := rm.coeff - minC, coeffExpr := none, base := rm.base }]
      else
        newRhsRem := newRhsRem ++ [rm]
    if found then
      rhsRem := newRhsRem
    else
      -- No matching base on the RHS — the entire LHS monomial is a remainder
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

/-- Close a goal by `ring`. Returns the proof term or `none` on failure.

    Note: Mathlib's `ring` core lives in `AtomM` (not plain `MetaM`), so calling it
    directly would require `AtomM.run` + `Mathlib.Tactic.Ring.proveEq`. We go through
    `runTactic` for simplicity; the cost is negligible because `ring` is fast on the
    small rearrangement goals produced by `cancelEq`. -/
private def proveByRing (goalType : Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar (some goalType)
  let (goals, _) ← Elab.runTactic mvar.mvarId!
    (← `(tactic| ring)) {} {} -- `ring` (not `ring_nf`): we need to *prove* the equality, not just normalize it
  if goals.isEmpty then
    return some (← instantiateMVars mvar)
  else
    return none

/-- Core cancellation logic, operating on a `ring_nf`-normalized equality expression.
    Returns a `Simp.Result` rewriting the equality to a simpler one. -/
private def cancelEq (e : Expr) : MetaM Simp.Result := do
  let some (ty, lhs, rhs) := e.eq?
    | return { expr := e }
  -- We assume the lhs and rhs have already been normalized
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
    `(tactic| ((try ring_nf $[$loc]?); try simp (config := {failIfUnchanged := false}) only [ringEqNfNat, ringEqNfInt] $[$loc]?))

end Aeneas.RingEqNF
