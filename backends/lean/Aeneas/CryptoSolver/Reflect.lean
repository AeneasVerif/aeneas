import Lean
import Aeneas.CryptoSolver.Expr
import Aeneas.CryptoSolver.Interval
import Aeneas.CryptoSolver.IntervalAnalysis

/-!
# Reflection: Lean Expr → AExpr and bounds collection

Converts Lean kernel expressions into our internal `AExpr` representation,
and harvests variable bounds from the local context.
-/

namespace Aeneas.CryptoSolver

open Lean Meta Elab

/-- Domain tag: whether an expression lives in Nat or Int -/
inductive Domain where
  | nat | int
  deriving Repr, BEq, Inhabited

/-- Try to extract a non-negative integer literal from a Lean expression.
    Handles `OfNat.ofNat`, `Nat.succ`, raw nat literals, etc. -/
partial def extractNonnegLit (e : Expr) : MetaM (Option Nat) := do
  -- Try raw nat literal
  if let some n := e.rawNatLit? then return some n
  -- Try OfNat.ofNat _ n _
  let e ← whnfD e
  if let some n := e.rawNatLit? then return some n
  match_expr e with
  | OfNat.ofNat _ n _ =>
    if let some n := n.rawNatLit? then return some n else return none
  | _ => return none

/-- Try to extract an integer literal (possibly negative) from a Lean expression. -/
partial def extractIntLit (e : Expr) : MetaM (Option Int) := do
  -- Try as non-negative first
  if let some n ← extractNonnegLit e then return some (Int.ofNat n)
  let e ← whnfD e
  -- Try Neg.neg (OfNat.ofNat n)
  match_expr e with
  | Neg.neg _ _ inner =>
    if let some n ← extractNonnegLit inner then return some (Int.negSucc (n - 1))
    else return none
  | Int.negSucc n =>
    if let some n := n.rawNatLit? then return some (Int.negSucc n) else return none
  | _ => return none

/-- Determine the domain of an expression's type -/
def getDomain (e : Expr) : MetaM Domain := do
  let ty ← inferType e
  let ty ← whnfD ty
  if ty.isConstOf ``Nat then return .nat
  else if ty.isConstOf ``Int then return .int
  else return .int -- default

/-- Convert a Lean expression to our internal `AExpr`. -/
partial def toAExpr (e : Expr) : MetaM AExpr := do
  -- Try literal first
  if let some n ← extractIntLit e then
    return .lit n
  -- Check for free variable
  if e.isFVar then
    return .var e.fvarId!
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Binary operations: fn has 6 args (α, β, γ, inst, a, b)
  if args.size == 6 then
    if fn.isConstOf ``HAdd.hAdd then
      return .add (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HSub.hSub then
      return .sub (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HMul.hMul then
      return .mul (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HDiv.hDiv then
      return .div (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HMod.hMod then
      return .mod (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HPow.hPow then
      -- Only handle literal exponents
      if let some n ← extractNonnegLit args[5]! then
        return .pow (← toAExpr args[4]!) n
    if fn.isConstOf ``HShiftLeft.hShiftLeft then
      if let some n ← extractNonnegLit args[5]! then
        return .shl (← toAExpr args[4]!) n
    if fn.isConstOf ``HShiftRight.hShiftRight then
      if let some n ← extractNonnegLit args[5]! then
        return .shr (← toAExpr args[4]!) n
    if fn.isConstOf ``HAnd.hAnd then
      return .band (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HOr.hOr then
      return .bor (← toAExpr args[4]!) (← toAExpr args[5]!)
    if fn.isConstOf ``HXor.hXor then
      return .bxor (← toAExpr args[4]!) (← toAExpr args[5]!)
  -- Unary operations: Neg.neg α inst a
  if args.size == 3 && fn.isConstOf ``Neg.neg then
    return .neg (← toAExpr args[2]!)
  -- Int.ofNat / Nat → Int coercion
  if args.size == 1 then
    if fn.isConstOf ``Int.ofNat then
      return ← toAExpr args[0]!
  -- OfNat.ofNat α n inst  (3 args)
  if args.size == 3 && fn.isConstOf ``OfNat.ofNat then
    if let some n := args[1]!.rawNatLit? then
      return .lit (Int.ofNat n)
  -- Try whnf reduction for definitions
  let e' ← whnf e
  if e' != e then
    return ← toAExpr e'
  -- Fallback: opaque expression
  return .unknown e

/-- Extract a comparison from a proposition expression.
    Returns (lhs, rhs, isStrict) where isStrict means `<` vs `≤`. -/
def parseComparison (prop : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let fn := prop.getAppFn
  let args := prop.getAppArgs
  -- LT.lt α inst a b  (4 args)
  if args.size == 4 && fn.isConstOf ``LT.lt then
    return some (args[2]!, args[3]!, true)
  -- LE.le α inst a b  (4 args)
  if args.size == 4 && fn.isConstOf ``LE.le then
    return some (args[2]!, args[3]!, false)
  -- Nat.lt a b  (2 args) — sometimes appears after whnf
  if args.size == 2 && fn.isConstOf ``Nat.lt then
    return some (args[0]!, args[1]!, true)
  -- Nat.ble a b etc. — skip for now
  return none

/-- Information about a bound extracted from the context -/
structure BoundInfo where
  fvarId : FVarId       -- The hypothesis providing this bound
  target : FVarId       -- The variable being bounded
  isUpper : Bool        -- true for `x < n` or `x ≤ n`, false for `n ≤ x` or `n < x`
  isStrict : Bool       -- true for `<`, false for `≤`
  bound : Int           -- The numeric bound
  deriving Repr

/-- Scan a single hypothesis for bounds information.
    Handles: `x < n`, `x ≤ n`, `n ≤ x`, `n < x` where `n` is a literal
    and `x` is a free variable. -/
def extractBound (hyp : LocalDecl) : MetaM (List BoundInfo) := do
  let ty ← instantiateMVars hyp.type
  -- Try as a comparison
  if let some (lhs, rhs, isStrict) ← parseComparison ty then
    let mut bounds := []
    -- Case 1: x < n or x ≤ n (variable on left, literal on right)
    if lhs.isFVar then
      if let some n ← extractIntLit rhs then
        bounds := bounds ++ [{
          fvarId := hyp.fvarId, target := lhs.fvarId!,
          isUpper := true, isStrict, bound := n
        }]
    -- Case 2: n < x or n ≤ x (literal on left, variable on right)
    if rhs.isFVar then
      if let some n ← extractIntLit lhs then
        bounds := bounds ++ [{
          fvarId := hyp.fvarId, target := rhs.fvarId!,
          isUpper := false, isStrict, bound := n
        }]
    return bounds
  -- Try conjunction: P ∧ Q
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if args.size == 2 && fn.isConstOf ``And then
    -- Recursively extract from both sides
    -- We'd need to project, which is complex; skip for now
    return []
  return []

/-- Collect all variable bounds from the local context.
    Returns an `IntervalEnv` mapping each bounded variable to its interval. -/
def collectBounds : MetaM IntervalEnv := do
  let ctx ← getLCtx
  let mut env : IntervalEnv := IntervalEnv.empty
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let bounds ← extractBound decl
    for b in bounds do
      let prev := env.getD b.target Interval.top
      let newBound : Interval :=
        if b.isUpper then
          let hi := if b.isStrict then b.bound - 1 else b.bound
          ⟨prev.lo, min prev.hi hi⟩
        else
          let lo := if b.isStrict then b.bound + 1 else b.bound
          ⟨max prev.lo lo, prev.hi⟩
      env := env.insert b.target newBound
  -- Also extract implicit non-negativity for Nat-typed variables
  for decl in ctx do
    if decl.isImplementationDetail then continue
    if !decl.type.isFVar && !decl.type.isApp then continue
    let ty ← inferType (mkFVar decl.fvarId)
    let ty ← whnfD ty
    if ty.isConstOf ``Nat then
      let prev := env.getD decl.fvarId Interval.top
      if prev.lo < 0 then
        env := env.insert decl.fvarId ⟨0, prev.hi⟩
  return env

end Aeneas.CryptoSolver
