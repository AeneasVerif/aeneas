import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic
import Aeneas.CryptoSolver.Init

/-! # General Modular Arithmetic Simplification Engine

This module provides tactics for reasoning about modular arithmetic:
- Mod-congruence propagation: from `a % n = b % n`, derive `(a - b) % n = 0`
- Mod-zero detection: detect when `expr ≡ 0 (mod n)` via products, sums, etc.
- Divisibility proofs: prove `n ∣ expr` or `expr % n = 0`
- Exact division: when `n ∣ a`, derive `a / n * n = a`
- Coprime inverse: for `x % n = (a * y⁻¹.val) % n` with gcd(y,n)=1

These rules are general and apply to any modular arithmetic goals
(Montgomery reduction, Barrett reduction, NTT operations, etc.).
-/

namespace Aeneas.CryptoSolver.ModArith

/-! ## General modular arithmetic helper lemmas -/

/-- Lifting `(x % n) * y` to `x * y` under mod n. -/
theorem Int.emod_mul_emod (x y n : Int) : ((x % n) * y) % n = (x * y) % n := by
  rw [Int.mul_emod (x % n) y, Int.emod_emod_of_dvd _ (dvd_refl n), ← Int.mul_emod]

/-- If `(1 + m * q) % R = 0`, then `R ∣ (a + (a * m % R) * q)` for any `a`.
    This is a general modular arithmetic fact used in Montgomery-like reductions,
    but applies to any divisibility proof from congruence hypotheses. -/
theorem dvd_add_mul_emod_mul {a m q R : Int}
    (h : (1 + m * q) % R = 0) : R ∣ (a + (a * m % R) * q) := by
  rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_mul_emod, ← Int.add_emod]
  have : (a + a * m * q) % R = (a * (1 + m * q)) % R := by congr 1; ring
  rw [this, Int.mul_emod, h, mul_zero, Int.zero_emod]

/-- From `(m * q) % R = (-1) % R`, derive `(1 + m * q) % R = 0`. -/
theorem one_add_mul_emod_eq_zero {m q R : Int}
    (h : (m * q) % R = (-1) % R) : (1 + m * q) % R = 0 := by
  have : (m * q - (-1)) % R = 0 := by
    rw [Int.sub_emod, h, sub_self, Int.zero_emod]
  rwa [show m * q - -1 = 1 + m * q from by ring] at this

open Lean Meta Elab Tactic

/-- Run a tactic sequence (via evalTactic) and return true only if all goals close. -/
private def tryClose (act : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  try
    act
    if (← getGoals).isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Try to prove a divisibility goal `n ∣ expr` using general modular arithmetic.

    Strategy:
    1. Convert to `expr % n = 0` via `Int.dvd_iff_emod_eq_zero`
    2. Rewrite `(x % n) * y` via `Int.mul_emod` + `Int.emod_emod_of_dvd` (mod-lifting)
    3. Factor expressions using `ring` rewrites
    4. Use `Int.mul_emod` to reduce `a * b % n` when `b % n = 0`
    5. Close with congruence hypotheses from context -/
private def tryDivisibilityGoal : TacticM Bool := do
  -- Strategy 1: Use dvd_add_mul_emod_mul + one_add_mul_emod_eq_zero
  -- This handles R ∣ (a + (a*m%R)*q) from Montgomery-like reductions
  if ← tryClose (do
    evalTactic (← `(tactic|
      apply dvd_add_mul_emod_mul
      apply one_add_mul_emod_eq_zero
      exact ‹_ % _ = (-1) % _›))
  ) then return true
  -- Strategy 2: Direct dvd_iff + ring_nf/omega
  if ← tryClose (do
    evalTactic (← `(tactic| rw [Int.dvd_iff_emod_eq_zero]))
    evalTactic (← `(tactic| ring_nf))
    evalTactic (← `(tactic| omega))
  ) then return true
  -- Strategy 3: Direct omega
  if ← tryClose (evalTactic (← `(tactic| omega))) then return true
  return false

/-- Try to prove a mod-equality goal `a % n = b % n` via ZMod reasoning.

    For goals like `t % q = (a * R⁻¹.val) % q` with coprimality:
    1. Introduce NeZero q
    2. Prove divisibility: R ∣ (numerator)
    3. Get exact division via Int.ediv_mul_cancel
    4. Lift to ZMod, use coprime inverse via ZMod.coe_mul_inv_eq_one
    5. Cast back -/
private def tryModEqualityViaZMod : TacticM Bool := do
  let goal ← getMainGoal
  let tgt ← goal.getType >>= instantiateMVars
  let tgt := tgt.consumeMData
  -- Check: goal is `_ = _`
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  if args.size < 3 then return false
  if !fn.isConstOf ``Eq then return false
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!.consumeMData
  -- Both sides should be HMod.hMod
  if !lhs.isAppOf ``HMod.hMod || !rhs.isAppOf ``HMod.hMod then return false
  -- Check if RHS involves ZMod inverse (.val)
  let hasZModInv := rhs.find? (fun e =>
    let e := e.consumeMData
    e.isAppOf ``ZMod.val || e.isAppOf ``Inv.inv) |>.isSome
  if !hasZModInv then return false
  trace[CryptoSolver] "tryModEqualityViaZMod: detected ZMod inverse in goal"
  -- Extract key expressions from the goal:
  -- LHS is (numerator / divisor) % modulus
  let lhsModArgs := lhs.getAppArgs
  if lhsModArgs.size < 6 then return false
  let modulus := lhsModArgs[5]!     -- the modulus (e.g., ↑q)
  let divExpr := lhsModArgs[4]!.consumeMData  -- numerator / divisor
  if !divExpr.isAppOf ``HDiv.hDiv then return false
  let divArgs := divExpr.getAppArgs
  if divArgs.size < 6 then return false
  let numerator := divArgs[4]!  -- the numerator before division
  let divisor := divArgs[5]!    -- the divisor (e.g., ↑R)
  -- Find the congruence hypothesis: _ % divisor = (-1) % divisor
  let congHyp? ← goal.withContext do
    let ctx ← getLCtx
    for decl in ctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      let ty := ty.consumeMData
      -- Check if ty is _ % _ = (-1) % _
      if !ty.isAppOf ``Eq then continue
      let eqArgs := ty.getAppArgs
      if eqArgs.size < 3 then continue
      let eqLhs := eqArgs[1]!.consumeMData
      let eqRhs := eqArgs[2]!.consumeMData
      if !eqLhs.isAppOf ``HMod.hMod || !eqRhs.isAppOf ``HMod.hMod then continue
      -- Check RHS is (-1) % _
      let rhsModArgs := eqRhs.getAppArgs
      if rhsModArgs.size < 6 then continue
      let negOneExpr := rhsModArgs[4]!.consumeMData
      -- Check if it's -1 via isDefEq
      let negOne ← withMainContext do mkAppM ``Neg.neg #[toExpr (1 : Int)]
      let isNegOne ← withMainContext do isDefEq negOneExpr negOne
      if !isNegOne then continue
      return some decl
    return none
  let some congHyp := congHyp? | do
    trace[CryptoSolver] "tryModEqualityViaZMod: no congruence hypothesis found"
    return false
  trace[CryptoSolver] "tryModEqualityViaZMod: found congruence hyp {congHyp.userName}"
  -- Helper: extract Nat behind Int cast (↑q → q)
  let extractNatBehindCast (e : Expr) (label : String) : MetaM Expr := do
    let e := e.consumeMData
    if e.isAppOf ``Nat.cast then return e.appArg!
    if e.isAppOf ``Int.ofNat then return e.appArg!
    throwError "tryModEqualityViaZMod: {label} is not a Nat cast: {e}"
  let natModulus ← withMainContext do extractNatBehindCast modulus "modulus"
  let natDivisor ← withMainContext do extractNatBehindCast divisor "divisor"
  -- Now build the proof using interpolated syntax
  let numStx ← withMainContext do PrettyPrinter.delab numerator
  let divStx ← withMainContext do PrettyPrinter.delab divisor
  let natModStx ← withMainContext do PrettyPrinter.delab natModulus
  let natDivStx ← withMainContext do PrettyPrinter.delab natDivisor
  let congStx := mkIdent congHyp.userName
  if ← tryClose (do
    evalTactic (← `(tactic| haveI : NeZero $natModStx := ⟨by omega⟩))
    evalTactic (← `(tactic|
      have _hdvd : $divStx ∣ $numStx := by
        apply dvd_add_mul_emod_mul
        apply one_add_mul_emod_eq_zero
        exact $congStx))
    evalTactic (← `(tactic| have hexact := Int.ediv_mul_cancel _hdvd))
    evalTactic (← `(tactic| rw [← ZMod.intCast_eq_intCast_iff']))
    evalTactic (← `(tactic|
      have h := congr_arg (fun (x : Int) => (x : ZMod $natModStx)) hexact))
    evalTactic (← `(tactic|
      simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_ofNat] at h))
    evalTactic (← `(tactic|
      simp only [ZMod.natCast_self, mul_zero, add_zero] at h))
    -- h : ↑t * ↑R = ↑a (in ZMod q)
    evalTactic (← `(tactic| have hRinv := ZMod.coe_mul_inv_eq_one _ ‹Nat.Coprime _ _›))
    -- Derive ↑t = ↑a * (↑R)⁻¹ by multiplying both sides by (↑R)⁻¹
    evalTactic (← `(tactic|
      have key := congr_arg (fun x => x * (↑$natDivStx : ZMod $natModStx)⁻¹) h))
    evalTactic (← `(tactic| simp only [mul_assoc] at key))
    evalTactic (← `(tactic| rw [hRinv, mul_one] at key))
    evalTactic (← `(tactic| simp only [key]))
    evalTactic (← `(tactic| push_cast))
    evalTactic (← `(tactic| congr 1))
    evalTactic (← `(tactic| exact (ZMod.natCast_zmod_val _).symm))
  ) then return true
  return false

/-- Try general modular arithmetic strategies.
    Dispatches based on goal shape:
    - `n ∣ expr` → tryDivisibilityGoal
    - `expr % n = 0` → convert to divisibility
    - `a % n = b % n` with ZMod → tryModEqualityViaZMod
    - Other mod equalities → direct simp/ring/omega -/
def tryModArith : TacticM Bool := do
  let goal ← getMainGoal
  let tgt ← goal.getType >>= instantiateMVars
  let tgt := tgt.consumeMData
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  -- Check for dvd goal: n ∣ expr
  if fn.isConstOf ``Dvd.dvd then
    return ← tryDivisibilityGoal
  -- Check for equality goal: @Eq α lhs rhs has 3 args
  if fn.isConstOf ``Eq && args.size >= 3 then
    let lhs := args[1]!.consumeMData
    let rhs := args[2]!.consumeMData
    -- Check for `a % n = b % n`
    if lhs.isAppOf ``HMod.hMod && rhs.isAppOf ``HMod.hMod then
      -- Try ZMod approach first (for coprime inverse goals)
      if ← tryModEqualityViaZMod then return true
      -- Fallback: omega/ring_nf for simpler mod equalities
      if ← tryClose (evalTactic (← `(tactic| omega))) then return true
      if ← tryClose (evalTactic (← `(tactic| ring_nf; omega))) then return true
  return false

end Aeneas.CryptoSolver.ModArith
