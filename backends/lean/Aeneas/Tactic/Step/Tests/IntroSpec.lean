module
import Aeneas.Tactic.Step
public meta import Lean
public meta import Aeneas.Tactic.Step
import Aeneas.Tactic.Solver.ScalarTac

/-!
# Tests for `intro_spec`, the `intro_tactic` of `spec` and `dspec`

Proofs written against earlier versions of `step` (e.g. the VCR proofs) rely on the order
and names of the introduced variables, and on the shape of the remaining goal. Many tests
below are reduced from such proofs.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.IntroSpec

/-! ## Normalization of the premise -/

/- `intro_spec` splits the conjunction of the premise: it comes back with one binder per
   conjunct. -/
example (P Q R : Prop) (hR : R) : P ∧ Q → R := by
  intro_spec
  guard_target = P → Q → R
  intro _ _
  exact hR

example (n : Nat) (P Q : Nat → Prop) (R : Prop) (hR : R) :
    (∃ x, x = n ∧ P x ∧ Q x) → R := by
  intro_spec
  guard_target = P n → Q n → R
  intro _ _
  exact hR

example (b : Bool) (n : Nat) (P Q : Nat → Prop) (R : Prop) (hR : R) :
    (match b with
     | true => ∃ x, n = x ∧ P x ∧ Q x
     | false => ∃ x, P x ∧ x = n) → R := by
  intro_spec
  guard_target = (match b with | true => P n ∧ Q n | false => P n) → R
  intro _
  exact hR

example (n : Nat) (P Q R : Prop) (hR : R) :
    ((n = n → True → Unit → P ∧ Q) ∧ (∃ x, x = n ∧ True)) → R := by
  intro_spec
  guard_target = P → Q → R
  intro _ _
  exact hR

example (P Q : Prop) (R : P ∧ Q → Prop) (hR : ∀ h, R h) : ∀ h, R h := by
  intro_spec
  guard_target = ∀ hp hq, R ⟨hp, hq⟩
  intro hp hq
  exact hR ⟨hp, hq⟩

example (Q R : Prop) (hR : R) : (Q ∧ ∃ f : Unit → Nat, f () = 0) → R := by
  intro_spec
  guard_target = Q → ∀ f : Unit → Nat, f () = 0 → R
  intro _ _ _
  exact hR

/- Keep let-bound postconditions bundled. -/
example (compute : Nat → Nat × Nat) (P : Nat → Nat → Nat → Prop) (R : Prop) (hR : R) :
    ∀ output : Nat × Nat,
      Aeneas.Std.WP.uncurry' (fun a b =>
        let (x, y) := compute a
        P a b x ∧ P a b y) output → R := by
  intro_spec
  guard_target = ∀ output : Nat × Nat,
    (let (x, y) := compute output.1
     P output.1 output.2 x ∧ P output.1 output.2 y) → R
  intro _ _
  exact hR

/- The example of `normalizePost`, which goes through its three steps. -/
example (P : Nat → Nat → Prop) (Q : Nat → Prop) (R : Prop) (hR : R) :
    ∀ x : Nat × Nat,
      Aeneas.Std.WP.uncurry' (fun a b => ∃ y z, z = a + 1 ∧ P y z ∧ Q b) x → R := by
  intro_spec
  guard_target = ∀ x : Nat × Nat, ∀ y, P y (x.1 + 1) → Q x.2 → R
  intro _ _ _ _
  exact hR

open Lean Meta Elab Tactic in
elab "run_intro_pending " n:ident : tactic => withMainContext do
  let n := mkFVar (← getFVarId n)
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let goal ← getMainGoal
  let worker ← mkFreshExprSyntheticOpaqueMVar ((← goal.getType).replaceFVar n pending)
  setGoals [worker.mvarId!]
  Step.runIntroTactic ``Aeneas.Std.WP.introTactic
  let target ← instantiateMVars (← (← getMainGoal).getType)
  if (target.find? (· == pending)).isNone then
    throwError "Output normalization did not preserve a pending obligation"
  pending.mvarId!.assign n
  goal.assign worker

example (n : Nat) (P : Nat → Prop) (R : Prop) (hR : R) :
    ∀ value, value = n ∧ P value → R := by
  run_intro_pending n
  intro value heq hP
  guard_hyp heq : value = n
  guard_hyp hP : P value
  exact hR

elab "run_intro_split_compact" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  Step.runIntroTactic ``Aeneas.Std.WP.introTactic
  let proof ← Lean.instantiateMVars (Lean.mkMVar goal)
  if (proof.find? fun e =>
      e.isConstOf ``And.casesOn || e.isConstOf ``And.rec ||
      e.isConstOf ``Exists.casesOn || e.isConstOf ``Exists.rec).isSome then
    throwError "introTactic exposed an elimination recursor around its continuation"

example (P : Nat → Prop) (Q R : Prop) (hR : R) :
    (∃ n, P n ∧ (True → Unit → Q)) → R := by
  run_intro_split_compact
  guard_target = ∀ n, P n → Q → R
  intro _ _ _
  exact hR

/-! ## Postconditions introduced by `step` -/

def dup (n : Nat) : Result (Nat × Nat) := ok (n, n)

def id' (n : Nat) : Result Nat := ok n

@[local step]
theorem id'_spec (n : Nat) : id' n ⦃ r => r = n ⦄ := by simp [id']

def bundled (compute : Nat → Nat × Nat) (n : Nat) : Result (Nat × Nat) :=
  ok (compute n)

@[local step]
theorem bundled_spec (compute : Nat → Nat × Nat) (n : Nat) :
    bundled compute n ⦃ a b =>
      let (x, y) := compute n
      a = x ∧ b = y ⦄ := by
  simp [bundled, Aeneas.Std.WP.uncurry']

example (compute : Nat → Nat × Nat) (n : Nat) :
    (do let (a, b) ← bundled compute n; ok (a, b)) ⦃ out => out = compute n ⦄ := by
  step as ⟨a, b, h⟩
  guard_hyp h : a = (compute n).1 ∧ b = (compute n).2
  obtain ⟨ha, hb⟩ := h
  exact Prod.ext ha hb

/- Facts which become trivial after instantiation are kept. -/
def conditional (bound : U32) : Result Bool := ok (bound.val = bound.val)

@[local step]
theorem conditional_spec (bound : U32) :
    conditional bound ⦃ result => bound.val = 0 → result = true ⦄ := by
  simp [conditional]

example : conditional 0#u32 ⦃ result => result = true ⦄ := by
  step as ⟨result, h⟩
  guard_hyp h : True → result = true
  exact h trivial

/-! ### Leading existentials of a postcondition come after the outputs -/

theorem dup_witness_spec (n : Nat) :
    dup n ⦃ a b => ∃ (w : Bool) (k : Nat), a = n + k ∧ b = n ∧ w = (k == 0) ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a, b)) ⦃ _ b => b = n ⦄ := by
  step with dup_witness_spec as ⟨a, b, w, k, ha, hb, hw⟩
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp w : Bool
  guard_hyp k : Nat
  guard_hyp ha : a = n + k
  guard_hyp hb : b = n
  guard_hyp hw : w = (k == 0)
  exact hb

example (f : Result (Nat × Nat × Nat))
    (h : f ⦃ p =>
      ∃ witness : Bool × Nat, p.1 = witness.1.toNat ∧ p.2.1 = witness.2 ∧ p.2.1 = p.2.2 ⦄) :
    (do let (a, b, c) ← f; ok (a, b, c)) ⦃ _ b c => b = c ⦄ := by
  let* ⟨a, b, c, witness, ha, hb, hbc⟩ ← h
  guard_hyp witness : Bool × Nat
  guard_hyp ha : a = witness.1.toNat
  guard_hyp hb : b = witness.2
  exact hbc

example (f : Result Unit) (h : f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄) :
    f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄ := by
  let* ⟨witness, hw⟩ ← h
  guard_hyp witness : Nat
  guard_hyp hw : witness > 0
  exact ⟨witness, hw⟩

example (f : Result (Nat × Nat))
    (h : f ⦃ p => ∃ witness : Bool, p.1 = witness.toNat ∧ p.1 = p.2 ⦄div) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄div := by
  let* ⟨a, b, witness, hw, hab⟩ ← h
  guard_hyp witness : Bool
  guard_hyp hw : a = witness.toNat
  simpa using hab

example (f : Result (List Nat)) (n : Nat)
    (h : f ⦃ result => ∃ hlen : result.length = n, n = result.length ∧ hlen = hlen ⦄) :
    f ⦃ result => result.length = n ⦄ := by
  step with h as ⟨result, hlen, hlen'⟩
  guard_hyp result : List Nat
  guard_hyp hlen : result.length = n
  guard_hyp hlen' : n = result.length
  exact hlen

/-! ### Facts about existential witnesses are named after the binder

The facts about the witness of `∃ s, …` are named `s_post`, `s_post1`, ... -/

theorem dup_nested_spec (n : Nat) :
    dup n ⦃ a b => a = n ∧ ∃ s, s ≥ a ∧ s = a + b ∧ b = n ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a + b)) ⦃ r => r = n + n ⦄ := by
  step with dup_nested_spec
  rename_i s
  guard_hyp s_post : s ≥ a
  guard_hyp s_post1 : s = a + b
  guard_hyp b_post : b = n
  simp [a_post, b_post]

example (f : Result Bool) (n : Nat) (P : Nat → Prop)
    (hf : f ⦃ b =>
      match b with
      | true => n = n ∧ ∃ j, j < n ∧ ¬ P j
      | false => True ⦄) :
    f ⦃ b => b = false ∨ ∃ j, j < n ∧ ¬ P j ⦄ := by
  step with hf as ⟨b, h⟩
  cases b
  · exact Or.inl rfl
  · obtain ⟨j, hj, hnot⟩ := h
    exact Or.inr ⟨j, hj, hnot⟩

example (f : Result Bool) (P : Prop)
    (hf : f ⦃ b => b = true ↔ True ∧ P ⦄) :
    f ⦃ b => b = true ↔ P ⦄ := by
  step with hf as ⟨b, h⟩
  guard_hyp h : b = true ↔ P
  exact h

/-! ### Reducible postconditions are split -/

abbrev dupPost (n a b : Nat) : Prop :=
  ∃ (_h : a = n), b = n ∧ a = b

theorem dup_abbrev_spec (n : Nat) : dup n ⦃ a b => dupPost n a b ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a, b)) ⦃ a b => dupPost n a b ⦄ := by
  step with dup_abbrev_spec as ⟨a, b, h0, h1, h2⟩
  guard_hyp h0 : a = n
  guard_hyp h1 : b = n
  guard_hyp h2 : a = b
  exact ⟨h0, h1, h2⟩

/-! ### The facts and the postcondition of the goal are normalized

Conjunctive and existential premises are curried, and `True` premises are dropped. -/

theorem id'_curried_spec (n : Nat) : id' n ⦃ r => ∀ j, (_h : j ≤ r ∧ r ≤ j) → j = n ⦄ := by
  simp only [id', WP.spec_ok]
  intro j h
  agrind

example (n : Nat) : (do let r ← id' n; ok r) ⦃ r => r = n ⦄ := by
  step with id'_curried_spec as ⟨r, h⟩
  exact h r (Nat.le_refl r) (Nat.le_refl r)

example (n : Nat) :
    (do let r ← id' n; id' r)
      ⦃ r => True → ∀ j, (_h : j ≤ r ∧ r ≤ j) → (∃ k, k + j = r) → j = n ⦄ := by
  step
  apply WP.spec_mono (id'_spec r)
  intro r' hr' j h1 h2 k hk
  guard_hyp h1 : j ≤ r'
  guard_hyp h2 : r' ≤ j
  guard_hyp hk : k + j = r'
  agrind

example (r : core.result.Result Never Nat) (e : Nat) (hr : r = .Err e) :
    (do
      let out ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame Nat) r
      ok (out, ()))
      ⦃ status state =>
        match status with
        | .Ok _ => False
        | .Err error => error = e ∧ state = () ⦄ := by
  step*

end Aeneas.Tactic.Step.Tests.IntroSpec
