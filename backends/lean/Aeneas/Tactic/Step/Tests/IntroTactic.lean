module
import Aeneas.Tactic.Step
public meta import Lean
public meta import Aeneas.Tactic.Step

open Aeneas

/-!
# Tests for `SpecInfo.intro_tactic`

The fixture is irreducible so that the tests depend on defining an `intro_tactic`.
-/

namespace Aeneas.Tactic.Step.Tests.IntroTactic

abbrev Post (α : Type) := α → Prop

def Post.entails (P Q : Post α) : Prop := ∀ value, P value → Q value

theorem Post.entails_iff (P Q : Post α) :
    Post.entails P Q ↔ ∀ value, P value → Q value :=
  Iff.rfl

def triple (P : Prop) (m : Id α) (Q : Post α) : Prop :=
  P → Q m

theorem triple_step_mono {P Pm : Prop} {Q : Post α}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q := by
  intro hP
  exact hPost m (hStep (hPre hP))

theorem triple_step_bind {P Pm : Prop} {next : α → Id β} {Q : Post β}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hNext : ∀ value, triple (Qm value) (next value) Q) :
    triple P (m >>= next) Q := by
  intro hP
  exact hNext m (hStep (hPre hP))

theorem triple_pull {P : Prop} {m : Id α} {Q : Post α} :
    triple P m Q ↔ (P → triple True m Q) := by
  constructor
  · intro h hP _
    exact h hP
  · intro h hP
    exact h hP True.intro

theorem triple_true (P : Prop) (m : Id α) :
    triple P m (fun _ => True) := by
  intro _
  trivial

/- intro tactic: it is responsible for the whole normalization of the mono and bind
   premises, so it exposes the binders of `Post.entails` itself, introduces them — `step`
   reverts what it introduces — and pulls the precondition of the continuation. -/
open Lean Elab Tactic in
meta def pullPre : Aeneas.IntroFn := do
  evalTactic (← `(tactic| (
    try rw [Post.entails_iff]
    intros
    first
    | exact triple_true _ _
    | (rw [triple_pull]; try rw [and_imp])
    | skip)))
  return 0

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    intro_tactic := some ``pullPre
    to_mvcgen := none
    liftings := #[]
  }

/- `intro_tactic` must name an `IntroFn`, not a tactic. -/
/--
error: `intro_tactic` must be a function of type `Aeneas.IntroFn`, but `Lean.Parser.Tactic.assumption` has type Lean.ParserDescr
-/
#guard_msgs in
#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    intro_tactic := some ``Lean.Parser.Tactic.assumption
    to_mvcgen := none
    liftings := #[]
  }

/-! ### Programs and tests -/

@[irreducible] def incr (value : Nat) : Id Nat :=
  value + 1

@[step]
theorem incr_spec (value : Nat) :
    triple True (incr value) (fun result => result = value + 1) := by
  unfold incr
  intro _
  rfl

attribute [irreducible] triple

@[irreducible] def incrTwice (value : Nat) : Id Nat := do
  let once ← incr value
  incr once

/- `step as` names the result and the hypothesis exposed by `intro_tactic`. -/
/--
trace: case hNext
value once : ℕ
hOnce : once = value + 1
⊢ triple True (incr once) fun result => result = value + 1 + 1
-/
#guard_msgs in
set_option pp.mvars false in
example (value : Nat) :
    triple True (incrTwice value) (fun result => result = value + 1 + 1) := by
  unfold incrTwice
  step as ⟨ once, hOnce ⟩
  trace_state
  guard_hyp hOnce : once = value + 1
  step*

/- `step*?` includes hypotheses exposed by `intro_tactic` in its suggestion. -/
/--
info: Try this:

  [apply]     let* ⟨ once, once_post ⟩ ← incr_spec
    let* ⟨ result, result_post ⟩ ← incr_spec
    agrind
-/
#guard_msgs in
example (value : Nat) :
    triple True (incrTwice value) (fun result => result = value + 1 + 1) := by
  unfold incrTwice
  step*?

/- `intro_tactic` may solve a prepared continuation completely. -/
example (value : Nat) :
    triple True (incrTwice value) (fun _ => True) := by
  unfold incrTwice
  step

/-! ## `runIntroTactic` contract -/

open Lean Elab Tactic in
meta def constructorFn : Aeneas.IntroFn := do
  evalTactic (← `(tactic| constructor))
  return 0

elab "run_constructor" : tactic => do
  discard <| Step.runIntroTactic ``constructorFn

/- `runIntroTactic` rejects tactics that create multiple goals. -/
/--
error: `intro_tactic` must not create multiple goals
-/
#guard_msgs in
example (P Q : Prop) : P ∧ Q := by
  run_constructor

open Lean Elab Tactic in
meta def assumptionFn : Aeneas.IntroFn := do
  evalTactic (← `(tactic| assumption))
  return 0

elab "run_assumption" : tactic => do
  discard <| Step.runIntroTactic ``assumptionFn

/- `runIntroTactic` permits tactics that solve the goal completely. -/
example (P : Prop) (h : P) : P := by
  run_assumption

elab "run_intro_split" : tactic => do
  discard <| Step.runIntroTactic ``Aeneas.Std.WP.introTactic

open Lean Meta Elab Tactic in
elab "run_intro_pending " n:ident : tactic => withMainContext do
  let n := mkFVar (← getFVarId n)
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let goal ← getMainGoal
  let worker ← mkFreshExprSyntheticOpaqueMVar ((← goal.getType).replaceFVar n pending)
  setGoals [worker.mvarId!]
  discard <| Step.runIntroTactic ``Aeneas.Std.WP.introTactic
  let proof ← instantiateMVars worker
  if proof.getAppFn.isConst then
    throwError "Output normalization generalized a pending obligation"
  pending.mvarId!.assign n
  goal.assign worker

example (n : Nat) (P : Nat → Prop) (R : Prop) (hR : R) :
    ∀ value, value = n ∧ P value → R := by
  run_intro_pending n
  intro value heq hP
  guard_hyp heq : value = n
  guard_hyp hP : P value
  exact hR

/- `Std.WP.introTactic` splits the conjunction of the premise: it comes back with one binder per
   conjunct. -/
example (P Q R : Prop) (hR : R) : P ∧ Q → R := by
  run_intro_split
  guard_target = P → Q → R
  intro _ _
  exact hR

example (n : Nat) (P Q : Nat → Prop) (R : Prop) (hR : R) :
    (∃ x, x = n ∧ P x ∧ Q x) → R := by
  run_intro_split
  guard_target = P n → Q n → R
  intro _ _
  exact hR

example (n : Nat) (P : Nat → Prop) (R : Prop) (hR : R) :
    (∃ x, P x ∧ n = x) → R := by
  run_intro_split
  guard_target = P n → R
  intro _
  exact hR

example (b : Bool) (n : Nat) (P Q : Nat → Prop) (R : Prop) (hR : R) :
    (match b with
     | true => ∃ x, n = x ∧ P x ∧ Q x
     | false => ∃ x, P x ∧ x = n) → R := by
  run_intro_split
  guard_target = (match b with | true => P n ∧ Q n | false => P n) → R
  intro _
  exact hR

example (n : Nat) (P Q R : Prop) (hR : R) :
    ((n = n → True → Unit → P ∧ Q) ∧ (∃ x, x = n ∧ True)) → R := by
  run_intro_split
  guard_target = P → Q → R
  intro _ _
  exact hR

example (P Q : Prop) (R : P ∧ Q → Prop) (hR : ∀ h, R h) : ∀ h, R h := by
  run_intro_split
  guard_target = ∀ hp hq, R ⟨hp, hq⟩
  intro hp hq
  exact hR ⟨hp, hq⟩

example (Q R : Prop) (hR : R) : (Q ∧ ∃ f : Unit → Nat, f () = 0) → R := by
  run_intro_split
  guard_target = Q → ∀ f : Unit → Nat, f () = 0 → R
  intro _ _ _
  exact hR

elab "run_intro_split_compact" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  discard <| Step.runIntroTactic ``Aeneas.Std.WP.introTactic
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

/- Keep let-bound postconditions bundled. -/
example (compute : Nat → Nat × Nat) (P : Nat → Nat → Nat → Prop) (R : Prop) (hR : R) :
    ∀ output : Nat × Nat,
      Aeneas.Std.WP.uncurry' (fun a b =>
        let (x, y) := compute a
        P a b x ∧ P a b y) output → R := by
  run_intro_split
  guard_target = ∀ output : Nat × Nat,
    (let (x, y) := compute output.1
     P output.1 output.2 x ∧ P output.1 output.2 y) → R
  intro _ _
  exact hR

open Aeneas.Std Result

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

def conditional (bound : U32) : Result Bool := ok (bound.val = bound.val)

@[local step]
theorem conditional_spec (bound : U32) :
    conditional bound ⦃ result => bound.val = 0 → result = true ⦄ := by
  simp [conditional]

example : conditional 0#u32 ⦃ result => result = true ⦄ := by
  step as ⟨result, h⟩
  guard_hyp h : True → result = true
  exact h trivial

example (f : Result (Nat × Nat))
    (h : f ⦃ a b => ∃ witness : Bool, a = witness.toNat ∧ a = b ⦄) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄ := by
  step with h as ⟨a, b, witness, hw, hab⟩
  guard_hyp witness : Bool
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp hw : a = witness.toNat
  exact hab

example (f : Result (Nat × Nat))
    (h : f ⦃ p => ∃ witness : Bool, p.1 = witness.toNat ∧ p.1 = p.2 ⦄) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄ := by
  let* ⟨witness, a, b, hw, hab⟩ ← h
  guard_hyp witness : Bool
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp hw : a = witness.toNat
  exact hab

example (f : Result (Nat × Nat × Nat))
    (h : f ⦃ p =>
      ∃ witness : Bool × Nat, p.1 = witness.1.toNat ∧ p.2.1 = witness.2 ∧ p.2.1 = p.2.2 ⦄) :
    (do let (a, b, c) ← f; ok (a, b, c)) ⦃ _ b c => b = c ⦄ := by
  let* ⟨witness, a, b, c, ha, hb, hbc⟩ ← h
  guard_hyp witness : Bool × Nat
  guard_hyp ha : a = witness.1.toNat
  guard_hyp hb : b = witness.2
  exact hbc

example (f : Result (Nat × Nat))
    (h : f ⦃ p =>
      ∃ witness : Nat × Nat, p.1 = witness.1 ∧ p.2 = witness.2 ∧ witness.1 = witness.2 ⦄) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄ := by
  let* ⟨witness, a, b, ha, hb, hw⟩ ← h
  guard_hyp witness : Nat × Nat
  exact ha.trans (hw.trans hb.symm)

example (f : Result Unit) (h : f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄) :
    f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄ := by
  let* ⟨witness, hw⟩ ← h
  guard_hyp witness : Nat
  guard_hyp hw : witness > 0
  exact ⟨witness, hw⟩

example (f : Result (Option Nat)) (n : Nat)
    (h : f ⦃ x => ∃ witness, x = some witness ∧ witness ≤ n ⦄) :
    f ⦃ r => ∃ witness, r = some witness ∧ witness ≤ n ⦄ := by
  step with h
  guard_hyp r : Nat
  exact ⟨r, x_post, r_post⟩

example (f : Result (Nat × Nat))
    (h : f ⦃ p => ∃ witness : Bool, p.1 = witness.toNat ∧ p.1 = p.2 ⦄div) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄div := by
  let* ⟨witness, a, b, hw, hab⟩ ← h
  guard_hyp witness : Bool
  guard_hyp hw : a = witness.toNat
  simpa using hab

example (r : core.result.Result Never Nat) (e : Nat) (hr : r = .Err e) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame Nat) r
      ⦃ out => out = .Err e ⦄ := by
  step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.spec
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

example (f : Result (List Nat)) (n : Nat)
    (h : f ⦃ result => ∃ hlen : result.length = n, n = result.length ∧ hlen = hlen ⦄) :
    f ⦃ result => result.length = n ⦄ := by
  step with h as ⟨result, hlen, hlen'⟩
  guard_hyp result : List Nat
  guard_hyp hlen : result.length = n
  guard_hyp hlen' : n = result.length
  exact hlen

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

theorem triple_step_mono_plain {P Pm : Prop} {Q : Post α}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm) (hPost : ∀ value, Qm value → Q value) :
    triple P m Q :=
  triple_step_mono m Qm hStep hPre hPost

meta def bundledSpecInfo : SpecInfo := {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono_plain
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    to_mvcgen := none
    liftings := #[]
  }

#register_spec_info bundledSpecInfo

example (m : Id (Nat × Nat)) (n : Nat)
    (h : triple True m (fun p => p.2 = n)) :
    triple True m (Aeneas.Std.uncurry fun (_a : Nat) (b : Nat) => b ≤ n) := by
  step with h
  guard_hyp b_post : b = n
  exact Nat.le_of_eq b_post

example (m : Id Nat) (P Q : Nat → Prop)
    (h : triple True m (fun r => P r ∧ Q r)) : triple True m P := by
  step with h as ⟨result, post⟩
  guard_hyp post : P result ∧ Q result
  exact post.1

open Lean Elab Tactic in
meta def keepBundled : Aeneas.IntroFn := do
  evalTactic (← `(tactic| (intros; try rw [triple_pull])))
  return 0

#register_spec_info { bundledSpecInfo with intro_tactic := some ``keepBundled }

example (m : Id Nat) (P Q : Nat → Prop)
    (h : triple True m (fun r => P r ∧ Q r)) : triple True m P := by
  step with h as ⟨result, post⟩
  guard_hyp post : P result ∧ Q result
  exact post.1

example (m : Id Nat) (next : Nat → Id Nat) (P Q S : Nat → Prop)
    (h : triple True m (fun r => P r ∧ Q r))
    (hNext : ∀ r, P r → triple True (next r) S) :
    triple True (m >>= next) S := by
  step with h as ⟨result, post⟩
  guard_hyp post : P result ∧ Q result
  exact hNext result post.1

end Aeneas.Tactic.Step.Tests.IntroTactic
