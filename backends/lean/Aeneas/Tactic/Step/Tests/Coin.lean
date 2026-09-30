module
import Aeneas.Std
import Aeneas.Tactic.Step

/-! # Coinductive specifications over `ITree`s

This file shows how to build coinductive predicates over `ITree`s, and how to register them with
the `step` tactic (see `#register_spec_info` below).
-/

open Aeneas
open Std Result WP Data Coinductive Effect Lean.Order

namespace Aeneas.Tactic.Step.Tests.Coin

def CoinEffect : Effect := {
   I := Unit
   O := fun _ => Bool
}

def ITreeC := ITree CoinEffect

-- can just use coinductive props!
coinductive coinSpec {α} (p : Post α) : (x : ITreeC α) → Prop where
| ret : ∀ x, p x → coinSpec p (ITree.ret x)
| vis : ∀ k, (∀ b, coinSpec p (k b)) → coinSpec p (ITree.vis () k)

theorem coinSpec_mono {α} {P₁ : Post α} {m : ITreeC α} {P₀ : Post α} (h : coinSpec P₀ m):
  (∀ x, P₀ x → P₁ x) → coinSpec P₁ m := by
  intros
  refine coinSpec.coinduct _ (coinSpec P₀) ?_ _ h
  intros x c
  cases c <;> grind only

/-- Implication of a `dspec` predicate with quantifier -/
def qimp_coinSpec {α β} (P : α → Prop) (k : α → ITreeC β) (Q : β → Prop) : Prop :=
  ∀ x, P x → coinSpec Q (k x)

theorem coinSpec_bind {α β} {k : α -> ITreeC β} {Pₖ : Post β} {m : ITreeC α} {Pₘ : Post α} :
  coinSpec Pₘ m →
  (qimp_coinSpec Pₘ k Pₖ) →
  coinSpec Pₖ (ITree.bind m k) := by
  intro Hm Hk
  refine coinSpec.coinduct _
    (fun t => ∃ (m : ITreeC α) (k : _), t = ITree.bind m k ∧ coinSpec Pₘ m ∧ qimp_coinSpec Pₘ k Pₖ)
    ?_ _ ?_
  · clear k Hk
    -- simp only
    rintro i ⟨m, k, rfl, cm, ck⟩
    cases cm with
    | ret a Pₘa =>
      simp
      have test := ck a Pₘa
      generalize h : k a = thing at *
      clear h
      have ck := ck a
      clear ck
      clear ck k
      cases test with
      | ret a' Pa' =>
        left
        grind
      | vis m' k' =>
        right
        exists m'
        simp
        intros b
        exists (ITree.ret a)
        simp [*, coinSpec.ret]
        unfold qimp_coinSpec
        exists (fun _ => m' b) -- this seems really weird. is the statement really right?
        simp [*]
    | vis m k =>
      simp
      right
      grind
  · --simp only
    exists m, k

instance : MonadLift Result ITreeC where
  monadLift r :=
  match r.match with
  | .ok a => .ret a
  | _ => .div -- TODO

theorem spec_coinSpec {α} {x : Result α} {p: Post α} : spec x p → coinSpec p x := by
  intros s
  cases x
  · apply coinSpec.ret
    simp [spec_ok] at s
    assumption
  · simp at s
  · simp at s

@[simp]
theorem qimp_coinSpec_unit {α} (P : Unit → Prop) (k : Unit → ITreeC α) (Q : α → Prop) :
  qimp_coinSpec P k Q ↔ (P () → coinSpec Q (k ())) := by
  grind [qimp_coinSpec]

@[simp]
theorem qimp_coinSpec_exists {α β γ} (P : γ → α → Prop) (k : α → ITreeC β) (Q : β → Prop) :
  qimp_coinSpec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_coinSpec (P x) k Q := by
  simp only [qimp_coinSpec, forall_exists_index]; grind

def qimp_coinSpec_iff {α β} (P : α → Prop) (k : α → ITreeC β) (Q : β → Prop) :
  qimp_coinSpec P k Q ↔ ∀ x, P x → coinSpec Q (k x) := by
  simp [qimp_coinSpec]

@[simp, grind =, agrind =]
theorem coinSpec_ret {α p} (x : α) : coinSpec p (ITree.ret x) ↔ p x := by
  constructor
  · intros s
    generalize h : ITree.ret x = thing at s
    cases s with
    | @ret x asdf =>
    have h := congrArg (CoInd.unfold _) h
    cases h
    assumption
    | vis k _ =>
    have h := congrArg (CoInd.unfold _) h
    cases h
  · intros
    apply coinSpec.ret
    assumption

open Lean Meta Elab Tactic in
meta def prepareIntroOutputs : PrepareIntroOutputs := do
  withMainContext do
  let goalTy := (← instantiateMVars (← getMainTarget)).consumeMData
  let (type, tree) ← match_expr goalTy with
    | qimp_coinSpec α _ P k Q =>
      let type ← withLocalDeclD `x α fun x => do
        let body ← mkAppM ``coinSpec #[Q, mkApp k x]
        mkForallFVars #[x] (← mkArrow (mkApp P x) body)
      pure (type, ← Step.getContInput k)
    | _ =>
      if goalTy.isForall then pure (goalTy, .leaf none)
      else throwError "Expected qimp_coinSpec or a quantified mono premise, got:\n{goalTy}"
  Step.prepareIntroOutputsWith type tree do
    let _ ← Simp.simpAt true { failIfUnchanged := false, iota := false }
      { simpThms := #[← Step.stepSimpExt.getTheorems],
        addSimpThms := #[``qimp_coinSpec_iff,
          ``Std.uncurry_apply_pair, ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair,
          ``forall_unit, ``true_imp_iff,
          ``Prod.forall, ``Step.forall_punit, ``and_imp, ``exists_imp] }
      (.targets #[] true)

#register_spec_info {
  spec_name := ``coinSpec
  arity := 3
  program_index := 2
  post_index := 1
  mk_spec_mono := ``coinSpec_mono
  mk_spec_mono_skip_args := 2
  mk_spec_bind := ``coinSpec_bind
  mk_spec_bind_skip_args := 4
  prepare_intro_outputs := ``prepareIntroOutputs
  to_mvcgen := .none
  liftings := #[
    { from_statement := ``Std.WP.spec
      conversion_thm := ``spec_coinSpec
      conversion_thm_inferred_args := 3 }
  ]
}

instance : Monad ITreeC := instMonadITree
instance {T} : Lean.Order.PartialOrder (ITreeC T) := instPartialOrderCoIndOfInhabitedPUnit _
noncomputable instance {T} : Lean.Order.CCPO (ITreeC T) := instCCPOCoIndOfInhabitedPUnit _
instance : MonoBind ITreeC := instMonoBindITree

/- Exercise both reasoning about a terminal call and about a let-binding. -/
example (n : Nat) (f : ITreeC Nat) (h : coinSpec (fun x => x = n) f) :
    coinSpec (fun x => x = n) f := by
  step with h as ⟨x, hx⟩
  exact hx

example (n : Nat) (f : ITreeC Nat) (g : Nat → ITreeC Nat)
    (h : coinSpec (fun x => x = n) f)
    (hg : ∀ x, coinSpec (fun y => y = x) (g x)) :
    coinSpec (fun y => y = n) (do let x ← f; g x) := by
  step with h as ⟨x, hx⟩
  step with hg as ⟨y, hy⟩
  exact hy.trans hx

end Aeneas.Tactic.Step.Tests.Coin
