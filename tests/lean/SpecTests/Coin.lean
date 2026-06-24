import Aeneas.Std.Primitives
import Aeneas.Std.Delab
import Std.Do
import Aeneas.Std.Spec
import Aeneas.Std.WP
import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect
import Aeneas.Std
import Std
import Aeneas.Tactic.Step
import Aeneas

open Aeneas
open Std Result WP Data Coinductive Effect Lean.Order

def Coin : Effect := {
   I := Unit
   O := fun _ => Bool
}

def ITreeC := ITree Coin

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
    simp only
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
  · simp only
    exists m, k

  instance : MonadLift Result ITreeC where
    monadLift r := match r with
      | .fail _e => .div -- TODO
      | .div => .div
      | .ok x => .ret x

theorem spec_coinSpec {α} {x : Result α} {p: Post α} : spec x p → coinSpec p x := by
  intros s
  cases x
  · apply coinSpec.ret
    assumption
  · contradiction
  · contradiction
#check spec_coinSpec

@[simp]
theorem qimp_coinSpec_unit {α} (P : Unit → Prop) (k : Unit → ITreeC α) (Q : α → Prop) :
  qimp_coinSpec P k Q ↔ (P () → coinSpec Q (k ())) := by
  grind [qimp_coinSpec]

@[simp]
theorem qimp_coinSpec_exists {α β γ} (P : γ → α → Prop) (k : α → ITreeC β) (Q : β → Prop) :
  qimp_coinSpec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_coinSpec (P x) k Q := by
  simp only [qimp_coinSpec, forall_exists_index]; grind

def qimp_coinSpec_iff {α β} (P : α → Prop) (k : α → ITreeC β) (Q : β → Prop) :
  qimp_coinSpec P k Q ↔ ∀ x, imp (P x) (coinSpec Q (k x)) := by
  simp [qimp_coinSpec, imp]

#check CoInd.unfold

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

#register_spec_statement {
    spec_name := ``coinSpec
    arity := 3
    program_index := 2
    post_index := 1
    mk_spec_mono := ``coinSpec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``coinSpec_bind
    mk_spec_bind_skip_args := 4
    uncurry_elim_tactics := #[
      ``qimp_coinSpec_unit,
      ``Std.WP.qimp_unit,
      ``qimp_coinSpec_exists,
      ``Std.WP.qimp_exists,
      ``forall_unit, ``true_imp_iff
    ]
    qimp_elim_tactics := #[
      ``qimp_coinSpec_iff,
      ``Std.WP.qimp_iff,
      ``Std.WP.imp_and_iff, ``Std.uncurry_apply_pair,
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair,
      ``Std.WP.imp_exists_iff,
      ``forall_unit, ``true_imp_iff
    ]
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


  def res : Result Nat := .ok 5
  def itreec : ITreeC Nat := res


  #check I32.add_spec
  -- set_option trace.Step true

  theorem test : coinSpec (fun z => z.val == 6)
    (do let x ← 1#i32 + 2#i32
        let y ← x + x
        ITree.vis () fun (b : Bool) =>
        if b then ITree.ret y else ITree.ret 6#i32)  := by
    step
    step
    apply coinSpec.vis
    intros b
    cases b
    · simp [*]
    · simp [*]
