import Aeneas.Std.Primitives
import Std.Do
import Iris.BI
-- import Iris.ProofMode
import Nola

namespace Aeneas.Std.WP

axiom GF : Iris.BundledGFunctors
abbrev sProp := aProp.{1} GF -- TODO: we have to be constant in the universe,
                             -- otherwise we have problems when lifting from Pure

open Std

abbrev Post α := (α -> Prop)
abbrev Pre := Prop
abbrev SLPost (α:Type) := (α → sProp)
abbrev SLPre := sProp


theorem proof_example_1 (P Q R : sProp) (Φ : SLPost α) :
  P ∗ Q ∗ □ R ⊢ □ (R -∗ ∃ x, Φ x) -∗ ∃ x, Φ x ∗ P ∗ Q
:= by
  iintro ⟨HP, HQ, □HR⟩ □HRΦ
  ispecialize HRΦ HR as HΦ
  icases HΦ with ⟨x, _HΦ⟩
  iexists x
  isplitr
  · iassumption
  isplitl [HP]
  · iexact HP
  · iexact HQ

def Wp (α : Type) := SLPost α → SLPre
def wp_return (x:α) : Wp α :=
  fun p => p x
def wp_bind (m:Wp α) (k:α -> Wp β) : Wp β :=
  fun p => m (fun r => k r p)

noncomputable
def theta (m:Result α) : Wp α :=
  match m with
  | .ok x => wp_return x
  | .fail _ => fun _ => iprop(⌜False⌝)
  | .div => fun _ => iprop(⌜False⌝)

-- def p2wp (post:Post α) : Wp α :=
--   fun p => forall r, post r → p r

-- def spec_general (x:Result α) (p:Post α) :=
--   wp_ord (p2wp p) (theta x)

noncomputable
def lift_to_SLPost (Q:Post α) : SLPost α :=
  fun v => iprop(⌜Q v⌝)

def slspec (P:SLPre) (x:Result α) (Q:SLPost α) :=
  P ⊢ theta x Q

def spec (x:Result α) (Q:Post α) :=
  slspec iprop(True) x (lift_to_SLPost Q)

-- Base theorems
-- Proofs about slspec
theorem slspec_ok (P:SLPre) (x : α) (Q:SLPost α): slspec P (.ok x) Q ↔ P ⊢ Q x := by
  simp [slspec, theta, wp_return]


theorem slspec_frame {m:Result α} :
  slspec P m Q →
  (forall F, slspec iprop(P ∗ F) m (fun x => iprop(Q x ∗ F))) := by
  intro Hspec F
  sorry

theorem slspec_consequence
  {P₁:SLPre} {Q₁:SLPost α} {m:Result α}
  {P₀:SLPre} {Q₀:SLPost α} (h : slspec P₀ m Q₀) :
  (P₁ ⊢ P₀ ∗ F) →
  (∀ x, F ∗ Q₀ x ⊢ Q₁ x) →
  slspec P₁ m Q₁ := by
  intros HMonPre HMonPost
  sorry

-- Derived theorems
theorem slspec_bind {F:sProp} {k:α -> Result β} {P:SLPre} {Qₖ:SLPost β} {m:Result α} {Pₘ:SLPre} {Qₘ:SLPost α} :
  slspec Pₘ m Qₘ →
  (P ⊢  Pₘ ∗ F) →
  (forall x, slspec iprop((Qₘ x) ∗ F) (k x) Qₖ) →
  slspec P (Std.bind m k) Qₖ := by
  intro Hm Hk Hx
  cases m
  · rename_i x
    simp
    apply slspec_consequence (Hx x) --iprop((Qₘ x) ∗ F) Qₖ
    · sorry
    · sorry
    · sorry
    -- · have := slspec_frame (.ok x) Hm F
    -- apply (slspec_ok _ _ Hm)
  · sorry
  · sorry

-- Proofs about spec
@[simp, grind =]
theorem spec_ok (x : α) : spec (.ok x) Q ↔ Q x := by
  simp [spec, slspec, lift_to_SLPost, theta, wp_return]
  apply Iff.intro
  · intro h
    sorry -- Cezar: I think it duable
  · intro h
    ipure_intro
    intro
    exact h

theorem spec_ok_l (x : α) : spec (.ok x) Q → Q x := by
  sorry

theorem spec_bind {k:α -> Result β} {Qₖ:Post β} {m:Result α} {Qₘ:Post α} :
  spec m Qₘ →
  (forall x, Qₘ x → spec (k x) Qₖ) →
  spec (Std.bind m k) Qₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    apply (spec_ok_l _ Hm)
  · simp
    apply Hm
  · simp
    apply Hm

theorem spec_consequence {Q₁:Post α} {m:Result α} {Q₀:Post α} (h : spec m Q₀):
  (∀ x, Q₀ x → Q₁ x) → spec m Q₁ := by
  intros HMonPost
  unfold spec
  apply slspec_consequence h
  rotate_right
  · apply iprop(⌜True⌝)
  · iintro %H
    ipure_intro
    simp
  · intro x
    unfold lift_to_SLPost
    iintro ⟨ %_, %HQ₀ ⟩
    ipure_intro
    apply HMonPost
    exact HQ₀


theorem progress_spec_equiv_exists (m:Result α) (P:Post α) :
  spec m P ↔ (∃ y, m = .ok y ∧ P y) :=
  by
    cases m
    · sorry
    · sorry
    · sorry

theorem progress_spec_exists {m:Result α} {P:Post α} :
  spec m P → (∃ y, m = .ok y ∧ P y) := by
  exact (progress_spec_equiv_exists m P).1

theorem progress_exists_spec {m:Result α} {P:Post α} :
  (∃ y, m = .ok y ∧ P y) → spec m P := by
  exact (progress_spec_equiv_exists m P).2

theorem spec_frame {m:Result α} :
  spec m Q →
  (forall F, slspec F m (fun x => iprop((lift_to_SLPost Q x) ∗ F))) := by
  intro Hspec F
  sorry

theorem lift_spec_bind {k:α -> Result β} {P:SLPre} {Qₖ:SLPost β} {m:Result α} {Qₘ:Post α} :
  spec m Qₘ →
  (forall x, slspec iprop(⌜(Qₘ x)⌝ ∗ P) (k x) Qₖ) →
  slspec P (Std.bind m k) Qₖ := by
  sorry

theorem spec_bind_lift {k:α -> Result β} {P:SLPre} {Qₖ:Post β} {m:Result α} {Qₘ:SLPost α} :
  slspec P m Qₘ →
  (forall x, slspec iprop(Qₘ x) (k x) (lift_to_SLPost Qₖ)) →
  spec (Std.bind m k) Qₖ := by
  sorry

theorem lift_spec_consequence {P:SLPre} {Q₁:SLPost α} {m:Result α} {Q₀:Post α} (h : spec m Q₀):
  (∀ x, ⌜Q₀ x⌝ ⊢ Q₁ x) → slspec P m Q₁ := by sorry

scoped syntax:lead (name := specSyntax) "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := specSyntaxPred) "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntax) " ⦃" term " ⦄" term:lead " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntaxPred) " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

macro_rules
  | `(($x) ⦃⇓ $r => $Q⦄)  => `(Aeneas.Std.WP.spec $x (fun $r => $Q))
  | `(($x) ⦃⇓ $Q:term⦄)  => `(Aeneas.Std.WP.spec $x (fun _ => $Q))
  | `(⦃$P⦄ $x ⦃⇓ $r =>  $Q⦄)  => `(Aeneas.Std.WP.slspec $P $x (fun $r => iprop($Q)))
  | `(⦃$P⦄ $x ⦃⇓ $Q⦄)  => `(Aeneas.Std.WP.slspec $P $x (fun _ => iprop($Q)))
-- scoped syntax:lead (name := slspecSyntax)
--   " ⦃" term "⦄" term:lead " ⦃" "⇓" term " => " term "⦄" : term

-- macro_rules
--   | `(⦃$P⦄ $x ⦃⇓ $r => $Q⦄)  => `(Aeneas.Std.WP.slspec $P $x (fun $r => $Q))

example : (.ok 0) ⦃⇓ r => r = 0⦄ := by simp

def add1 (x : Nat) := Result.ok (x + 1)
theorem  add1_spec (x : Nat) : (add1 x) ⦃⇓ y => y = x + 1⦄ :=
  by simp [add1]

example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃⇓ y => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro y h
    -- progress as ⟨ y1, z1⟩
    apply spec_consequence (add1_spec _)
    intro y' h
    --
    grind

def add2 (x : Nat) := Result.ok (x + 1, x + 2)
theorem  add2_spec (x : Nat) : (add2 x) ⦃⇓ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃⇓ (y, _) => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec
    intro tmp h
    split at h
    rename_i tmp y z
    clear tmp
    -- progress as ⟨ y1, z1⟩
    apply spec_consequence
    . apply add2_spec
    intro tmp h
    split at h
    rename_i tmp y1 z1
    clear tmp
    --
    grind

-- TODO:
-- noncomputable
-- example incr_ptr (p : RawPtr U32) : ITree Unit := do
--   let x0 ← read_ptr p
--   let x1 ← UScalar.add x0 1#u32
--   write_ptr p x1

def RawPtr (_ : Type) := Nat
axiom ptr {α} : RawPtr α → α → sProp
axiom eqPtr {α} : RawPtr α → RawPtr α → sProp

noncomputable
def emp : sProp := iprop(True)
notation " ∅ " => emp

macro:max x:term " ↦ " y:term : term => `(ptr $x $y)

axiom read_ptr {α : Type} (p : RawPtr α) : Result α
axiom read_ptr.spec {α} {x : α} {p : RawPtr α} :
  ⦃ p ↦ x ⦄ read_ptr p ⦃⇓ x' => (p ↦ x) ∧ ⌜x = x'⌝ ⦄

axiom write_ptr {α : Type} (p : RawPtr α) (x : α) : Result Unit
axiom write_ptr.spec {α} (x:α) {x' : α} {p : RawPtr α} :
  ⦃ p ↦ x ⦄ write_ptr p x' ⦃⇓ p ↦ x' ⦄

axiom mut_to_raw {α} (x : α) : Result (RawPtr α)
axiom mut_to_raw.spec {α} (x : α) : ⦃ ∅ ⦄ mut_to_raw x ⦃⇓ p => p ↦ x ⦄

axiom end_mut_to_raw {α} (p : RawPtr α) : Result α
axiom end_mut_to_raw.spec {α : Type} {x : α} (p : RawPtr α) :
  ⦃ p ↦ x ⦄ end_mut_to_raw p ⦃⇓ ∅ ⦄


noncomputable
def incr_ptr (p : RawPtr Nat) : Result Unit := do
  let x0 ← read_ptr p
  let x1 ← add1 x0
  write_ptr p x1

theorem entails_empty : ⊢ ∅ := by sorry
def incr_ptr.spec (p : RawPtr Nat) (x : Nat) :
  ⦃ p ↦ x ⦄ incr_ptr p ⦃⇓ p ↦ (x+1) ⦄
  := by
  unfold incr_ptr
  -- progress as ⟨ x' ⟩
  apply slspec_bind read_ptr.spec
  · -- TODO: iframe
    iintro H
    isplitl [H]
    · iapply H
    · apply entails_empty
  intro x'
  -- progress as ⟨ y ⟩
  apply lift_spec_bind (add1_spec _)
  intro y
  -- progress
  apply slspec_consequence (write_ptr.spec _)
  · -- TODO: iframe
    iintro ⟨ Hy, ⟨ Hp, Hx' ⟩ , _ ⟩ -- TODO: bug, one cannot use % on Hy and Hx here
    isplitl [Hp]
    iapply Hp
    iapply Hy -- TODO: need icombine tactic
    -- icombine [Hy, Hx'] as Hyx
    -- iapply Hyx
  · intro _
    sorry
    -- iintro ⟨ ⟨ Hy, Hx'⟩ , Hp ⟩
    -- rewrite [Hx', Hy]
    -- iframe
    -- isplitl [Hy]
    -- iexact Hy
    -- iexact Hx'

noncomputable
def incr_borrow (x : Nat) : Result Nat := do
  let xp ← mut_to_raw x
  let xv ← read_ptr xp
  let xv1 ← add1 xv
  let _ ← write_ptr xp xv1
  end_mut_to_raw xp -- inserted by Aeneas as the backward function for `mut_to_raw`:

theorem incr_borrow.spec (x : Nat) :
  (incr_borrow x) ⦃⇓ y => y = x + 1 ⦄ := by
  unfold incr_borrow
  -- progress as ⟨ p ⟩
  apply spec_bind_lift (mut_to_raw.spec _)
  intro p
  -- progress as ⟨ x' ⟩
  apply slspec_bind (read_ptr.spec)
  · --iframe
    iintro Hp
    isplitl [Hp]
    · iapply Hp
    · apply entails_empty
  intro x'
  -- progress as ⟨ y ⟩
  apply lift_spec_bind (add1_spec _)
  intro y
  -- progress
  apply slspec_bind (write_ptr.spec _)
  · iintro ⟨ Hy, ⟨ ⟨ Hp, Hx⟩ , _ ⟩  ⟩
    isplitl [Hp]
    · iapply Hp
    · iapply Hy -- TODO: need icombine to combine Hy and Hx
  simp
  -- progress
  apply slspec_consequence (end_mut_to_raw.spec _)
  · --iframe
    iintro ⟨ Hp, Hy ⟩
    isplitl [Hp]
    · iapply Hp
    · iapply Hy
  · intro x'
    iintro ⟨ %Hy, _ ⟩
    unfold lift_to_SLPost
    ipure_intro
    simp
    sorry -- TODO: related to previous TODO, need icombine tactic

-- Equal or Disjoint pointers
inductive EqOrDisj (α : Type) where
| equal (v : α)
| disjoint (v1 v2 : α)

noncomputable
def isEqOrDisj {α} (xp yp : RawPtr α) (v : EqOrDisj α) : sProp :=
  match v with
  | .equal v => iprop((xp ↦ v) ∗ (yp ↦ v) ∗ eqPtr xp yp)
  | .disjoint xv yv => iprop((xp ↦ xv) ∗ (yp ↦ yv))

def EqOrDisj.read {α} (eod : EqOrDisj α) : α :=
  match eod with
  | .equal v => v
  | .disjoint v _ => v

def EqOrDisj.write {α} (eod : EqOrDisj α) (yv:α): EqOrDisj α :=
  match eod with
  | .equal _ => equal yv
  | .disjoint xv _ => disjoint xv yv

theorem read_ptr.spec' {α} {eod : EqOrDisj α} {xp yp : RawPtr α} :
  ⦃ isEqOrDisj xp yp eod ⦄ read_ptr xp ⦃⇓ x => ⌜x = eod.read⌝ ∗ isEqOrDisj xp yp eod ⦄
  := by
  simp [isEqOrDisj, EqOrDisj.read]
  cases eod <;> simp <;> apply slspec_consequence (read_ptr.spec)
  · -- iframe?
    iintro ⟨ Hx, Hyeq ⟩
    isplitl [Hx]
    · iapply Hx
    · iapply Hyeq
  · intro x
    -- iframe
    iintro ⟨ ⟨ Hy, Heq ⟩, Hx, %Hxv ⟩
    isplitl []
    · symm at Hxv
      ipure_intro
      apply Hxv
    isplitl [Hx]
    · iapply Hx
    isplitl [Hy]
    · iapply Hy
    iapply Heq
  · -- iframe
    iintro ⟨ Hx, Hy ⟩
    isplitl [Hx]
    · iapply Hx
    · iapply Hy
  · intro x
    -- iframe
    iintro ⟨ Hy, Hx, %Hxv ⟩
    isplitl []
    · symm at Hxv
      ipure_intro
      apply Hxv
    isplitl [Hx]
    · iapply Hx
    · iapply Hy


theorem write_ptr.spec' {α} {eod: EqOrDisj α} {xp yp : RawPtr α} {v:α} :
  ⦃ isEqOrDisj xp yp eod ⦄ write_ptr yp v ⦃⇓ isEqOrDisj xp yp (eod.write v) ⦄ := by
  simp [isEqOrDisj, EqOrDisj.write]
  cases eod <;> simp_all <;> apply slspec_consequence (write_ptr.spec _)
  · iintro ⟨ Hx, Hy, Heq ⟩
    isplitl [Hy]
    · iapply Hy
    · iapply Hx -- TODO: need icombine tactic
  · sorry -- TODO: related to previous TODO
  · -- iframe
    iintro ⟨ Hx, Hy ⟩
    isplitl [Hy]
    · iapply Hy
    · iapply Hx
  · -- iframe
    intro _
    iintro ⟨ Hx, Hy ⟩
    isplitl [Hx]
    iapply Hx
    iapply Hy
end Aeneas.Std.WP


namespace Aeneas.Std.WP

open Std Result
open Std.Do

instance Result.instWP : WP (Result) (.except Error .pure) where
    wp
        | .ok v => wp (pure v : Except Error _)
        | .fail e => wp (throw e : Except Error _)
        | .div => PredTrans.const ⌜False⌝

instance : LawfulMonad Result where
    map_const := sorry
    id_map := sorry
    seqLeft_eq := sorry
    seqRight_eq := sorry
    pure_seq := sorry
    pure_bind := sorry
    bind_pure_comp := sorry
    bind_map := sorry
    bind_assoc := sorry

instance : WPMonad Result (.except Error .pure) where
  wp_pure := by
    intros
    ext Q
    simp [wp, PredTrans.pure, pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [Result.instWP]
    ext Q
    cases x <;> simp [PredTrans.const]

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e)⌝⟩) → P x := by
  intro hspec
  simp only [instWP] at hspec
  split at hspec <;> simp_all

end Aeneas.Std.WP
