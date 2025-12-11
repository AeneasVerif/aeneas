import Aeneas.Std.Primitives
import Std.Do
import Iris.BI
import Iris.Std.Heap
-- import Iris.ProofMode
import Nola

namespace Aeneas.Std.WP

axiom GF : Iris.BundledGFunctors
abbrev sProp := aProp.{1} GF -- TODO: we have to be constant in the universe,
                             -- otherwise we have problems when lifting from Pure

-- open Iris.BI
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

theorem spec_mono {Q₁:Post α} {m:Result α} {Q₀:Post α} (h : spec m Q₀):
  (∀ x, Q₀ x → Q₁ x) → spec m Q₁ := by
  intros HMonPost
  revert h
  sorry

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


-- Proofs about slspec
theorem slspec_ok (P:SLPre) (x : α) (Q:SLPost α): slspec P (.ok x) Q ↔ P ⊢ Q x := by
  simp [slspec, theta, wp_return]

theorem slspec_frame (m:Result α) :
  slspec P m Q →
  (forall F, slspec iprop(P ∗ F) m (fun x => iprop(Q x ∗ F))) := by
  intro Hspec F
  sorry

theorem slspec_mono
  {P₁:SLPre} {Q₁:SLPost α} {m:Result α}
  (P₀:SLPre) (Q₀:SLPost α) (h : slspec P₀ m Q₀) :
  (⊢ P₁ -∗ P₀) →
  (∀ x, Q₀ x ⊢ Q₁ x) →
  slspec P₁ m Q₁ := by
  intros HMonPre HMonPost
  sorry

theorem slspec_bind {k:α -> Result β} {P:SLPre} {Qₖ:SLPost β} {m:Result α} {Pₘ:SLPre} {Qₘ:SLPost α} :
  slspec Pₘ m Qₘ →
  (⊢ P -∗ Pₘ ∗ F) →
  (forall x, slspec iprop((Qₘ x) ∗ F) (k x) Qₖ) →
  slspec P (Std.bind m k) Qₖ := by
  intro Hm Hk Hx
  cases m
  · rename_i x
    simp
    apply slspec_mono iprop((Qₘ x) ∗ F) Qₖ
    · apply Hx
    · sorry
    · sorry
    -- · have := slspec_frame (.ok x) Hm F
    -- apply (slspec_ok _ _ Hm)
  · sorry
  · sorry

scoped syntax:lead (name := specSyntax) "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := specSyntaxPred) "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntax) " ⦃" term " ⦄" term:lead " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntaxPred) " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

macro_rules
  | `(($x) ⦃⇓ $r => $Q⦄)  => `(Aeneas.Std.WP.spec $x (fun $r => $Q))
  | `(($x) ⦃⇓ $Q:term⦄)  => `(Aeneas.Std.WP.spec $x $Q)
  | `(⦃$P⦄ $x ⦃⇓ $r =>  $Q⦄)  => `(Aeneas.Std.WP.slspec $x $P (fun $r => $Q))
  | `(⦃$P⦄ $x ⦃⇓ $Q⦄)  => `(Aeneas.Std.WP.slspec $x $P $Q)
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
    apply spec_mono (add1_spec _)
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
    apply spec_mono
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

-- def RawPtr (_ : Type) := Nat
-- axiom ptr {α} : RawPtr α → α → HProp

-- macro:max x:term " ~> " y:term : term => `(ptr $x $y)

-- axiom mut_to_raw {α} (x : α) : Result (RawPtr α)
-- axiom mut_to_raw.spec {α} (x : α) : ⦃ ∅ ⦄ (mut_to_raw x) ⦃ fun p => p ~> x ⦄
-- axiom end_mut_to_raw {α} (p : RawPtr α) : Result α
-- axiom end_mut_to_raw.spec {α : Type} {x : α} (p : RawPtr α) :
--   ⦃ p ~> x ⦄ (end_mut_to_raw p) ⦃ fun _ => ∅ ⦄


-- axiom read_ptr {α : Type} (p : RawPtr α) : ITree α
-- axiom write_ptr {α : Type} (p : RawPtr α) (x : α) : ITree Unit

-- axiom read_ptr.spec {α} {x : α} {p : RawPtr α} :
--   ⦃ p ~> x ⦄ (read_ptr p) ⦃ fun _ => p ~> x ⦄ {{ fun x' => x' = x }}

-- axiom write_ptr.spec {α} {x x' : α} {p : RawPtr α} :
--   ⦃ p ~> x ⦄ (write_ptr p x') ⦃ fun _ => p ~> x' ⦄ {{ fun () => True }}


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
