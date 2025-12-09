import Aeneas.Std.Primitives
import Std.Do

namespace Aeneas.Std.WP

open Std

def Post α := (α -> Prop)
def Pre := Prop

def Wp α := Post α → Pre

def wp_return (x:α) : Wp α := fun p => p x

def wp_bind (m:Wp α) (k:α -> Wp β) : Wp β :=
  fun p => m (fun r => k r p)

def wp_ord (wp1 wp2:Wp α) :=
  forall p, wp1 p → wp2 p

def theta (m:Result α) : Wp α :=
  match m with
  | .ok x => wp_return x
  | .fail _ => fun _ => False
  | .div => fun _ => False

def p2wp (post:Post α) : Wp α :=
  fun p => forall r, post r → p r

def spec_general (x:Result α) (p:Post α) :=
  wp_ord (p2wp p) (theta x)

def spec (x:Result α) (p:Post α) :=
  theta x p

@[simp, grind =]
theorem spec_ok (x : α) : spec (.ok x) p ↔ p x := by simp [spec, theta, wp_return]

theorem spec_bind (m:Result α) (k:α -> Result β) (Pₘ:Post α) (Pₖ:Post β) :
  spec m Pₘ →
    (forall x, Pₘ x → spec (k x) Pₖ) →
      spec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    apply Hm
  · simp
    apply Hm
  · simp
    apply Hm

theorem spec_mono (m:Result α) (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind

theorem progress_spec_exists (m:Result α) (P:Post α) :
  spec m P ↔ (∃ y, m = .ok y /\ P y) :=
  by
    cases m
    · simp [spec, theta, wp_return]
    · simp [spec, theta]
    · simp [spec, theta]

scoped syntax:lead (name := specSyntax) term:lead " ⦃" "⇓" term " => " term "⦄" : term

macro_rules
  | `($x ⦃⇓ $r => $P⦄)  => `(Aeneas.Std.WP.spec $x (fun $r => $P))

example : .ok 0 ⦃⇓ r => r = 0⦄ := by simp

def add1 (x : Nat) := Result.ok (x + 1, x + 2)
theorem  add1_spec (x : Nat) : add1 x ⦃⇓ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add1]


example (x : Nat) :
  (do
    let (y, z) ← add1 x
    add1 y) ⦃⇓ (y, _) => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind
    . apply add1_spec
    intro tmp h
    split at h
    rename_i tmp y z
    clear tmp
    -- progress as ⟨ y1, z1⟩
    apply spec_mono
    . apply add1_spec
    intro tmp h
    split at h
    rename_i tmp y1 z1
    clear tmp
    --
    grind


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
