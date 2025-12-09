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

theorem progress_thm (m:Result α) (k:α -> Result β) (Pₘ:Post α) (Pₖ:Post β) :
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

@[simp]
theorem spec_ok (x : α) : spec (.ok x) p ↔ p x := by simp [spec, theta, wp_return]

scoped syntax:lead (name := specSyntax) term:lead " ⦃" "⇓" term " => " term "⦄" : term

macro_rules
  | `($x ⦃⇓ $r => $P⦄)  => `(Aeneas.Std.WP.spec $x (fun $r => $P))

example : .ok 0 ⦃⇓ r => r = 0⦄ := by simp

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
