import Aeneas.Std.Primitives
import Std.Do

namespace Aeneas.Std.WP

open Std
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

def post (x : Result α) (P: α -> Prop) :=
  (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P a⌝, fun e => ⌜False⌝⟩)

def triple (pre:Prop) (x : Result α) (P: α -> Prop) :=
  ⌜pre⌝ ⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P a⌝, fun e => ⌜False⌝⟩

def f (x:Int) : Result Int := if x ≥ 0 then .ok x else .ok 0

theorem myt x : triple (x ≥ 0) (f x) (fun r => r = x) := by
  intro pre
  unfold f
  simp
  sorry

end Aeneas.Std.WP
