module
public import Aeneas.NonPos.Model.Cont

@[expose] public section
/-!
# Lifting: adding a least element

`Lift A` is `A` with a new least element `bot`; `up` is monotone.  This is a pointed ω-cpo whenever
`A` is admissible; it is how plain fields of unpointed type enter the inverse limit.
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe w

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod
set_option linter.unusedSectionVars false

inductive Lift (A : Type w) : Type w
  | bot : Lift A
  | up : A → Lift A

namespace Lift
variable {A : Type w} [Dom A]

def le : Lift A → Lift A → Prop
  | bot, _ => True
  | up _, bot => False
  | up a, up b => Dom.le a b

instance po : PartialOrder (Lift A) where
  rel := le
  rel_refl {x} := by cases x <;> simp [le, Dom.le_refl]
  rel_trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> simp_all [le]
    exact Dom.le_trans h₁ h₂
  rel_antisymm {x y} h₁ h₂ := by
    cases x <;> cases y <;> simp_all [le]
    exact Dom.le_antisymm h₁ h₂

theorem bot_le (x : Lift A) : (bot : Lift A) ⊑ x := trivial
theorem up_le_up {a b : A} : (up a : Lift A) ⊑ up b ↔ Dom.le a b := Iff.rfl
theorem not_up_le_bot {a : A} : ¬ ((up a : Lift A) ⊑ bot) := id
theorem le_bot {x : Lift A} (h : x ⊑ bot) : x = bot := by
  cases x with
  | bot => rfl
  | up a => exact absurd h not_up_le_bot
theorem up_le {a : A} {x : Lift A} (h : up a ⊑ x) : ∃ b, x = up b ∧ Dom.le a b := by
  cases x with
  | bot => exact absurd h not_up_le_bot
  | up b => exact ⟨b, rfl, h⟩

/-- `up` from index `n₀` on: the chain of the values (`a₀` is a dummy for the impossible case). -/
def tailVal (c : Chain (Lift A)) (a₀ : A) (n : Nat) : A :=
  match c n with | up a => a | bot => a₀

theorem up_at (c : Chain (Lift A)) {n₀ : Nat} {a₀ : A} (h : c n₀ = up a₀) {m : Nat} (hm : n₀ ≤ m) :
    c m = up (tailVal c a₀ m) := by
  obtain ⟨b, hb, _⟩ := up_le (h ▸ c.le hm)
  simp [tailVal, hb]

def tail (c : Chain (Lift A)) (n₀ : Nat) (a₀ : A) (h : c n₀ = up a₀) : Dom.Chain A :=
  @Chain.mk A Dom.po (fun n => tailVal c a₀ (n₀ + n)) fun n => by
    have h₁ := up_at c h (Nat.le_add_right n₀ n)
    have h₂ := up_at c h (Nat.le_trans (Nat.le_add_right n₀ n) (Nat.le_succ (n₀ + n)))
    have := c.step (n₀ + n)
    rw [h₁, h₂] at this
    exact this

theorem tail_spec (c : Chain (Lift A)) (n₀ : Nat) (a₀ : A) (h : c n₀ = up a₀) (n : Nat) :
    c (n₀ + n) = up (tail c n₀ a₀ h n) :=
  up_at c h (Nat.le_add_right n₀ n)

/-- Whether a chain contains an `up`. -/
def HasUp (c : Chain (Lift A)) : Prop := ∃ n a, c n = up a

theorem all_bot (c : Chain (Lift A)) (h : ¬ HasUp c) (n : Nat) : c n = bot := by
  cases hc : c n with
  | bot => rfl
  | up a => exact absurd ⟨n, a, hc⟩ h

open Classical in
def sup (c : Chain (Lift A)) : Lift A :=
  if h : HasUp c then
    up (Dom.sup (tail c (choose h) (choose (choose_spec h)) (choose_spec (choose_spec h))))
  else bot

open Classical in
theorem sup_pos (c : Chain (Lift A)) (h : HasUp c) :
    sup c = up (Dom.sup (tail c (choose h) (choose (choose_spec h)) (choose_spec (choose_spec h)))) := by
  simp [sup, h]

theorem sup_neg (c : Chain (Lift A)) (h : ¬ HasUp c) : sup c = bot := by
  simp [sup, h]

open Classical in
instance oc : OmegaComplete (Lift A) where
  bottom := bot
  bottom_le := bot_le
  sup := sup
  le_sup c n := by
    by_cases h : HasUp c
    · rw [sup_pos c h]
      have h₀ := choose_spec (choose_spec h)
      refine PartialOrder.rel_trans (c.le (Nat.le_add_left n (choose h))) ?_
      rw [tail_spec c _ _ h₀ n]
      exact up_le_up.2 (Dom.le_sup _ n)
    · rw [all_bot c h n]; exact bot_le _
  sup_le c x hx := by
    by_cases h : HasUp c
    · rw [sup_pos c h]
      have h₀ := choose_spec (choose_spec h)
      obtain ⟨b, hb, _⟩ := up_le (h₀ ▸ hx (choose h))
      rw [hb]
      apply up_le_up.2
      apply Dom.sup_le
      intro n
      have := hx (choose h + n)
      rw [tail_spec c _ _ h₀ n, hb] at this
      exact this
    · rw [sup_neg c h]; exact bot_le _

/-- Suprema of nonempty chains: `up` of the supremum of the `up`-values, if there are any. -/
instance cc : ChainComplete (Lift A) := by
  letI : PartialOrder A := Dom.po
  letI : ChainComplete A := Dom.cc
  refine ⟨fun C hC hne => ?_⟩
  by_cases hup : ∃ a, C (up a)
  · have hCA : chain (fun a => C (up a)) := fun a b ha hb => hC _ _ ha hb
    have hs := chainSup_spec (fun a => C (up a)) hCA hup
    refine ⟨up (chainSup _ hCA hup), isSup_of (fun x hx => ?_) (fun u hu => ?_)⟩
    · cases x with
      | bot => exact bot_le _
      | up a => exact up_le_up.2 (isSup_le hs hx)
    · obtain ⟨a₀, ha₀⟩ := hup
      obtain ⟨b, rfl, _⟩ := up_le (hu _ ha₀)
      exact up_le_up.2 (isSup_le_of hs fun a ha => up_le_up.1 (hu _ ha))
  · refine ⟨bot, isSup_of (fun x hx => ?_) (fun u _ => bot_le u)⟩
    cases x with
    | bot => exact bot_le _
    | up a => exact absurd ⟨a, hx⟩ hup

/-- The lifted domain. -/
def domain (A : Type w) [Dom A] : Domain.{w} := Domain.of (Lift A)

/-- `up`, as a monotone map `A → Lift A`. -/
theorem up_mono {a b : A} (h : Dom.le a b) : (up a : Lift A) ⊑ up b := h

def isUp : Lift A → Prop
  | bot => False
  | up _ => True

theorem isUp_up (a : A) : isUp (up a : Lift A) := trivial

/-- The value of an `up`. -/
def get : (x : Lift A) → isUp x → A
  | up a, _ => a
  | bot, h => h.elim

theorem get_up (a : A) (h : isUp (up a : Lift A)) : get (up a) h = a := rfl
theorem get_of_eq {x : Lift A} {h : isUp x} {a : A} (e : x = up a) : get x h = a := by
  subst e; rfl
theorem up_get (x : Lift A) (h : isUp x) : up (get x h) = x := by
  cases x with
  | bot => exact h.elim
  | up a => rfl
theorem get_mono {x y : Lift A} (h : x ⊑ y) {hx : isUp x} {hy : isUp y} : Dom.le (get x hx) (get y hy) := by
  cases x with
  | bot => exact hx.elim
  | up a => cases y with
    | bot => exact hy.elim
    | up b => exact h
theorem exists_of_isUp {x : Lift A} (h : isUp x) : ∃ a, x = up a := by
  cases x with
  | bot => exact absurd h id
  | up a => exact ⟨a, rfl⟩

theorem isUp_mono {x y : Lift A} (h : x ⊑ y) (hx : isUp x) : isUp y := by
  obtain ⟨a, rfl⟩ := exists_of_isUp hx
  obtain ⟨b, rfl, _⟩ := up_le h
  trivial

theorem isUp_sup (c : Chain (Lift A)) (h : ∀ n, isUp (c n)) : isUp (OmegaSup.sup c) := by
  obtain ⟨a, ha⟩ := exists_of_isUp (h 0)
  show isUp (sup c)
  rw [sup_pos c ⟨0, a, ha⟩]; trivial

theorem isUp_eventually (c : Chain (Lift A)) (h : isUp (OmegaSup.sup c)) : ∃ n, isUp (c n) := by
  refine Classical.byContradiction fun hn => ?_
  have hb : ¬ HasUp c := fun ⟨n, a, ha⟩ => hn ⟨n, by rw [ha]; trivial⟩
  have : OmegaSup.sup c = bot := sup_neg c hb
  rw [this] at h
  exact h

/-- A chain of `A`, mapped by `up`. -/
def upChain (c : Dom.Chain A) : Chain (Lift A) := ⟨fun n => up (c n), fun n => up_mono (Dom.step c n)⟩

open Classical in
/-- The supremum of a chain of `up`s is `up` of the supremum. -/
theorem sup_upChain (c : Dom.Chain A) : OmegaSup.sup (upChain c) = up (Dom.sup c) := by
  have h : HasUp (upChain c) := ⟨0, c 0, rfl⟩
  show sup _ = _
  rw [sup_pos _ h]
  congr 1
  have hs : ∀ n, tail (upChain c) _ _ (choose_spec (choose_spec h)) n = c (choose h + n) := fun n =>
    (up.inj (tail_spec (upChain c) _ _ (choose_spec (choose_spec h)) n)).symm
  apply Dom.le_antisymm
  · apply Dom.sup_le; intro n; rw [hs n]; exact Dom.le_sup c _
  · apply Dom.sup_le; intro n
    exact Dom.le_trans (Dom.chain_le c (Nat.le_add_left n _)) (by rw [← hs n]; exact Dom.le_sup _ n)

end Lift
end
end NonPos
