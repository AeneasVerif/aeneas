module
public import Mathlib.Data.Nat.Basic
import all Init.Data.Nat.Power2.Basic
@[expose] public section

namespace Aeneas

/-! ## Powers of Two -/

@[simp, grind ←]
lemma one_isPowerOfTwo : Nat.isPowerOfTwo 1 := by decide

@[simp, grind ←]
lemma isPowerOfTwo_ge_one (n : Nat) : n.isPowerOfTwo → n ≥ 1 := by intro ⟨x, hx⟩; grind

grind_pattern isPowerOfTwo_ge_one => n.isPowerOfTwo

@[grind ←]
lemma pos_of_isPowerOfTwo {n : Nat} (h : n.isPowerOfTwo) : 0 < n :=
  Nat.pos_of_isPowerOfTwo h

@[grind ←]
lemma dvd_of_isPowerOfTwo_le {a b : Nat} (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo) (hle : a ≤ b) :
    a ∣ b := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  apply Nat.pow_dvd_pow
  rw [Nat.pow_le_pow_iff_right] at hle
  all_goals trivial

/-! ## Bounded Maximum (`natMax`) -/

def natMax : (n : Nat) → ((i : Nat) → i < n → Nat) → Nat → Nat
  | 0, _, init => init
  | n + 1, f, init => max (natMax n (λ i _ ↦ f i (by omega)) init) (f n (by omega))

@[simp] lemma init_le_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init, init ≤ natMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, _, init => Nat.le_trans (init_le_natMax n _ init) (Nat.le_max_left _ _)

grind_pattern init_le_natMax => natMax n f init

@[simp] lemma le_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init (i : Nat) (hi : i < n), f i hi ≤ natMax n f init
  | n + 1, f, init, i, hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact Nat.le_trans (le_natMax n (λ k _ ↦ f k (by omega)) init i hlt) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

grind_pattern le_natMax => natMax n f init, i < n

lemma lub_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init z (_ : init ≤ z) (_ : ∀ i, (hi : i < n) → f i hi ≤ z), natMax n f init ≤ z
  | 0, _, _, z, h1, _ => h1
  | n + 1, _, init, z, h1, h2 => by
    apply Nat.max_le.mpr
    constructor; apply lub_natMax
    all_goals grind

@[simp, grind .]
lemma natMax_isPowerOfTwo : ∀ n (f : (i : Nat) → i < n → Nat) init,
    init.isPowerOfTwo → (∀ i (hi : i < n), (f i hi).isPowerOfTwo) → (natMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    have := natMax_isPowerOfTwo n (λ i _ ↦ f i (by omega)) init h0 (by grind)
    by_cases h : natMax n (λ i _ ↦ f i (by omega)) init ≤ f n (by omega)
    all_goals (simp [natMax]; grind)

/-! ## Alignment Rounding (`alignUp`) -/

def alignUp (x A : Nat) : Nat := ((x + A - 1) / A) * A

@[simp]
lemma le_alignUp (x : Nat) {A : Nat} (hA : 0 < A) : x ≤ alignUp x A := by
  have h := Nat.div_add_mod (x + A - 1) A
  rw [Nat.mul_comm] at h
  have := Nat.mod_lt (x + A - 1) hA
  dsimp [alignUp]
  omega
grind_pattern le_alignUp => alignUp x A

@[simp]
lemma aligned_alignUp (x : Nat) {A : Nat} : A ∣ alignUp x A := by
  apply Nat.dvd_mul_left
grind_pattern aligned_alignUp => alignUp x A

@[simp, grind =]
lemma alignUp_zero (A : Nat) : alignUp 0 A = 0 := by
  cases A <;> simp [alignUp, Nat.div_eq_of_lt]

@[simp]
lemma alignUp_mono {x y : Nat} (hxy : x ≤ y) (A : Nat) : alignUp x A ≤ alignUp y A :=
  Nat.mul_le_mul_right A (Nat.div_le_div_right (by omega))

grind_pattern alignUp_mono => alignUp x A, alignUp y A

end Aeneas
