import Lean
import Base.Primitives

namespace Diverge

open Primitives

section Fix

open Result

variable {a b : Type}

/-! # The least fixed point definition and its properties -/

def least_p (p : Nat → Prop) (n : Nat) : Prop := p n ∧ (∀ m, m < n → ¬ p m)
noncomputable def least (p : Nat → Prop) : Nat :=
  Classical.epsilon (least_p p)

-- Auxiliary theorem for [least_spec]: if there exists an `n` satisfying `p`,
-- there there exists a least `m` satisfying `p`.
theorem least_spec_aux (p : Nat → Prop) : ∀ (n : Nat), (hn : p n) → ∃ m, least_p p m := by
  apply Nat.strongRec'
  intros n hi hn
  -- Case disjunction on: is n the smallest n satisfying p?
  match Classical.em (∀ m, m < n → ¬ p m) with
  | .inl hlt =>
    -- Yes: trivial
    exists n
  | .inr hlt =>
    simp at *
    let ⟨ m, ⟨ hmlt, hm ⟩ ⟩ := hlt
    have hi := hi m hmlt hm
    apply hi

-- The specification of [least]: either `p` is never satisfied, or it is satisfied
-- by `least p` and no `n < least p` satisfies `p`.
theorem least_spec (p : Nat → Prop) : (∀ n, ¬ p n) ∨ (p (least p) ∧ ∀ n, n < least p → ¬ p n) := by
  -- Case disjunction on the existence of an `n` which satisfies `p`
  match Classical.em (∀ n, ¬ p n) with
  | .inl h =>
    -- There doesn't exist: trivial
    apply (Or.inl h)
  | .inr h =>
    -- There exists: we simply use `least_spec_aux` in combination with the property
    -- of the epsilon operator
    simp at *
    let ⟨ n, hn ⟩ := h
    apply Or.inr
    have hl := least_spec_aux p n hn
    have he := Classical.epsilon_spec hl
    apply he

/-! # The fixed point definitions -/

def fix_fuel (n : Nat) (f : (a → Result b) → a → Result b) (x : a) : Result b :=
  match n with
  | 0 => .div
  | n + 1 =>
    f (fix_fuel n f) x

@[simp] def fix_fuel_pred (f : (a → Result b) → a → Result b) (x : a) (n : Nat) :=
  not (div? (fix_fuel n f x))

def fix_fuel_P (f : (a → Result b) → a → Result b) (x : a) (n : Nat) : Prop :=
  fix_fuel_pred f x n

noncomputable def fix (f : (a → Result b) → a → Result b) (x : a) : Result b :=
  fix_fuel (least (fix_fuel_P f x)) f x

/-! # The proof of the fixed point equation -/

-- Monotonicity relation over results
-- TODO: generalize
def result_rel {a : Type u} (x1 x2 : Result a) : Prop :=
  match x1 with
  | div => True
  | fail _ => x2 = x1
  | ret _ => x2 = x1 -- TODO: generalize

-- Monotonicity relation over monadic arrows
-- TODO: generalize
def marrow_rel (f g : a → Result b) : Prop :=
  ∀ x, result_rel (f x) (g x)

-- Validity property for a body
def is_valid (f : (a → Result b) → a → Result b) : Prop :=
  ∀ {{g h}}, marrow_rel g h → marrow_rel (f g) (f h)

/-

 -/  

theorem fix_fuel_mono {f : (a → Result b) → a → Result b} (Hvalid : is_valid f) :
  ∀ {{n m}}, n ≤ m → marrow_rel (fix_fuel n f) (fix_fuel m f) := by
  intros n
  induction n
  case zero => simp [marrow_rel, fix_fuel, result_rel]
  case succ n1 Hi =>
    intros m Hle x
    simp [result_rel]
    match m with
    | 0 =>
      exfalso
      -- TODO: annoying to do those conversions by hand - try zify?
      have : n1 + 1 ≤ (0 : Int) := by simp [*] at *
      have : 0 ≤ n1 := by simp [*] at *
      linarith
    | Nat.succ m1 =>
      simp_arith at Hle
      simp [fix_fuel]
      have Hi := Hi Hle
      simp [is_valid] at Hvalid
      have Hvalid := Hvalid Hi x
      simp [result_rel] at Hvalid
      apply Hvalid

@[simp] theorem neg_fix_fuel_P {f : (a → Result b) → a → Result b} {x : a} {n : Nat} :
  ¬ fix_fuel_P f x n ↔ (fix_fuel n f x = div) := by
  simp [fix_fuel_P, div?]
  cases fix_fuel n f x <;> simp  

theorem fix_fuel_fix_mono {f : (a → Result b) → a → Result b} (Hvalid : is_valid f) :
  ∀ n, marrow_rel (fix_fuel n f) (fix f) := by
  intros n x
  simp [result_rel]
  have Hl := least_spec (fix_fuel_P f x)
  simp at Hl
  match Hl with
  | .inl Hl => simp [*]
  | .inr ⟨ Hl, Hn ⟩ =>
    match Classical.em (fix_fuel n f x = div) with
    | .inl Hd =>
      simp [*]
    | .inr Hd =>
      have Hineq : least (fix_fuel_P f x) ≤ n := by
        -- Proof by contradiction
        cases Classical.em (least (fix_fuel_P f x) ≤ n) <;> simp [*]
        simp at *
        rename_i Hineq
        have Hn := Hn n Hineq
        contradiction
      have Hfix : ¬ (fix f x = div) := by
        simp [fix]
        -- By property of the least upper bound
        revert Hd Hl
        -- TODO: there is no conversion to select the head of a function!
        have : fix_fuel_P f x (least (fix_fuel_P f x)) = fix_fuel_pred f x (least (fix_fuel_P f x)) :=
          by simp[fix_fuel_P]
        simp [this, div?]
        clear this
        cases fix_fuel (least (fix_fuel_P f x)) f x <;> simp
      have Hmono := fix_fuel_mono Hvalid Hineq x
      simp [result_rel] at Hmono
      -- TODO: there is no conversion to select the head of a function!
      revert Hmono Hfix Hd
      simp [fix]
      -- TODO: it would be good if cases actually introduces an equation: this
      -- way we wouldn't have to do all the book-keeping
      cases fix_fuel (least (fix_fuel_P f x)) f x <;> cases fix_fuel n f x <;>
      intros <;> simp [*] at *  

theorem fix_fuel_P_least {f : (a → Result b) → a → Result b} (Hvalid : is_valid f) :
  ∀ {{x n}}, fix_fuel_P f x n → fix_fuel_P f x (least (fix_fuel_P f x)) := by sorry

theorem fix_fixed_eq (f : (a → Result b) → a → Result b) (Hvalid : is_valid f) :
  ∀ x, fix f x = f (fix f) x := by
  intros x
  -- conv => lhs; simp [fix]
  -- Case disjunction: is there a fuel such that the execution successfully execute?
  match Classical.em (∃ n, fix_fuel_P f x n) with
  | .inr He =>
    -- No fuel: the fixed point evaluates to `div`
    --simp [fix] at *
    simp at *
    simp [fix]
    have He := He (Nat.succ (least (fix_fuel_P f x)))
    simp [*, fix_fuel] at *
    -- Use the monotonicity of `f`
    have Hmono := fix_fuel_fix_mono Hvalid (least (fix_fuel_P f x)) x
    simp [result_rel] at Hmono
    simp [*] at *
    -- TODO: we need a stronger validity predicate
    sorry
  | .inl ⟨ n, He ⟩ =>
    have Hl := fix_fuel_P_least Hvalid He
    -- TODO: better control of simplification
    have Heq : fix_fuel_P f x (least (fix_fuel_P f x)) = fix_fuel_pred f x (least (fix_fuel_P f x)) :=
      by simp [fix_fuel_P]
    simp [Heq] at Hl; clear Heq
    -- The least upper bound is > 0
    have ⟨ n, Hsucc ⟩ : ∃ n, least (fix_fuel_P f x) = Nat.succ n := by sorry
    simp [Hsucc] at Hl
    revert Hl
    simp [*, div?, fix, fix_fuel]
    -- Use the monotonicity
    have Hineq : n ≤ Nat.succ n := by sorry
    have Hmono := fix_fuel_fix_mono Hvalid n
    have Hv := Hvalid Hmono x
    -- Use functional extensionality
    simp [result_rel, fix] at Hv
    revert Hv
    split <;> simp [*] <;> intros <;> simp [*]

  
end Fix

end Diverge
