import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith

/-
TODO:
- we want an easier to use cases:
  - keeps in the goal an equation of the shape: `t = case`
  - if called on Prop terms, uses Classical.em
  Actually, the cases from mathlib seems already quite powerful
  (https://leanprover-community.github.io/mathlib_docs/tactics.html#cases)
  For instance: cases h : e
  Also: cases_matching
- better split tactic
- we need conversions to operate on the head of applications.
  Actually, something like this works:
  ```
  conv at Hl =>
    apply congr_fun
    simp [fix_fuel_P]
  ```
  Maybe we need a rpt ... ; focus?
- simplifier/rewriter have a strange behavior sometimes
-/

namespace Diverge

namespace Primitives
/-! # Copy-pasting from Primitives to make the file self-contained -/

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ret (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

open Result

def bind (x: Result α) (f: α -> Result β) : Result β :=
  match x with
  | ret v  => f v 
  | fail v => fail v
  | div => div

@[simp] theorem bind_ret (x : α) (f : α → Result β) : bind (.ret x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using return x in do-blocks
instance : Pure Result where
  pure := fun x => ret x

@[simp] theorem bind_tc_ret (x : α) (f : α → Result β) :
  (do let y ← .ret x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, bind]

def div? {α: Type} (r: Result α): Bool :=
  match r with
  | div => true
  | ret _ | fail _ => false

end Primitives

namespace Fix

  open Primitives
  open Result

  variable {a b c d : Type}

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

  /-! # The validity property -/

  -- Monotonicity relation over results
  -- TODO: generalize (we should parameterize the definition by a relation over `a`)
  def result_rel {a : Type u} (x1 x2 : Result a) : Prop :=
    match x1 with
    | div => True
    | fail _ => x2 = x1
    | ret _ => x2 = x1 -- TODO: generalize

  -- Monotonicity relation over monadic arrows (i.e., Kleisli arrows)
  def karrow_rel (k1 k2 : a → Result b) : Prop :=
    ∀ x, result_rel (k1 x) (k2 x)

  -- Monotonicity property for function bodies
  def is_mono (f : (a → Result b) → a → Result b) : Prop :=
    ∀ {{k1 k2}}, karrow_rel k1 k2 → karrow_rel (f k1) (f k2)

  -- "Continuity" property.
  -- We need this, and this looks a lot like continuity. Also see this paper:
  -- https://inria.hal.science/file/index/docid/216187/filename/tarski.pdf
  -- We define our "continuity" criteria so that it gives us what we need to
  -- prove the fixed-point equation, and we can also easily manipulate it.
  def is_cont (f : (a → Result b) → a → Result b) : Prop :=
    ∀ x, (Hdiv : ∀ n, fix_fuel (.succ n) f x = div) → f (fix f) x = div

  /-! # The proof of the fixed-point equation -/
  theorem fix_fuel_mono {f : (a → Result b) → a → Result b} (Hmono : is_mono f) :
    ∀ {{n m}}, n ≤ m → karrow_rel (fix_fuel n f) (fix_fuel m f) := by
    intros n
    induction n
    case zero => simp [karrow_rel, fix_fuel, result_rel]
    case succ n1 Hi =>
      intros m Hle x
      simp [result_rel]
      match m with
      | 0 =>
        exfalso
        zify at *
        linarith
      | Nat.succ m1 =>
        simp_arith at Hle
        simp [fix_fuel]
        have Hi := Hi Hle
        have Hmono := Hmono Hi x
        simp [result_rel] at Hmono
        apply Hmono

  @[simp] theorem neg_fix_fuel_P {f : (a → Result b) → a → Result b} {x : a} {n : Nat} :
    ¬ fix_fuel_P f x n ↔ (fix_fuel n f x = div) := by
    simp [fix_fuel_P, div?]
    cases fix_fuel n f x <;> simp  

  theorem fix_fuel_fix_mono {f : (a → Result b) → a → Result b} (Hmono : is_mono f) :
    ∀ n, karrow_rel (fix_fuel n f) (fix f) := by
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
          conv => lhs; apply congr_fun; apply congr_fun; apply congr_fun; simp [fix_fuel_P, div?]
          cases fix_fuel (least (fix_fuel_P f x)) f x <;> simp
        have Hmono := fix_fuel_mono Hmono Hineq x
        simp [result_rel] at Hmono
        simp [fix] at *
        cases Heq: fix_fuel (least (fix_fuel_P f x)) f x <;>
        cases Heq':fix_fuel n f x <;>
        simp_all

  theorem fix_fuel_P_least {f : (a → Result b) → a → Result b} (Hmono : is_mono f) :
    ∀ {{x n}}, fix_fuel_P f x n → fix_fuel_P f x (least (fix_fuel_P f x)) := by
    intros x n Hf
    have Hfmono := fix_fuel_fix_mono Hmono n x
    -- TODO: there is no conversion to select the head of a function!
    conv => apply congr_fun; simp [fix_fuel_P]
    simp [fix_fuel_P] at Hf
    revert Hf Hfmono
    simp [div?, result_rel, fix]
    cases fix_fuel n f x <;> simp_all

  -- Prove the fixed point equation in the case there exists some fuel for which
  -- the execution terminates
  theorem fix_fixed_eq_terminates (f : (a → Result b) → a → Result b) (Hmono : is_mono f)
    (x : a) (n : Nat) (He : fix_fuel_P f x n) :
    fix f x = f (fix f) x := by
    have Hl := fix_fuel_P_least Hmono He
    -- TODO: better control of simplification
    conv at Hl =>
      apply congr_fun
      simp [fix_fuel_P]
    -- The least upper bound is > 0
    have ⟨ n, Hsucc ⟩ : ∃ n, least (fix_fuel_P f x) = Nat.succ n := by
      revert Hl
      simp [div?]
      cases least (fix_fuel_P f x) <;> simp [fix_fuel]
    simp [Hsucc] at Hl
    revert Hl
    simp [*, div?, fix, fix_fuel]
    -- Use the monotonicity
    have Hfixmono := fix_fuel_fix_mono Hmono n
    have Hvm := Hmono Hfixmono x
    -- Use functional extensionality
    simp [result_rel, fix] at Hvm
    revert Hvm
    split <;> simp [*] <;> intros <;> simp [*]

  theorem fix_fixed_eq_forall {{f : (a → Result b) → a → Result b}}
    (Hmono : is_mono f) (Hcont : is_cont f) :
    ∀ x, fix f x = f (fix f) x := by
    intros x
    -- Case disjunction: is there a fuel such that the execution successfully execute?
    match Classical.em (∃ n, fix_fuel_P f x n) with
    | .inr He =>
      -- No fuel: the fixed point evaluates to `div`
      --simp [fix] at *
      simp at *
      conv => lhs; simp [fix]
      have Hel := He (Nat.succ (least (fix_fuel_P f x))); simp [*, fix_fuel] at *; clear Hel
      -- Use the "continuity" of `f`
      have He : ∀ n, fix_fuel (.succ n) f x = div := by intros; simp [*]
      have Hcont := Hcont x He
      simp [Hcont]
    | .inl ⟨ n, He ⟩ => apply fix_fixed_eq_terminates f Hmono x n He

  -- The final fixed point equation
  theorem fix_fixed_eq {{f : (a → Result b) → a → Result b}}
    (Hmono : is_mono f) (Hcont : is_cont f) :
    fix f = f (fix f) := by
    have Heq := fix_fixed_eq_forall Hmono Hcont
    have Heq1 : fix f = (λ x => fix f x) := by simp
    rw [Heq1]
    conv => lhs; ext; simp [Heq]

  /-! # Making the proofs of validity manageable (and automatable) -/

  -- Monotonicity property for expressions
  def is_mono_p (e : (a → Result b) → Result c) : Prop :=
    ∀ {{k1 k2}}, karrow_rel k1 k2 → result_rel (e k1) (e k2)

  theorem is_mono_p_same (x : Result c) :
    @is_mono_p a b c (λ _ => x) := by
    simp [is_mono_p, karrow_rel, result_rel]
    split <;> simp

  theorem is_mono_p_rec (x : a) :
    @is_mono_p a b b (λ f => f x) := by
    simp_all [is_mono_p, karrow_rel, result_rel]

  -- The important lemma about `is_mono_p`
  theorem is_mono_p_bind
    (g : (a → Result b) → Result c)
    (h : c → (a → Result b) → Result d) :
    is_mono_p g →
    (∀ y, is_mono_p (h y)) →
    is_mono_p (λ k => do let y ← g k; h y k) := by
    intro hg hh
    simp [is_mono_p]
    intro fg fh Hrgh
    simp [karrow_rel, result_rel]
    have hg := hg Hrgh; simp [result_rel] at hg
    cases heq0: g fg <;> simp_all
    rename_i y _
    have hh := hh y Hrgh; simp [result_rel] at hh
    simp_all

  -- Continuity property for expressions - note that we take the continuation
  -- as parameter
  def is_cont_p (k : (a → Result b) → a → Result b)
    (e : (a → Result b) → Result c) : Prop :=
    (Hc : ∀ n, e (fix_fuel n k) = .div) →
    e (fix k) = .div

  theorem is_cont_p_same (k : (a → Result b) → a → Result b) (x : Result c) :
    is_cont_p k (λ _ => x) := by
    simp [is_cont_p]

  theorem is_cont_p_rec (f : (a → Result b) → a → Result b) (x : a) :
    is_cont_p f (λ f => f x) := by
    simp_all [is_cont_p, fix]

  -- The important lemma about `is_cont_p`
  theorem is_cont_p_bind
    (k : (a → Result b) → a → Result b)
    (Hkmono : is_mono k)
    (g : (a → Result b) → Result c)
    (h : c → (a → Result b) → Result d) :
    is_mono_p g →
    is_cont_p k g →
    (∀ y, is_mono_p (h y)) →
    (∀ y, is_cont_p k (h y)) →
    is_cont_p k (λ k => do let y ← g k; h y k) := by
    intro Hgmono Hgcont Hhmono Hhcont
    simp [is_cont_p]
    intro Hdiv
    -- Case on `g (fix... k)`: is there an n s.t. it terminates?
    cases Classical.em (∀ n, g (fix_fuel n k) = .div) <;> rename_i Hn
    . -- Case 1: g diverges
      have Hgcont := Hgcont Hn
      simp_all
    . -- Case 2: g doesn't diverge
      simp at Hn
      let ⟨ n, Hn ⟩ := Hn
      have Hdivn := Hdiv n
      have Hffmono := fix_fuel_fix_mono Hkmono n
      have Hgeq := Hgmono Hffmono
      simp [result_rel] at Hgeq
      cases Heq: g (fix_fuel n k) <;> rename_i y <;> simp_all
      -- Remains the .ret case
      -- Use Hdiv to prove that: ∀ n, h y (fix_fuel n f) = div
      -- We do this in two steps: first we prove it for m ≥ n
      have Hhdiv: ∀ m, h y (fix_fuel m k) = .div := by
        have Hhdiv : ∀ m, n ≤ m → h y (fix_fuel m k) = .div := by
          -- We use the fact that `g (fix_fuel n f) = .div`, combined with Hdiv
          intro m Hle
          have Hdivm := Hdiv m
          -- Monotonicity of g
          have Hffmono := fix_fuel_mono Hkmono Hle
          have Hgmono := Hgmono Hffmono
          -- We need to clear Hdiv because otherwise simp_all rewrites Hdivm with Hdiv
          clear Hdiv
          simp_all [result_rel]
        intro m
        -- TODO: we shouldn't need the excluded middle here because it is decidable
        cases Classical.em (n ≤ m) <;> rename_i Hl
        . apply Hhdiv; assumption
        . simp at Hl
          -- Make a case disjunction on `h y (fix_fuel m k)`: if it is not equal
          -- to div, use the monotonicity of `h y`
          have Hle : m ≤ n := by linarith
          have Hffmono := fix_fuel_mono Hkmono Hle
          have Hmono := Hhmono y Hffmono
          simp [result_rel] at Hmono
          cases Heq: h y (fix_fuel m k) <;> simp_all
      -- We can now use the continuity hypothesis for h
      apply Hhcont; assumption

  -- The validity property for an expression
  def is_valid_p (k : (a → Result b) → a → Result b)
    (e : (a → Result b) → Result c) : Prop :=
    is_mono_p e ∧
    (is_mono k → is_cont_p k e)

  @[simp] theorem is_valid_p_same (k : (a → Result b) → a → Result b) (x : Result c) :
    is_valid_p k (λ _ => x) := by
    simp [is_valid_p, is_mono_p_same, is_cont_p_same]

  @[simp] theorem is_valid_p_rec (k : (a → Result b) → a → Result b) (x : a) :
    is_valid_p k (λ k => k x) := by
    simp_all [is_valid_p, is_mono_p_rec, is_cont_p_rec]

  -- Lean is good at unification: we can write a very general version
  -- (in particular, it will manage to figure out `g` and `h` when we
  -- apply the lemma)
  theorem is_valid_p_bind
    {{k : (a → Result b) → a → Result b}}
    {{g : (a → Result b) → Result c}}
    {{h : c → (a → Result b) → Result d}}
    (Hgvalid : is_valid_p k g)
    (Hhvalid : ∀ y, is_valid_p k (h y)) :
    is_valid_p k (λ k => do let y ← g k; h y k) := by
    let ⟨ Hgmono, Hgcont ⟩ := Hgvalid
    simp [is_valid_p, forall_and] at Hhvalid
    have ⟨ Hhmono, Hhcont ⟩ := Hhvalid
    simp [← imp_forall_iff] at Hhcont
    simp [is_valid_p]; constructor
    . -- Monotonicity
      apply is_mono_p_bind <;> assumption
    . -- Continuity
      intro Hkmono
      have Hgcont := Hgcont Hkmono
      have Hhcont := Hhcont Hkmono
      apply is_cont_p_bind <;> assumption

  theorem is_valid_p_imp_is_valid {{e : (a → Result b) → a → Result b}}
    (Hvalid : ∀ k x, is_valid_p k (λ k => e k x)) :
    is_mono e ∧ is_cont e := by
    have Hmono : is_mono e := by
      intro f h Hr x
      have Hmono := Hvalid (λ _ _ => .div) x
      have Hmono := Hmono.left
      apply Hmono; assumption
    have Hcont : is_cont e := by
      intro x Hdiv
      have Hcont := (Hvalid e x).right Hmono
      simp [is_cont_p] at Hcont
      apply Hcont
      intro n
      have Hdiv := Hdiv n
      simp [fix_fuel] at Hdiv
      simp [*]
    simp [*]

  theorem is_valid_p_fix_fixed_eq {{e : (a → Result b) → a → Result b}}
    (Hvalid : ∀ k x, is_valid_p k (λ k => e k x)) :
    fix e = e (fix e) := by
    have ⟨ Hmono, Hcont ⟩ := is_valid_p_imp_is_valid Hvalid
    exact fix_fixed_eq Hmono Hcont

end Fix

namespace Ex1
  /- An example of use of the fixed-point -/
  open Primitives Fix

  variable {a : Type} (k : (List a × Int) → Result a)

  def list_nth_body (x : (List a × Int)) : Result a :=
    let (ls, i) := x
    match ls with
    | [] => .fail .panic
    | hd :: tl =>
      if i = 0 then .ret hd
      else k (tl, i - 1)

  theorem list_nth_body_is_valid: ∀ k x, is_valid_p k (λ k => @list_nth_body a k x) := by
    intro k x
    simp [list_nth_body]
    split <;> simp
    split <;> simp

  noncomputable
  def list_nth (ls : List a) (i : Int) : Result a := fix list_nth_body (ls, i)

  -- The unfolding equation - diverges if `i < 0`
  theorem list_nth_eq (ls : List a) (i : Int) :
    list_nth ls i =
      match ls with
      | [] => .fail .panic
      | hd :: tl =>
        if i = 0 then .ret hd
        else list_nth tl (i - 1)
    := by
    have Heq := is_valid_p_fix_fixed_eq (@list_nth_body_is_valid a)
    simp [list_nth]
    conv => lhs; rw [Heq]

end Ex1

namespace Ex2
  /- Same as Ex1, but we make the body of nth non tail-rec (this is mostly
     to see what happens when there are let-bindings) -/
  open Primitives Fix

  variable {a : Type} (k : (List a × Int) → Result a)

  def list_nth_body (x : (List a × Int)) : Result a :=
    let (ls, i) := x
    match ls with
    | [] => .fail .panic
    | hd :: tl =>
      if i = 0 then .ret hd
      else
        do
          let y ← k (tl, i - 1)
          .ret y

  theorem list_nth_body_is_valid: ∀ k x, is_valid_p k (λ k => @list_nth_body a k x) := by
    intro k x
    simp [list_nth_body]
    split <;> simp
    split <;> simp
    apply is_valid_p_bind <;> intros <;> simp_all

  noncomputable
  def list_nth (ls : List a) (i : Int) : Result a := fix list_nth_body (ls, i)

  -- The unfolding equation - diverges if `i < 0`
  theorem list_nth_eq (ls : List a) (i : Int) :
    (list_nth ls i =
       match ls with
       | [] => .fail .panic
       | hd :: tl =>
         if i = 0 then .ret hd
         else
           do
             let y ← list_nth tl (i - 1)
             .ret y)
    := by
    have Heq := is_valid_p_fix_fixed_eq (@list_nth_body_is_valid a)
    simp [list_nth]
    conv => lhs; rw [Heq]

end Ex2

namespace Ex3
  /- Mutually recursive functions -/
  open Primitives Fix

  /- Because we have mutually recursive functions, we use a sum for the inputs
     and the output types:
     - inputs: the sum allows to select the function to call in the recursive
       calls (and the functions may not have the same input types)
     - outputs: this case is degenerate because `even` and `odd` have the same
       return type `Bool`, but generally speaking we need a sum type because
       the functions in the mutually recursive group may have different
       return types.
   -/
  variable (k : (Int ⊕ Int) → Result (Bool ⊕ Bool))

  def is_even_is_odd_body (x : (Int ⊕ Int)) : Result (Bool ⊕ Bool) :=
    match x with
    | .inl i =>
      -- Body of `is_even`
      if i = 0
      then .ret (.inl true) -- We use .inl because this is `is_even`
      else
        do
          let b ←
            do
              -- Call `odd`: we need to wrap the input value in `.inr`, then
              -- extract the output value
              let r ← k (.inr (i- 1))
              match r with
              | .inl _ => .fail .panic -- Invalid output
              | .inr b => .ret b
          -- Wrap the return value
          .ret (.inl b)
    | .inr i =>
      -- Body of `is_odd`
      if i = 0
      then .ret (.inr false) -- We use .inr because this is `is_odd`
      else
        do
          let b ←
            do
              -- Call `is_even`: we need to wrap the input value in .inr, then
              -- extract the output value
              let r ← k (.inl (i- 1))
              match r with
              | .inl b => .ret b
              | .inr _ => .fail .panic -- Invalid output
          -- Wrap the return value
          .ret (.inr b)

  theorem is_even_is_odd_body_is_valid:
    ∀ k x, is_valid_p k (λ k => is_even_is_odd_body k x) := by
    intro k x
    simp [is_even_is_odd_body]
    split <;> simp <;> split <;> simp
    apply is_valid_p_bind; simp
    intros; split <;> simp
    apply is_valid_p_bind; simp
    intros; split <;> simp

  noncomputable
  def is_even (i : Int): Result Bool :=
    do
      let r ← fix is_even_is_odd_body (.inl i)
      match r with
      | .inl b => .ret b
      | .inr _ => .fail .panic

  noncomputable
  def is_odd (i : Int): Result Bool :=
    do
      let r ← fix is_even_is_odd_body (.inr i)
      match r with
      | .inl _ => .fail .panic
      | .inr b => .ret b

  -- TODO: move
  -- TODO: this is not enough
  theorem swap_if_bind {a b : Type} (e : Prop) [Decidable e]
    (x y : Result a) (f : a → Result b) :
    (do
      let z ← (if e then x else y)
      f z)
     =
    (if e then do let z ← x; f z
     else do let z ← y; f z) := by
    split <;> simp

  -- The unfolding equation for `is_even` - diverges if `i < 0`
  theorem is_even_eq (i : Int) :
    is_even i = (if i = 0 then .ret true else is_odd (i - 1))
    := by
    have Heq := is_valid_p_fix_fixed_eq is_even_is_odd_body_is_valid
    simp [is_even, is_odd]
    conv => lhs; rw [Heq]; simp; rw [is_even_is_odd_body]; simp
    -- Very annoying: we need to swap the matches
    -- Doing this with rewriting lemmas is hard generally speaking
    -- (especially as we may have to generate lemmas for user-defined
    -- inductives on the fly).
    -- The simplest is to repeatedly split then simplify (we identify
    -- the outer match or monadic let-binding, and split on its scrutinee)
    split <;> simp
    cases H0 : fix is_even_is_odd_body (Sum.inr (i - 1)) <;> simp
    rename_i v
    split <;> simp

  -- The unfolding equation for `is_odd` - diverges if `i < 0`
  theorem is_odd_eq (i : Int) :
    is_odd i = (if i = 0 then .ret false else is_even (i - 1))
    := by
    have Heq := is_valid_p_fix_fixed_eq is_even_is_odd_body_is_valid
    simp [is_even, is_odd]
    conv => lhs; rw [Heq]; simp; rw [is_even_is_odd_body]; simp
    -- Same remark as for `even`
    split <;> simp
    cases H0 : fix is_even_is_odd_body (Sum.inl (i - 1)) <;> simp
    rename_i v
    split <;> simp

end Ex3

namespace Ex4
  /- Higher-order example -/
  open Primitives Fix

  variable {a b : Type}

  /- An auxiliary function, which doesn't require the fixed-point -/
  def map (f : a → Result b) (ls : List a) : Result (List b) :=
    match ls with
    | [] => .ret []
    | hd :: tl =>
      do
        let hd ← f hd
        let tl ← map f tl
        .ret (hd :: tl)

  /- The validity theorem for `map`, generic in `f` -/
  theorem map_is_valid
    {{f : (a → Result b) → a → Result c}}
    (Hfvalid : ∀ k x, is_valid_p k (λ k => f k x))
    (k : (a → Result b) → a → Result b)
    (ls : List a) :
    is_valid_p k (λ k => map (f k) ls) := by
    induction ls <;> simp [map]
    apply is_valid_p_bind <;> simp_all
    intros
    apply is_valid_p_bind <;> simp_all

  /- An example which uses map -/
  inductive Tree (a : Type) :=
  | leaf (x : a)
  | node (tl : List (Tree a))

  def id_body (f : Tree a → Result (Tree a)) (t : Tree a) : Result (Tree a) :=
    match t with
    | .leaf x => .ret (.leaf x)
    | .node tl =>
      do
        let tl ← map f tl
        .ret (.node tl)

  theorem id_body_is_valid :
    ∀ k x, is_valid_p k (λ k => @id_body a k x) := by
    intro k x
    simp [id_body]
    split <;> simp
    apply is_valid_p_bind <;> simp_all
    -- We have to show that `map k tl` is valid
    apply map_is_valid; simp

  noncomputable def id (t : Tree a) := fix id_body t

  -- The unfolding equation
  theorem id_eq (t : Tree a) :
    (id t =
       match t with
       | .leaf x => .ret (.leaf x)
       | .node tl =>
       do
         let tl ← map id tl
         .ret (.node tl))
    := by
    have Heq := is_valid_p_fix_fixed_eq (@id_body_is_valid a)
    simp [id]
    conv => lhs; rw [Heq]; simp; rw [id_body]

end Ex4

end Diverge
