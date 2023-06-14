import Lean
import Base.Primitives

namespace Diverge

open Primitives

namespace Fix

open Result

variable {a b : Type}

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
-- TODO: Kleisli arrow
-- TODO: generalize
def marrow_rel (f g : a → Result b) : Prop :=
  ∀ x, result_rel (f x) (g x)

-- Monotonicity property
def is_mono (f : (a → Result b) → a → Result b) : Prop :=
  ∀ {{g h}}, marrow_rel g h → marrow_rel (f g) (f h)

-- "Continuity" property.
-- We need this, and this looks a lot like continuity. Also see this paper:
-- https://inria.hal.science/file/index/docid/216187/filename/tarski.pdf
def is_cont (f : (a → Result b) → a → Result b) : Prop :=
  ∀ x, (Hdiv : ∀ n, fix_fuel (.succ n) f x = div) → f (fix f) x = div

-- Validity property for a body
structure is_valid (f : (a → Result b) → a → Result b) :=
  intro::
  hmono : is_mono f
  hcont : is_cont f

/-

 -/  

theorem fix_fuel_mono {f : (a → Result b) → a → Result b} (Hmono : is_mono f) :
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
      have Hmono := fix_fuel_mono Hmono Hineq x
      simp [result_rel] at Hmono
      -- TODO: there is no conversion to select the head of a function!
      revert Hmono Hfix Hd
      simp [fix]
      -- TODO: it would be good if cases actually introduces an equation: this
      -- way we wouldn't have to do all the book-keeping
      cases fix_fuel (least (fix_fuel_P f x)) f x <;> cases fix_fuel n f x <;>
      intros <;> simp [*] at *  

theorem fix_fuel_P_least {f : (a → Result b) → a → Result b} (Hmono : is_mono f) :
  ∀ {{x n}}, fix_fuel_P f x n → fix_fuel_P f x (least (fix_fuel_P f x)) := by
  intros x n Hf
  have Hfmono := fix_fuel_fix_mono Hmono n x
  revert Hf Hfmono
  -- TODO: would be good to be able to unfold fix_fuel_P only on the left
  simp [fix_fuel_P, div?, result_rel, fix]
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

-- The final fixed point equation
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
    conv => lhs; simp [fix]
    have Hel := He (Nat.succ (least (fix_fuel_P f x))); simp [*, fix_fuel] at *; clear Hel
    -- Use the "continuity" of `f`
    have He : ∀ n, fix_fuel (.succ n) f x = div := by intros; simp [*]
    have Hcont := Hvalid.hcont x He
    simp [Hcont]
  | .inl ⟨ n, He ⟩ => apply fix_fixed_eq_terminates f Hvalid.hmono x n He
  
/-
(∀ n, fix_fuel n f x = div)

⊢ f (fun y => fix_fuel (least (fix_fuel_P f y)) f y) x = div

(? x. p x) ==> p (epsilon p)


P (nf : a -> option Nat) :=
  match nf x with
  | None => forall n, fix_fuel n f x = div
  | Some n => fix_fuel n f x <> div

TODO: theorem de Tarsky,
Gilles Dowek (Introduction à la théorie des langages de programmation)

fix_f is f s.t.: f x = f (fix f) x ∧ ! g. g x = g (fix g) x ==> f <= g

-/  

end Fix

namespace Ex1
  /- An example of use of the fixed-point -/
  open Fix

  variable {a : Type} (f : (List a × Int) → Result a)

  def list_nth_body (x : (List a × Int)) : Result a :=
    let (ls, i) := x
    match ls with
    | [] => .fail .panic
    | hd :: tl =>
      if i = 0 then .ret hd
      else f (tl, i - 1)

  theorem list_nth_body_mono : is_mono (@list_nth_body a) := by
    simp [is_mono]; intro g h Hr (ls, i); simp [result_rel, list_nth_body]
    cases ls <;> simp
    rename_i hd tl
    -- TODO: making a case disjunction over `i = 0` is annoying, we need a more
    -- general tactic for this
    cases (Classical.em (Eq i 0)) <;> simp [*] at *
    apply Hr

  theorem list_nth_body_cont : is_cont (@list_nth_body a) := by
    rw [is_cont]; intro (ls, i) Hdiv; simp [list_nth_body, fix_fuel] at *
    cases ls <;> simp at *
    -- TODO: automate this
    cases (Classical.em (Eq i 0)) <;> simp [*] at *
    -- Recursive call
    apply Hdiv

  noncomputable
  def list_nth (ls : List a) (i : Int) : Result a := fix list_nth_body (ls, i)

  theorem list_nth_eq (ls : List a) (i : Int) :
    list_nth ls i =
      match ls with
      | [] => .fail .panic
      | hd :: tl =>
        if i = 0 then .ret hd
        else list_nth tl (i - 1)
    := by
    have Hvalid : is_valid (@list_nth_body a) :=
      is_valid.intro list_nth_body_mono list_nth_body_cont
    have Heq := fix_fixed_eq (@list_nth_body a) Hvalid
    simp [Heq, list_nth]
    conv => lhs; rw [list_nth_body]
    simp [Heq]

end Ex1

namespace Ex2
  /- Higher-order example -/
  open Fix

  variable {a b : Type}

  /- An auxiliary function, which doesn't require the fixed-point -/
  def map (f : a → Result b) (ls : List a) : Result (List b) :=
    match ls with
    | [] => .ret []
    | hd :: tl =>
      do
        match f hd with
        | .ret hd =>
          match map f tl with
          | .ret tl =>
            .ret (hd :: tl)
          | r => r
        | .fail e => .fail e
        | .div => .div

  theorem map_is_mono {{f g : a → Result b}} (Hr : marrow_rel f g) :
    ∀ ls, result_rel (map f ls) (map g ls) := by
    intro ls; induction ls <;> simp [result_rel, map]
    case cons hd tl Hi =>
    have Hr1 := Hr hd; simp [result_rel] at Hr1
    -- TODO: reverting is annoying
    revert Hr1
    cases f hd <;> intro Hr1 <;> simp [*]
    -- ret case
    simp [result_rel] at Hi
    -- TODO: annoying
    revert Hi
    cases map f tl <;> intro Hi <;> simp [*]

  -- Auxiliary definition
  def map_fix_fuel (n0 n1 : Nat) (f : (a → Result b) → a → Result b) (ls : List a) : Result (List b) :=
    match ls with
    | [] => .ret []
    | hd :: tl =>
      do
        match fix_fuel n0 f hd with
        | .ret hd =>
          match map (fix_fuel n1 f) tl with
          | .ret tl =>
            .ret (hd :: tl)
          | r => r
        | .fail e => .fail e
        | .div => .div

  def exists_map_fix_fuel_not_div_imp {{f : (a → Result b) → a → Result b}} {{ls : List a}}
    (Hmono : is_mono f) :
    (∃ n0 n1, map_fix_fuel n0 n1 f ls ≠ .div) →
    ∃ n2, map (fix_fuel n2 f) ls ≠ .div := by
    intro ⟨ n0, n1, Hnd ⟩
    exists n0 + n1
    have Hineq0 : n0 ≤ n0 + n1 := by linarith
    have Hineq1 : n1 ≤ n0 + n1 := by linarith
    simp [map_fix_fuel] at Hnd
    -- TODO: I would like a rewrite_once tactic
    unfold map; simp
    --
    revert Hnd
    cases ls <;> simp
    rename_i hd tl
    -- Use the monotonicity of fix_fuel
    have Hfmono := fix_fuel_mono Hmono Hineq0 hd
    simp [result_rel] at Hfmono; revert Hfmono
    cases fix_fuel n0 f hd <;> intro <;> simp [*]
    -- Use the monotonicity of map
    have Hfmono := fix_fuel_mono Hmono Hineq1
    have Hmmono := map_is_mono Hfmono tl
    simp [result_rel] at Hmmono; revert Hmmono
    cases map (fix_fuel n1 f) tl <;> intro <;> simp [*]

  -- TODO: it is simpler to prove the contrapositive of is_cont than is_cont itself.
  -- The proof is still quite technical: think of a criteria whose proof is simpler
  -- to automate.
  theorem map_is_cont_contra_aux {{f : (a → Result b) → a → Result b}} (Hmono : is_mono f) :
    ∀ ls, map (fix f) ls ≠ .div →
    ∃ n0 n1, map_fix_fuel n0 n1 f ls ≠ .div
    := by
    intro ls; induction ls <;> simp [result_rel, map_fix_fuel, map]
    simp [fix]
    case cons hd tl Hi =>
    -- Instantiate the first n and do a case disjunction
    intro Hf; exists (least (fix_fuel_P f hd)); revert Hf
    cases fix_fuel (least (fix_fuel_P f hd)) f hd <;> simp
    -- Use the induction hyp
    have Hr := Classical.em (map (fix f) tl = .div)
    simp [fix] at *
    cases Hr <;> simp_all
    have Hj : ∃ n2, map (fix_fuel n2 f) tl ≠ .div := exists_map_fix_fuel_not_div_imp Hmono Hi
    revert Hj; intro ⟨ n2, Hj ⟩
    intro Hf; exists n2; revert Hf
    revert Hj; cases map (fix_fuel n2 f) tl <;> simp_all

  theorem map_is_cont_contra {{f : (a → Result b) → a → Result b}} (Hmono : is_mono f) :
    ∀ ls, map (fix f) ls ≠ .div →
    ∃ n, map (fix_fuel n f) ls ≠ .div
    := by
    intro ls Hf
    have Hc := map_is_cont_contra_aux Hmono ls Hf
    apply exists_map_fix_fuel_not_div_imp <;> assumption

  theorem map_is_cont {{f : (a → Result b) → a → Result b}} (Hmono : is_mono f) :
    ∀ ls, (Hc : ∀ n, map (fix_fuel n f) ls = .div) →
    map (fix f) ls = .div
    := by
    intro ls Hc
    -- TODO: is there a tactic for proofs by contraposition?
    apply Classical.byContradiction; intro Hndiv
    let ⟨ n, Hcc ⟩ := map_is_cont_contra Hmono ls Hndiv
    simp_all

  /- An example which uses map -/
  inductive Tree (a : Type) :=
  | leaf (x : a)
  | node (tl : List (Tree a))

  def id_body (f : Tree a → Result (Tree a)) (t : Tree a) : Result (Tree a) :=
    match t with
    | .leaf x => .ret (.leaf x)
    | .node tl =>
      match map f tl with
      | .div => .div
      | .fail e => .fail e
      | .ret tl => .ret (.node tl)

  theorem id_body_mono : is_mono (@id_body a) := by
    simp [is_mono]; intro g h Hr t; simp [result_rel, id_body]
    cases t <;> simp
    rename_i tl
    have Hmmono := map_is_mono Hr tl
    revert Hmmono; simp [result_rel]
    cases map g tl <;> simp_all

  theorem id_body_cont : is_cont (@id_body a) := by
    rw [is_cont]; intro t Hdiv
    simp [fix_fuel] at *
    -- TODO: weird things are happening with the rewriter and the simplifier here
    rw [id_body]
    simp [id_body] at Hdiv
    --
    cases t <;> simp at *
    rename_i tl
    -- TODO: automate this
    have Hmc := map_is_cont id_body_mono tl
    have Hdiv : ∀ (n : ℕ), map (fix_fuel n id_body) tl = Result.div := by
      intro n
      have Hdiv := Hdiv n; revert Hdiv
      cases map (fix_fuel n id_body) tl <;> simp_all
    have Hmc := Hmc Hdiv; revert Hmc
    cases map (fix id_body) tl <;> simp_all

  noncomputable def id (t : Tree a) := fix id_body t

  theorem id_eq (t : Tree a) :
    id t =
      match t with
      | .leaf x => .ret (.leaf x)
      | .node tl =>
        match map id tl with
        | .div => .div
        | .fail e => .fail e
        | .ret tl => .ret (.node tl)
    := by
    have Hvalid : is_valid (@id_body a) :=
      is_valid.intro id_body_mono id_body_cont
    have Heq := fix_fixed_eq (@id_body a) Hvalid
    conv => lhs; rw [id, Heq, id_body]

end Ex2

end Diverge
