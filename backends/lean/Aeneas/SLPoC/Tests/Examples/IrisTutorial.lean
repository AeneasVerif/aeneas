import Aeneas.SLPoC.MutableData.Ptr

namespace Aeneas.SepLogic

open Aeneas.Std (Heap Result)


namespace IrisTutorial

def aand (P Q : IProp) : IProp :=
  iforall fun b : Bool => if b then P else Q

def aor (P Q : IProp) : IProp :=
  iexists fun b : Bool => if b then P else Q

infixr:36 " ∧ₐ " => aand
infixr:35 " ∨ₐ " => aor

namespace Basics

/- The intentionally failing connective-scope example was omitted; `or_elim` exposes the garbage that Iris discards implicitly. -/

def and_success (P Q : IProp) : IProp :=
  P ∧ₐ Q

theorem asm (P : IProp) : P ⊢ P := by
  iframe

theorem sep_comm (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

theorem modus_ponens (P Q : IProp) :
    emp ⊢ P -∗ (P -∗ Q) -∗ Q := by
  apply wand_intro
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

theorem sep_assoc_1 (P Q R : IProp) :
    P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R := by
  iframe

theorem sep_comm_v2 (P Q : IProp) : P ∗ Q ⊢ Q ∗ P :=
  sep_comm P Q

theorem wand_adj_1 (P Q R : IProp) :
    (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R := by
  irewrite (wand_cancel P (Q -∗ R))
  irewrite (wand_cancel Q R)
  iframe

theorem wand_adj (P Q R : IProp) :
    (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R) := by
  have hForward : (P -∗ Q -∗ R) ⊢ (P ∗ Q -∗ R) :=
    wand_intro (by
      irewrite (wand_cancel P (Q -∗ R))
      irewrite (wand_cancel Q R)
      iframe)
  have hBackward : (P ∗ Q -∗ R) ⊢ (P -∗ Q -∗ R) := by
    apply wand_intro
    apply wand_intro
    irewrite (wand_cancel (P ∗ Q) R)
    iframe
  exact ⟨hForward, hBackward⟩

theorem or_comm (P Q : IProp) : Q ∨ₐ P ⊢ P ∨ₐ Q := by
  unfold aor
  iintro_entail
  cases x
  · refine entails_exists_r true ?_
    simp
    iframe
  · refine entails_exists_r false ?_
    simp
    iframe

theorem or_elim (P Q R : IProp) :
    (P -∗ R) ∗ (Q -∗ R) ∗ (P ∨ₐ Q) ⊢ R := by
  unfold aor
  iintro_entail
  cases x
  · simp
    irewrite (wand_cancel Q R)
    iframe
  · simp
    irewrite (wand_cancel P R)
    iframe

theorem sep_or_distr (P Q R : IProp) :
    P ∗ (Q ∨ₐ R) ⊣⊢ (P ∗ Q) ∨ₐ (P ∗ R) := by
  have hForward : P ∗ (Q ∨ₐ R) ⊢ (P ∗ Q) ∨ₐ (P ∗ R) := by
    unfold aor
    iintro_entail
    cases x
    · refine entails_exists_r false ?_
      simp
      iframe
    · refine entails_exists_r true ?_
      simp
      iframe
  have hBackward : (P ∗ Q) ∨ₐ (P ∗ R) ⊢ P ∗ (Q ∨ₐ R) := by
    unfold aor
    iintro_entail
    cases x
    · refine entails_exists_r false ?_
      simp
      iframe
    · refine entails_exists_r true ?_
      simp
      iframe
  exact ⟨hForward, hBackward⟩

theorem sep_ex_distr {A : Sort _} (P : IProp) (Φ : A → IProp) :
    P ∗ iexists Φ ⊣⊢ iexists fun x => P ∗ Φ x := by
  have hForward : P ∗ iexists Φ ⊢ iexists fun x => P ∗ Φ x := by
    iframe
  have hBackward : iexists (fun x => P ∗ Φ x) ⊢ P ∗ iexists Φ := by
    iframe
  exact ⟨hForward, hBackward⟩

theorem sep_all_distr {A : Sort _} (P Q : A → IProp) :
    iforall P ∗ iforall Q ⊢ iforall fun x => P x ∗ Q x := by
  apply forall_intro
  intro x
  exact sep_mono (forall_specialize x) (forall_specialize x)

end Basics

namespace Pure

/- Nothing is omitted, and — the logic being affine, as Iris's is — nothing has
to be absorbed by an explicit affine top either: `abstr_not_pure` is stated
exactly as Iris states it. -/

theorem asm_pure (φ : Prop) : ⌜φ⌝ ⊢ ⌜φ⌝ := by
  iframe

theorem eq_5_5 : emp ⊢ ⌜5 = 5⌝ := by
  iframe

theorem eq_elm {A : Type} (P : A → IProp) (x y : A) :
    ⌜x = y⌝ ∗ P x ⊢ P y := by
  iintro_entail
  subst y
  iframe

theorem true_intro : emp ⊢ ⌜True⌝ := by
  iframe

theorem and_pure : emp ⊢ (⌜5 = 5⌝ ∧ₐ ⌜8 = 8⌝) := by
  unfold aand
  apply forall_intro
  intro b
  cases b <;> simp <;> iframe

theorem sep_pure : emp ⊢ ⌜5 = 5⌝ ∗ ⌜8 = 8⌝ := by
  iframe

theorem wand_pure {A : Type} (x y : A) :
    ⌜x = y⌝ ⊢ ⌜y = x⌝ := by
  iintro_entail
  subst y
  iframe

theorem abstr_not_pure (P : IProp) :
    P ⊢ ⌜8 = 8⌝ := by
  iframe

theorem pure_adj1 (φ : Prop) (hφ : φ) : emp ⊢ ⌜φ⌝ := by
  iframe

theorem pure_adj2 (P : IProp) :
    emp ⊢ ⌜emp ⊢ P⌝ -∗ P := by
  apply wand_intro
  iintro_entail
  exact h

end Pure

namespace Specifications

/- Atomicity, nondeterminism, parallelism, and the generic modal WP rule were not ported; names ending in `Sequential` are deterministic sequential variants, not implementations of the original concurrent operations. -/

def arith : Result Int :=
  pure (1 + 2 * 3 + 4 + 5)

@[step]
theorem arith_spec :
    (arith) ⦃⇓ v => v = 16⦄ := by
  unfold arith
  step*

def lambda : Result Int :=
  let add5 := fun x : Int => x + 5
  let double := fun x : Int => x * 2
  let compose := fun f g x => g (f x)
  pure (compose add5 double 5)

@[step]
theorem lambda_spec :
    (lambda) ⦃⇓ v => v = 20⦄ := by
  unfold lambda
  step*

def prog : Result Int := do
  let x ← alloc (1 : Int)
  let value ← read x
  update x (value + 2)
  read x

@[step]
theorem prog_spec :
    ⦃ emp ⦄ prog ⦃⇓ v => ⌜v = 3⌝⦄ := by
  unfold prog
  step*

theorem pt_not_dupl {α : Type} (p : Ptr α) (v v' : α) :
    p ↦ v ∗ p ↦ v' ⊢ ⌜False⌝ :=
  pointsTo_exclusive p v v'

def compareAndSetSequential (p : Ptr Int) (expected replacement : Int) :
    Result Bool := do
  let value ← read p
  if value = expected then
    update p replacement
    pure true
  else
    pure false

@[step]
theorem compareAndSetSequential_spec (p : Ptr Int)
    (value expected replacement : Int) :
    ⦃ p ↦ value ⦄ compareAndSetSequential p expected replacement
      ⦃⇓ success =>
        iprop(⌜success = decide (value = expected)⌝ ∗
          if value = expected then p ↦ replacement else p ↦ value)⦄ := by
  unfold compareAndSetSequential
  step*

def cmpXchg0To10Sequential (p : Ptr Int) : Result Bool :=
  compareAndSetSequential p 0 10

theorem cmpXchg_0_to_10_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ cmpXchg0To10Sequential p
      ⦃⇓ success =>
        iprop(⌜success = decide (value = 0)⌝ ∗
          if value = 0 then p ↦ 10 else p ↦ value)⦄ := by
  unfold cmpXchg0To10Sequential
  step*

def casSequential : Result (Option (Int × Int)) := do
  let p ← alloc (5 : Int)
  let first ← compareAndSetSequential p 6 7
  if first then
    pure none
  else
    let a ← read p
    let second ← compareAndSetSequential p 5 7
    if second then
      let b ← read p
      pure (some (a, b))
    else
      pure none

theorem cas_sequential_spec :
    ⦃ emp ⦄ casSequential ⦃⇓ result => ⌜result = some (5, 7)⌝⦄ := by
  unfold casSequential
  step*

def parClientSequential : Result (Ptr Int × Ptr Int × Int) := do
  let l₁ ← alloc (0 : Int)
  let l₂ ← alloc (0 : Int)
  update l₁ 21
  update l₂ 2
  let left ← read l₁
  let right ← read l₂
  pure (l₁, l₂, left * right)

theorem par_client_sequential_spec :
    ⦃ emp ⦄ parClientSequential
      ⦃⇓ result =>
        iprop(⌜result.2.2 = 42⌝ ∗
          result.1 ↦ 21 ∗ result.2.1 ↦ 2)⦄ := by
  unfold parClientSequential
  step*

def raceLeftThenRightSequential (p : Ptr Int) : Result Unit := do
  update p 1
  update p 2

theorem race_left_then_right_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ raceLeftThenRightSequential p
      ⦃⇓ p ↦ 2⦄ := by
  unfold raceLeftThenRightSequential
  step*

def raceRightThenLeftSequential (p : Ptr Int) : Result Unit := do
  update p 2
  update p 1

theorem race_right_then_left_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ raceRightThenLeftSequential p
      ⦃⇓ p ↦ 1⦄ := by
  unfold raceRightThenLeftSequential
  step*

def progAdd2 : Result Int := do
  let value ← prog
  pure (value + 2)

theorem prog_add_2_spec :
    ⦃ emp ⦄ progAdd2 ⦃⇓ v => ⌜v = 5⌝⦄ := by
  unfold progAdd2
  step*

theorem prog_add_2_spec' :
    ⦃ emp ⦄ progAdd2 ⦃⇓ v => ⌜v = 5⌝⦄ := by
  unfold progAdd2
  step*

theorem prog_add_2_spec'' :
    ⦃ emp ⦄ progAdd2 ⦃⇓ v => ⌜v = 5⌝⦄ :=
  prog_add_2_spec'

def swap (x y : Ptr α) : Result Unit := do
  let value ← read x
  let other ← read y
  update x other
  update y value

def swapTwice (x y : Ptr α) : Result Unit := do
  swap x y
  swap x y

@[step]
theorem swap_spec (x y : Ptr α) (value other : α) :
    ⦃ x ↦ value ∗ y ↦ other ⦄ swap x y
      ⦃⇓ x ↦ other ∗ y ↦ value⦄ := by
  unfold swap
  step*

theorem swap_swap_spec (x y : Ptr α) (value other : α) :
    ⦃ x ↦ value ∗ y ↦ other ⦄ swapTwice x y
      ⦃⇓ x ↦ value ∗ y ↦ other⦄ := by
  unfold swapTwice
  step*

end Specifications

namespace LinkedList

/- No sequential example was omitted; Iris persistence for callback specifications was replaced by Lean hypotheses. -/

structure Node (α : Type) where
  value : α
  next : Option (Ptr (Node α))

abbrev Link (α : Type) :=
  Option (Ptr (Node α))

def isList : Link α → List α → IProp
  | none, [] => emp
  | some p, x :: xs =>
      iexists fun next => iprop(p ↦ { value := x, next := next } ∗ isList next xs)
  | _, _ => ⌜False⌝

theorem isList_cons (p : Ptr (Node α)) (x : α) (next : Link α) (xs : List α) :
    p ↦ { value := x, next := next } ∗ isList next xs ⊢
      isList (some p) (x :: xs) := by
  change _ ⊢ iexists fun next' =>
    iprop(p ↦ { value := x, next := next' } ∗ isList next' xs)
  exact entails_exists_r next (entails_refl _)

def inc : List Int → Link Int → Result Unit
  | [], _ => pure ()
  | _ :: _, none => pure ()
  | _ :: xs, some p => do
      let node ← read p
      update p { node with value := node.value + 1 }
      inc xs node.next

@[step]
theorem inc_spec (l : Link Int) (xs : List Int) :
    ⦃ isList l xs ⦄ inc xs l
      ⦃⇓ isList l (xs.map fun x => x + 1)⦄ := by
  induction xs generalizing l with
  | nil =>
      cases l
      · simp only [isList, inc, List.map_nil]
        step*
      · simp only [isList]
        iintro
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          iintro
          contradiction
      | some p =>
          simp only [isList, inc, List.map_cons]
          iintro
          step*

def append : List α → Link α → Link α → Result (Link α)
  | [], _, l₂ => pure l₂
  | _ :: _, none, l₂ => pure l₂
  | _ :: xs, some p, l₂ => do
      let node ← read p
      let result ← append xs node.next l₂
      update p { node with next := result }
      pure (some p)

@[step]
theorem append_spec (l₁ l₂ : Link α) (xs ys : List α) :
    ⦃ isList l₁ xs ∗ isList l₂ ys ⦄ append xs l₁ l₂
      ⦃⇓ l => isList l (xs ++ ys)⦄ := by
  induction xs generalizing l₁ l₂ ys with
  | nil =>
      cases l₁
      · simp only [isList, append, List.nil_append]
        step*
      · simp only [isList]
        iintro
        contradiction
  | cons x xs ih =>
      cases l₁ with
      | none =>
          simp only [isList]
          iintro
          contradiction
      | some p =>
          simp only [isList, append, List.cons_append]
          iintro
          step*

def reverseAppend : List α → Link α → Link α → Result (Link α)
  | [], _, acc => pure acc
  | _ :: _, none, acc => pure acc
  | _ :: xs, some p, acc => do
      let node ← read p
      update p { node with next := acc }
      reverseAppend xs node.next (some p)

@[step]
theorem reverse_append_spec (l acc : Link α) (xs ys : List α) :
    ⦃ isList l xs ∗ isList acc ys ⦄ reverseAppend xs l acc
      ⦃⇓ result => isList result (xs.reverse ++ ys)⦄ := by
  induction xs generalizing l acc ys with
  | nil =>
      cases l
      · simp only [isList, reverseAppend, List.reverse_nil, List.nil_append]
        step*
      · simp only [isList]
        iintro
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          iintro
          contradiction
      | some p =>
          simp only [isList, reverseAppend, List.reverse_cons, List.append_assoc,
            List.singleton_append]
          iintro next
          step* 2
          step with ih (l := next) (acc := some p) (ys := x :: ys)
          iframe

def reverse (xs : List α) (l : Link α) : Result (Link α) :=
  reverseAppend xs l none

theorem reverse_spec (l : Link α) (xs : List α) :
    ⦃ isList l xs ⦄ reverse xs l
      ⦃⇓ result => isList result xs.reverse⦄ := by
  unfold reverse
  step with reverse_append_spec l none xs []
  iframe

def bigSep (P : α → IProp) : List α → IProp
  | [] => emp
  | x :: xs => iprop(P x ∗ bigSep P xs)

@[simp]
theorem bigSep_emp (xs : List α) :
    bigSep (fun _ : α => emp) xs = emp := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [bigSep, ih, sep_emp_l_eq]

def foldRight (f : α → β → Result β) : List α → Link α → β → Result β
  | [], _, acc => pure acc
  | _ :: _, none, acc => pure acc
  | _ :: xs, some p, acc => do
      let node ← read p
      let result ← foldRight f xs node.next acc
      f node.value result

@[step]
theorem fold_right_spec (P : α → IProp) (I : List α → β → IProp)
    (f : α → β → Result β) (acc : β) (l : Link α) (xs : List α)
    (hf : ∀ x acc' ys,
      ⦃ P x ∗ I ys acc' ⦄ f x acc'
        ⦃⇓ result => I (x :: ys) result⦄) :
    ⦃ isList l xs ∗ bigSep P xs ∗ I [] acc ⦄ foldRight f xs l acc
      ⦃⇓ result => isList l xs ∗ I xs result⦄ := by
  induction xs generalizing l acc with
  | nil =>
      cases l
      · simp only [isList, bigSep, foldRight]
        step*
      · simp only [isList]
        iintro
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          iintro
          contradiction
      | some p =>
          simp only [isList, bigSep, foldRight]
          iintro
          step*

def sumList (xs : List Int) (l : Link Int) : Result Int :=
  foldRight (fun x acc => pure (x + acc)) xs l 0

theorem sum_list_spec (l : Link Int) (xs : List Int) :
    ⦃ isList l xs ⦄ sumList xs l
      ⦃⇓ result =>
        iprop(⌜result = xs.foldr (· + ·) 0⌝ ∗ isList l xs)⦄ := by
  have hf : ∀ x acc ys,
      ⦃ emp ∗ ⌜acc = ys.foldr (· + ·) 0⌝ ⦄
        (pure (x + acc) : Result Int)
        ⦃⇓ result => ⌜result = (x :: ys).foldr (· + ·) 0⌝⦄ := by
    intro x acc ys
    step*
  unfold sumList
  apply triple_conseq
    (fold_right_spec (fun _ : Int => emp)
      (fun ys acc => ⌜acc = ys.foldr (· + ·) 0⌝)
      (fun x acc => pure (x + acc)) 0 l xs hf)
  · iframe
  · iframe

end LinkedList

end IrisTutorial

end Aeneas.SepLogic
