import Aeneas.SLPoC.Step

namespace Aeneas.SLPoC

open scoped SepLogic

namespace IrisTutorial

def aand (P Q : SLProp) : SLProp :=
  hforall fun b : Bool => if b then P else Q

def aor (P Q : SLProp) : SLProp :=
  hexists fun b : Bool => if b then P else Q

infixr:36 " ∧ₐ " => aand
infixr:35 " ∨ₐ " => aor

namespace Basics

/- The intentionally failing connective-scope example was omitted; `or_elim` exposes the garbage that Iris discards implicitly. -/

def and_success (P Q : SLProp) : SLProp :=
  P ∧ₐ Q

theorem asm (P : SLProp) : P ⊢ P := by
  sl_frame

theorem sep_comm (P Q : SLProp) : P ∗ Q ⊢ Q ∗ P := by
  sl_frame

theorem modus_ponens (P Q : SLProp) :
    emp ⊢ P -∗ (P -∗ Q) -∗ Q := by
  apply hwand_intro
  apply hwand_intro
  sl_xchange (hwand_cancel P Q)
  sl_frame

theorem sep_assoc_1 (P Q R : SLProp) :
    P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R := by
  sl_frame

theorem sep_comm_v2 (P Q : SLProp) : P ∗ Q ⊢ Q ∗ P :=
  sep_comm P Q

theorem wand_adj_1 (P Q R : SLProp) :
    (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R := by
  sl_xchange (hwand_cancel P (Q -∗ R))
  sl_xchange (hwand_cancel Q R)
  sl_frame

theorem wand_adj (P Q R : SLProp) :
    (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R) := by
  have hForward : (P -∗ Q -∗ R) ⊢ (P ∗ Q -∗ R) :=
    hwand_intro (by
      sl_xchange (hwand_cancel P (Q -∗ R))
      sl_xchange (hwand_cancel Q R)
      sl_frame)
  have hBackward : (P ∗ Q -∗ R) ⊢ (P -∗ Q -∗ R) := by
    apply hwand_intro
    apply hwand_intro
    sl_xchange (hwand_cancel (P ∗ Q) R)
    sl_frame
  intro h
  exact ⟨hForward h, hBackward h⟩

theorem or_comm (P Q : SLProp) : Q ∨ₐ P ⊢ P ∨ₐ Q := by
  unfold aor
  sl_xpull
  cases x
  · refine himpl_hexists_r true ?_
    simp
    sl_frame
  · refine himpl_hexists_r false ?_
    simp
    sl_frame

theorem or_elim (P Q R : SLProp) :
    (P -∗ R) ∗ (Q -∗ R) ∗ (P ∨ₐ Q) ⊢ R ∗ GC := by
  unfold aor
  sl_xpull
  cases x
  · simp
    sl_xchange (hwand_cancel Q R)
    sl_frame
  · simp
    sl_xchange (hwand_cancel P R)
    sl_frame

theorem sep_or_distr (P Q R : SLProp) :
    P ∗ (Q ∨ₐ R) ⊣⊢ (P ∗ Q) ∨ₐ (P ∗ R) := by
  have hForward : P ∗ (Q ∨ₐ R) ⊢ (P ∗ Q) ∨ₐ (P ∗ R) := by
    unfold aor
    sl_xpull
    cases x
    · refine himpl_hexists_r false ?_
      simp
      sl_frame
    · refine himpl_hexists_r true ?_
      simp
      sl_frame
  have hBackward : (P ∗ Q) ∨ₐ (P ∗ R) ⊢ P ∗ (Q ∨ₐ R) := by
    unfold aor
    sl_xpull
    cases x
    · refine himpl_hexists_r false ?_
      simp
      sl_frame
    · refine himpl_hexists_r true ?_
      simp
      sl_frame
  intro h
  exact ⟨hForward h, hBackward h⟩

theorem sep_ex_distr {A : Sort _} (P : SLProp) (Φ : A → SLProp) :
    P ∗ hexists Φ ⊣⊢ hexists fun x => P ∗ Φ x := by
  have hForward : P ∗ hexists Φ ⊢ hexists fun x => P ∗ Φ x := by
    sl_frame
  have hBackward : hexists (fun x => P ∗ Φ x) ⊢ P ∗ hexists Φ := by
    sl_frame
  intro h
  exact ⟨hForward h, hBackward h⟩

theorem sep_all_distr {A : Sort _} (P Q : A → SLProp) :
    hforall P ∗ hforall Q ⊢ hforall fun x => P x ∗ Q x := by
  apply hforall_intro
  intro x
  exact hstar_mono (hforall_specialize x) (hforall_specialize x)

end Basics

namespace Pure

/- Nothing was omitted; `abstr_not_pure` exposes the garbage that Iris discards implicitly. -/

theorem asm_pure (φ : Prop) : ⌜φ⌝ ⊢ ⌜φ⌝ := by
  sl_frame

theorem eq_5_5 : emp ⊢ ⌜5 = 5⌝ := by
  sl_frame

theorem eq_elm {A : Type} (P : A → SLProp) (x y : A) :
    ⌜x = y⌝ ∗ P x ⊢ P y := by
  sl_xpull
  subst y
  sl_frame

theorem true_intro : emp ⊢ GC := by
  sl_frame

theorem and_pure : emp ⊢ (⌜5 = 5⌝ ∧ₐ ⌜8 = 8⌝) := by
  unfold aand
  apply hforall_intro
  intro b
  cases b <;> simp <;> sl_frame

theorem sep_pure : emp ⊢ ⌜5 = 5⌝ ∗ ⌜8 = 8⌝ := by
  sl_frame

theorem wand_pure {A : Type} (x y : A) :
    ⌜x = y⌝ ⊢ ⌜y = x⌝ := by
  sl_xpull
  subst y
  sl_frame

theorem abstr_not_pure (P : SLProp) :
    P ⊢ ⌜8 = 8⌝ ∗ GC := by
  sl_frame

theorem pure_adj1 (φ : Prop) (hφ : φ) : emp ⊢ ⌜φ⌝ := by
  sl_frame

theorem pure_adj2 (P : SLProp) :
    emp ⊢ ⌜emp ⊢ P⌝ -∗ P := by
  apply hwand_intro
  sl_xpull
  exact h

end Pure

namespace Specifications

/- Atomicity, nondeterminism, parallelism, and the generic modal WP rule were not ported; names ending in `Sequential` are deterministic sequential variants, not implementations of the original concurrent operations. -/

def arith : St Int :=
  pure (1 + 2 * 3 + 4 + 5)

@[step]
theorem arith_spec :
    (arith) ⦃⇓ v => v = 16⦄ := by
  unfold arith
  sl_step*

def lambda : St Int :=
  let add5 := fun x : Int => x + 5
  let double := fun x : Int => x * 2
  let compose := fun f g x => g (f x)
  pure (compose add5 double 5)

@[step]
theorem lambda_spec :
    (lambda) ⦃⇓ v => v = 20⦄ := by
  unfold lambda
  sl_step*

def prog : St Int := do
  let x ← alloc (1 : Int)
  let value ← read x
  update x (value + 2)
  read x

@[step]
theorem prog_spec :
    (prog) ⦃⇓ v => v = 3⦄ := by
  unfold prog
  sl_step*

theorem pt_not_dupl {α : Type} (p : Ptr α) (v v' : α) :
    p ↦ v ∗ p ↦ v' ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hd, _, rfl, rfl⟩
  exfalso
  apply hd p
  · simp [Ptr.singleton, singleton]
    rfl
  · simp [Ptr.singleton, singleton]
    rfl

def compareAndSetSequential (p : Ptr Int) (expected replacement : Int) :
    St Bool := do
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
  sl_step
  by_cases h : value = expected
  · simp only [h, ↓reduceIte, decide_true]
    sl_step*
  · simp only [h, ↓reduceIte, decide_false]
    sl_step*

def cmpXchg0To10Sequential (p : Ptr Int) : St Bool :=
  compareAndSetSequential p 0 10

theorem cmpXchg_0_to_10_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ cmpXchg0To10Sequential p
      ⦃⇓ success =>
        iprop(⌜success = decide (value = 0)⌝ ∗
          if value = 0 then p ↦ 10 else p ↦ value)⦄ := by
  unfold cmpXchg0To10Sequential
  sl_step*

def casSequential : St (Option (Int × Int)) := do
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
    (casSequential) ⦃⇓ result => result = some (5, 7)⦄ := by
  unfold casSequential
  sl_step*

def parClientSequential : St (Ptr Int × Ptr Int × Int) := do
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
  sl_step* 6
  sl_pure
  sl_frame

def raceLeftThenRightSequential (p : Ptr Int) : St Unit := do
  update p 1
  update p 2

theorem race_left_then_right_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ raceLeftThenRightSequential p
      ⦃⇓ p ↦ 2⦄ := by
  unfold raceLeftThenRightSequential
  sl_step*

def raceRightThenLeftSequential (p : Ptr Int) : St Unit := do
  update p 2
  update p 1

theorem race_right_then_left_sequential_spec (p : Ptr Int) (value : Int) :
    ⦃ p ↦ value ⦄ raceRightThenLeftSequential p
      ⦃⇓ p ↦ 1⦄ := by
  unfold raceRightThenLeftSequential
  sl_step*

def progAdd2 : St Int := do
  let value ← prog
  pure (value + 2)

theorem prog_add_2_spec :
    (progAdd2) ⦃⇓ v => v = 5⦄ := by
  unfold progAdd2
  sl_step*

theorem prog_add_2_spec' :
    (progAdd2) ⦃⇓ v => v = 5⦄ := by
  unfold progAdd2
  sl_step with prog_spec
  sl_step*

theorem prog_add_2_spec'' :
    (progAdd2) ⦃⇓ v => v = 5⦄ :=
  prog_add_2_spec'

def swap (x y : Ptr α) : St Unit := do
  let value ← read x
  let other ← read y
  update x other
  update y value

def swapTwice (x y : Ptr α) : St Unit := do
  swap x y
  swap x y

@[step]
theorem swap_spec (x y : Ptr α) (value other : α) :
    ⦃ x ↦ value ∗ y ↦ other ⦄ swap x y
      ⦃⇓ x ↦ other ∗ y ↦ value⦄ := by
  unfold swap
  sl_step*

theorem swap_swap_spec (x y : Ptr α) (value other : α) :
    ⦃ x ↦ value ∗ y ↦ other ⦄ swapTwice x y
      ⦃⇓ x ↦ value ∗ y ↦ other⦄ := by
  unfold swapTwice
  sl_step*

end Specifications

namespace LinkedList

/- No sequential example was omitted; Iris persistence for callback specifications was replaced by Lean hypotheses. -/

structure Node (α : Type) where
  value : α
  next : Option (Ptr (Node α))

abbrev Link (α : Type) :=
  Option (Ptr (Node α))

def isList : Link α → List α → SLProp
  | none, [] => emp
  | some p, x :: xs =>
      hexists fun next => iprop(p ↦ { value := x, next := next } ∗ isList next xs)
  | _, _ => ⌜False⌝

theorem isList_cons (p : Ptr (Node α)) (x : α) (next : Link α) (xs : List α) :
    p ↦ { value := x, next := next } ∗ isList next xs ⊢
      isList (some p) (x :: xs) := by
  change _ ⊢ hexists fun next' =>
    iprop(p ↦ { value := x, next := next' } ∗ isList next' xs)
  exact himpl_hexists_r next (himpl_refl _)

def inc : List Int → Link Int → St Unit
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
        sl_step*
      · simp only [isList]
        sl_pull
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          sl_pull
          contradiction
      | some p =>
          simp only [isList, inc, List.map_cons]
          sl_pull next
          sl_step
          sl_step
          sl_step with ih next

def append : List α → Link α → Link α → St (Link α)
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
        sl_pure
        sl_frame
      · simp only [isList]
        sl_pull
        contradiction
  | cons x xs ih =>
      cases l₁ with
      | none =>
          simp only [isList]
          sl_pull
          contradiction
      | some p =>
          simp only [isList, append, List.cons_append]
          sl_pull next
          sl_step
          sl_step with ih (l₁ := next) (l₂ := l₂) (ys := ys)
          sl_step
          sl_pure
          exact isList_cons p x result (xs ++ ys)

def reverseAppend : List α → Link α → Link α → St (Link α)
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
        sl_pure
        sl_frame
      · simp only [isList]
        sl_pull
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          sl_pull
          contradiction
      | some p =>
          simp only [isList, reverseAppend, List.reverse_cons, List.append_assoc,
            List.singleton_append]
          sl_pull next
          sl_step
          sl_step
          sl_step with ih (l := next) (acc := some p) (ys := x :: ys)

def reverse (xs : List α) (l : Link α) : St (Link α) :=
  reverseAppend xs l none

theorem reverse_spec (l : Link α) (xs : List α) :
    ⦃ isList l xs ⦄ reverse xs l
      ⦃⇓ result => isList result xs.reverse⦄ := by
  unfold reverse
  sl_step with reverse_append_spec l none xs []

def bigSep (P : α → SLProp) : List α → SLProp
  | [] => emp
  | x :: xs => iprop(P x ∗ bigSep P xs)

@[simp]
theorem bigSep_emp (xs : List α) :
    bigSep (fun _ : α => emp) xs = emp := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [bigSep, ih, hstar_hempty_l_eq]

def foldRight (f : α → β → St β) : List α → Link α → β → St β
  | [], _, acc => pure acc
  | _ :: _, none, acc => pure acc
  | _ :: xs, some p, acc => do
      let node ← read p
      let result ← foldRight f xs node.next acc
      f node.value result

@[step]
theorem fold_right_spec (P : α → SLProp) (I : List α → β → SLProp)
    (f : α → β → St β) (acc : β) (l : Link α) (xs : List α)
    (hf : ∀ x acc' ys,
      ⦃ P x ∗ I ys acc' ⦄ f x acc'
        ⦃⇓ result => I (x :: ys) result⦄) :
    ⦃ isList l xs ∗ bigSep P xs ∗ I [] acc ⦄ foldRight f xs l acc
      ⦃⇓ result => isList l xs ∗ I xs result⦄ := by
  induction xs generalizing l acc with
  | nil =>
      cases l
      · simp only [isList, bigSep, foldRight]
        sl_pure
        sl_frame
      · simp only [isList]
        sl_pull
        contradiction
  | cons x xs ih =>
      cases l with
      | none =>
          simp only [isList]
          sl_pull
          contradiction
      | some p =>
          simp only [isList, bigSep, foldRight]
          sl_pull next
          sl_step
          sl_step with ih (l := next) (acc := acc)
          sl_step with hf x

def sumList (xs : List Int) (l : Link Int) : St Int :=
  foldRight (fun x acc => pure (x + acc)) xs l 0

theorem sum_list_spec (l : Link Int) (xs : List Int) :
    ⦃ isList l xs ⦄ sumList xs l
      ⦃⇓ result =>
        iprop(⌜result = xs.foldr (· + ·) 0⌝ ∗ isList l xs)⦄ := by
  have hf : ∀ x acc ys,
      ⦃ emp ∗ ⌜acc = ys.foldr (· + ·) 0⌝ ⦄
        (pure (x + acc) : St Int)
        ⦃⇓ result => ⌜result = (x :: ys).foldr (· + ·) 0⌝⦄ := by
    intro x acc ys
    sl_pure
    sl_frame
  unfold sumList
  apply triple_conseq
    (fold_right_spec (fun _ : Int => emp)
      (fun ys acc => ⌜acc = ys.foldr (· + ·) 0⌝)
      (fun x acc => pure (x + acc)) 0 l xs hf)
  · simp only [bigSep_emp, hstar_hempty_l_eq]
    sl_frame
  · intro result
    sl_frame

end LinkedList

end IrisTutorial

end Aeneas.SLPoC
