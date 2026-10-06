import Aeneas.Std.RawPtrLemmas
import Aeneas.Tactic.Step

namespace PureSpecNotationTests

open Aeneas
open Aeneas.Std (Error Result RustEffect RawPtr MutRawPtr)
open Aeneas.SepLogic
open Aeneas.Std.WP

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = ispec emp m (fun x => ⌜p x⌝) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = (⦃ emp ⦄ m ⦃⇓ x => ⌜p x⌝⦄) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄div) = (⦃ emp ⦄ m ⦃⇓ x => ⌜p x⌝⦄div) := rfl

example (m : Result (Nat × Nat)) (p : Nat → Nat → Prop) :
    (m ⦃ x y => p x y ⦄) = ispec emp m (fun (x, y) => ⌜p x y⌝) := rfl

example (P : IProp) (m : Result (Nat × Nat)) (Q : Nat → Nat → IProp) :
    (⦃ P ⦄ m ⦃⇓ x y => Q x y ⦄) = ispec P m (fun (x, y) => Q x y) := rfl

example (P : IProp) (m : Result (Nat × Nat)) (Q : Nat → Nat → IProp) :
    (⦃ P ⦄ m ⦃⇓ (x, y) => Q x y ⦄) = ispec P m (fun (x, y) => Q x y) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ p ⦄) = ispec emp m (fun value => ⌜p value⌝) := rfl

example (P : Prop) : (emp ⊢ ⌜P⌝) ↔ P :=
  entails_emp_ipure_iff P

example (P : Prop) (m : Result Nat) (Q : Nat → Prop) :
    ispec ⌜P⌝ m (fun value => ⌜Q value⌝) ↔ (P → m ⦃ Q ⦄) :=
  ispec_ipure_iff

example (P : Prop) (m : Result Nat) (Q : Nat → Prop) :
    dispec ⌜P⌝ m (fun value => ⌜Q value⌝) ↔ (P → m ⦃ Q ⦄div) :=
  dispec_ipure_iff

example (P Q : Nat → Prop) :
    (emp ⊢ (fun value => ⌜P value⌝) -∗+ fun value => ⌜Q value⌝) ↔
      ∀ value, P value → Q value :=
  entails_emp_postWand_ipure_iff P Q

/-- error: unsolved goals
⊢ Result.ok 0 ⦃ r => r = 0 ⦄ -/
#guard_msgs in example : Result.ok 0 ⦃ r => r = 0 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok 0 ⦃ r => r = 0 ⦄div -/
#guard_msgs in example : Result.ok 0 ⦃ r => r = 0 ⦄div := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok 0
    ⦃⇓ x => ⌜True⌝ ⦄ -/
#guard_msgs in example : ispec emp (Result.ok 0) (fun _ => ⌜True⌝) := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok 0
    ⦃⇓ r => ⌜r = 0⌝ ⦄ -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok 0 ⦃⇓ r => ⌜r = 0⌝ ⦄ := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok 0
    ⦃⇓ r => ⌜r = 0⌝ ⦄div -/
#guard_msgs in
example : dispec emp (Result.ok 0) (fun r => ⌜r = 0⌝) := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok (0, 1)
    ⦃⇓ x y => ⌜x = 0 ∧ y = 1⌝ ⦄ -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok (0, 1) ⦃⇓ x y => ⌜x = 0 ∧ y = 1⌝ ⦄ := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok (0, 1)
    ⦃⇓ (x, y) => ⌜x = 0 ∧ y = 1⌝ ⦄div -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok (0, 1) ⦃⇓ (x, y) => ⌜x = 0 ∧ y = 1⌝ ⦄div := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in
example : Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in
example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄div -/
#guard_msgs in
example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄div := by done

/-- error: unsolved goals
⊢ Result.ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in
example : Result.ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1, 2) ⦃ a b c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in
example : Result.ok (0, 1, 2) ⦃ a b c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1, 2) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in
example : Result.ok (0, 1, 2) ⦃ a (b, c) =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok (0, 1, 2) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in
example : Result.ok (0, 1, 2) ⦃ (a, (b, c)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by
  step*

example : Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by
  step*

example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄div := by
  step*

example : Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄div := by
  step*

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 1 ⦄
    Result.ok (0, 1)
    ⦃⇓ (x, y) => p ↦ x + y ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ (x, y) =>
      p ↦ (x + y)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 1 ⦄
    Result.ok (0, 1)
    ⦃⇓ x y => p ↦ x + y ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ x y =>
      p ↦ (x + y)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 1 ⦄
    Result.ok (0, 1)
    ⦃⇓ x y => p ↦ x + y ⦄div -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ x y =>
      p ↦ (x + y)
    ⦄div := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 3 ⦄
    Result.ok ((0, 1), 2)
    ⦃⇓ (a, b) c => p ↦ a + b + c ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok ((0, 1), 2) ⦃⇓ (a, b) c =>
      p ↦ (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 3 ⦄
    Result.ok (0, 1, 2)
    ⦃⇓ a b c => p ↦ a + b + c ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok (0, 1, 2) ⦃⇓ a b c =>
      p ↦ (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 3 ⦄
    Result.ok (0, 1, 2)
    ⦃⇓ a (b, c) => p ↦ a + b + c ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok (0, 1, 2) ⦃⇓ a (b, c) =>
      p ↦ (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr ℕ
⊢ ⦃ p ↦ 3 ⦄
    Result.ok (0, 1, 2)
    ⦃⇓ (a, (b, c)) => p ↦ a + b + c ⦄ -/
#guard_msgs in
example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok (0, 1, 2) ⦃⇓ (a, (b, c)) =>
      p ↦ (a + b + c)
    ⦄ := by done

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ (x, y) =>
      p ↦ (x + y)
    ⦄ := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ (x, y) =>
      p ↦ (x + y)
    ⦄div := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ x y =>
      p ↦ (x + y)
    ⦄ := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 1 ⦄ Result.ok (0, 1) ⦃⇓ x y =>
      p ↦ (x + y)
    ⦄div := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok ((0, 1), 2) ⦃⇓ ((x, y), z) =>
      p ↦ (x + y + z)
    ⦄ := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok ((0, 1), 2) ⦃⇓ (x, y) z =>
      p ↦ (x + y + z)
    ⦄ := by
  step

example (p : MutRawPtr Nat) :
    ⦃ p ↦ 3 ⦄ Result.ok (0, 1, 2) ⦃⇓ x (y, z) =>
      p ↦ (x + y + z)
    ⦄div := by
  step

def incr (value : Nat) : Result Nat :=
  Result.ok (value + 1)

@[step]
theorem incr.spec (value : Nat) :
    ⦃ emp ⦄ incr value ⦃⇓ result =>
      ⌜result = value + 1⌝
    ⦄ := by
  unfold incr
  step

def pair (value : Nat) : Result (Nat × Nat) :=
  Result.ok (value, value + 1)

@[step]
theorem pair.spec (value : Nat) :
    pair value ⦃ first second =>
      first = value ∧ second = value + 1
    ⦄ := by
  unfold pair
  step*

def incrPair (value : Nat) : Result Nat := do
  let output ← pair value
  incr (output.1 + output.2)

example (value : Nat) :
    ⦃ emp ⦄
      incrPair value
    ⦃⇓ result => ⌜result = value + (value + 1) + 1⌝ ⦄ := by
  unfold incrPair
  step as ⟨ output, hFirst, hSecond ⟩
  guard_hyp hFirst : output.1 = value
  guard_hyp hSecond : output.2 = value + 1
  step*

def pureSLTwice (value : Nat) : Result Nat := do
  let next ← incr value
  incr next

example (value : Nat) :
    ⦃ emp ⦄ pureSLTwice value ⦃⇓ result => ⌜result = value + 2⌝⦄ := by
  unfold pureSLTwice
  step*

def pureSLPair (value : Nat) : Result Nat := do
  let (first, _) ← pair value
  incr first

example (value : Nat) :
    ⦃ emp ⦄ pureSLPair value ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold pureSLPair
  step*

def pureSLUnit (value : Nat) : Result Nat := do
  let _ ← (Result.ok () : Result Unit)
  incr value

example (value : Nat) :
    ⦃ emp ⦄ pureSLUnit value ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold pureSLUnit
  step*

def pureSLExists (value : Nat) : Result Nat :=
  Result.ok value

@[step]
theorem pureSLExists.spec (value : Nat) :
    ⦃ emp ⦄ pureSLExists value ⦃⇓ result =>
      ∃ witness : Nat, ⌜result = witness ∧ witness = value⌝
    ⦄ := by
  unfold pureSLExists
  step*
  refine entails_exists_r value ?_
  iframe

def consumePureSLExists (value : Nat) : Result Nat := do
  let result ← pureSLExists value
  incr result

example (value : Nat) :
    ⦃ emp ⦄ consumePureSLExists value
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold consumePureSLExists
  step*

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄
    Result.ok 0
    ⦃⇓ value => P ∗ ⌜value = 0⌝ ⦄ -/
#guard_msgs in
example (P : IProp) :
    ispec P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄
    Result.ok 0
    ⦃⇓ value => P ∗ ⌜value = 0⌝ ⦄div -/
#guard_msgs in
example (P : IProp) :
    dispec P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

/-- error: unsolved goals
P : IProp
Q : IPost ℕ
m : Result ℕ
⊢ ⦃ P ⦄
    m
    ⦃⇓ Q ⦄ -/
#guard_msgs in
example (P : IProp) (Q : IPost Nat) (m : Result Nat) :
    ispec P m Q := by done

example (makeIncrement : Result (Nat → Result Nat)) : Prop :=
  ⦃ emp ⦄ makeIncrement ⦃⇓ increment =>
    ⌜⦃ emp ⦄ increment 0 ⦃⇓ value => ⌜value = 1⌝ ⦄⌝
  ⦄

example (makeIncrement : Result (Nat → Result Nat)) : Prop :=
  ⦃ emp ⦄ makeIncrement ⦃⇓ increment =>
    ⌜∀ x, ⦃ emp ⦄ increment x ⦃⇓ value => ⌜value = x + 1⌝ ⦄⌝
  ⦄

def increment (p : MutRawPtr Nat) (_ : Unit) : Result Nat := do
  let value ← RawPtr.read p
  MutRawPtr.write p (value + 1)
  pure (value + 1)

@[step]
theorem increment.spec (p : MutRawPtr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ increment p () ⦃⇓ value =>
      p ↦ (n + 1) ∗ ⌜value = n + 1⌝
    ⦄ := by
  unfold increment
  step*

def incrementTwiceSL (p : MutRawPtr Nat) : Result Nat := do
  let _ ← increment p ()
  increment p ()

example (p : MutRawPtr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ incrementTwiceSL p ⦃⇓ value =>
      p ↦ (n + 2) ∗ ⌜value = n + 2⌝
    ⦄ := by
  unfold incrementTwiceSL
  step*

def readPairSL (p : MutRawPtr Nat) : Result (Nat × Nat) := do
  let value ← RawPtr.read p
  pure (value, value + 1)

@[step]
theorem readPairSL.spec (p : MutRawPtr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ readPairSL p ⦃⇓ first second =>
      p ↦ n ∗ ⌜first = n ∧ second = n + 1⌝
    ⦄ := by
  unfold readPairSL
  step*

def usePairSL (p : MutRawPtr Nat) : Result Unit := do
  let (_, next) ← readPairSL p
  MutRawPtr.write p next

example (p : MutRawPtr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ usePairSL p ⦃⇓ p ↦ (n + 1)⦄ := by
  unfold usePairSL
  step*

def updateTwiceSL (p : MutRawPtr Nat) (n : Nat) : Result Unit := do
  MutRawPtr.write p (n + 1)
  MutRawPtr.write p (n + 2)

example (p : MutRawPtr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ updateTwiceSL p n ⦃⇓ p ↦ (n + 2)⦄ := by
  unfold updateTwiceSL
  step*

def makeCounter : Result (Unit → Result Nat) :=
  Aeneas.Std.bind (MutRawPtr.alloc 0) fun p =>
    Result.ok (increment p)

@[step]
theorem makeCounter.spec :
  ⦃ emp ⦄ makeCounter ⦃⇓ increment =>
    ∃ p : MutRawPtr Nat,
      p ↦ 0 ∗
      ⌜∀ n, ⦃ p ↦ n ⦄ increment () ⦃⇓ value => p ↦ (n + 1) ∗ ⌜value = n + 1⌝ ⦄⌝
  ⦄ := by
  unfold makeCounter
  step as ⟨p⟩
  have hIncrement := increment.spec p
  step*

def countToFive : Result Nat :=
  Aeneas.Std.bind makeCounter fun increment => do
    let _ ← increment ()
    let _ ← increment ()
    let _ ← increment ()
    let _ ← increment ()
    increment ()

theorem countToFive.spec :
    ⦃ emp ⦄ countToFive ⦃⇓ value => ⌜value = 5⌝⦄ := by
  unfold countToFive
  step*

def old_add1 (x : Nat) : Result Nat := Result.ok (x + 1)

@[step]
theorem old_add1.spec (x : Nat) :
    Aeneas.Std.WP.spec (old_add1 x) (fun y => y = x + 1) := by
  simp [old_add1]

example (v : Nat) (P : IProp) :
    ⦃ P ⦄ old_add1 v ⦃⇓ y => P ∗ ⌜y = v + 1⌝ ⦄ := by
  step*

example (v : Nat) : old_add1 v ⦃ y => y = v + 1 ⦄ := by
  step with old_add1.spec
  assumption

example (m : Result Nat) (p : Nat → Prop) :
    Aeneas.Std.WP.spec m p = ispec emp m (fun value => ⌜p value⌝) := rfl

example (e : Error) (p : Nat → Prop) : ¬ Aeneas.Std.WP.spec (Result.fail e) p :=
  (spec_fail e).mp

example (p : Nat → Prop) : ¬ Aeneas.Std.WP.spec (Result.div : Result Nat) p :=
  spec_div.mp

example : Result.ok 3 ⦃ r => r = 3 ⦄ := ret.spec 3

example (e : Error) : ¬ (Result.fail e ⦃ (_ : Nat) => True ⦄) :=
  (spec_fail e).mp

example : ¬ ((Result.div : Result Nat) ⦃ _ => True ⦄) := spec_div.mp

example : (Result.div : Result Nat) ⦃ _ => True ⦄div := dispec_div

example (x : Nat) (h : Result.ok x ⦃ r => r = 3 ⦄) : x = 3 := (spec_ok x).mp h

namespace Ex

def bump (x : Nat) : Result Nat := pure (x + 1)

@[step]
theorem bump.spec (x : Nat) : bump x ⦃ y => y = x + 1 ⦄ := by
  unfold bump; step*

def bumps (x : Nat) : Result (Nat × Nat) := pure (x + 1, x + 2)

@[step]
theorem bumps.spec (x : Nat) : bumps x ⦃ y z => y = x + 1 ∧ z = x + 2 ⦄ := by
  unfold bumps; step*

example (x : Nat) : (do let p ← bumps x; bump p.1) ⦃ r => r = x + 2 ⦄ := by
  step*

def bumpCell (p : MutRawPtr Nat) : Result Unit := do
  let v ← RawPtr.read p
  let w ← bump v
  MutRawPtr.write p w

@[step]
theorem bumpCell.spec (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃⇓ p ↦ v + 1⦄ := by
  unfold bumpCell
  step*

def bumpBoxed (v : Nat) : Result Nat := do
  let p ← MutRawPtr.alloc v
  bumpCell p
  let w ← RawPtr.read p
  MutRawPtr.free p
  pure w

@[step]
theorem bumpBoxed.spec (v : Nat) :
    ⦃ emp ⦄ bumpBoxed v ⦃⇓ r => ⌜r = v + 1⌝⦄ := by
  unfold bumpBoxed
  step*

def mixedCall (p : MutRawPtr Nat) : Result Nat := do
  bumpCell p
  let v ← RawPtr.read p
  bumpBoxed v

@[step]
theorem mixedCall.spec (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ mixedCall p ⦃⇓ r => ⌜r = v + 2⌝ ∗ p ↦ v + 1⦄ := by
  unfold mixedCall
  step*

def pureCall (x : Nat) : Result Nat := do
  let y ← bumpBoxed x
  let z ← bump y
  bumpBoxed z

example (x : Nat) : ⦃ emp ⦄ pureCall x ⦃⇓ r => ⌜r = x + 3⌝⦄ := by
  unfold pureCall
  step*

example (x : Nat) : bump x ⦃ y => y = x + 1 ⦄div := by step*

example (v : Nat) : ⦃ emp ⦄ bumpBoxed v ⦃⇓ r => ⌜r = v + 1⌝⦄div := by step*

example (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃⇓ p ↦ v + 1⦄div :=
  ispec_dispec (bumpCell.spec p v)

def callWith (f : Nat → Result Nat) (x : Nat) : Result Nat := f x

theorem callWith.spec_pure (f : Nat → Result Nat) (x : Nat) (post : Nat → Prop)
    (hf : f x ⦃ y => post y ⦄) :
    callWith f x ⦃ y => post y ⦄ := by
  unfold callWith; exact hf

example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec_pure
  step*

example (x : Nat) : ⦃ emp ⦄ callWith bumpBoxed x ⦃⇓ y => ⌜y = x + 1⌝⦄ := by
  apply callWith.spec_pure
  step*

example (p : MutRawPtr Nat) (v x : Nat) :
    ⦃ p ↦ v ⦄ callWith bumpBoxed x ⦃⇓ y => ⌜y = x + 1⌝ ∗ p ↦ v⦄ := by
  step with (callWith.spec_pure (post := fun y => y = x + 1))
  · step*

theorem callWith.spec (f : Nat → Result Nat) (x : Nat) (P : IPre) (Q : IPost Nat)
    (hf : ⦃ P ⦄ f x ⦃⇓ y => Q y⦄) :
    ⦃ P ⦄ callWith f x ⦃⇓ y => Q y⦄ := by
  unfold callWith; exact hf

example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec
  step

example (p : MutRawPtr Nat) (v w : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do MutRawPtr.write p n; RawPtr.read p) w
      ⦃⇓ y => ⌜y = w⌝ ∗ p ↦ w⦄ := by
  apply callWith.spec
  step*

example (p : MutRawPtr Nat) (v w : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do let m ← bump n; MutRawPtr.write p m; RawPtr.read p) w
      ⦃⇓ y => ⌜y = w + 1⌝ ∗ p ↦ w + 1⦄ := by
  apply callWith.spec
  step*

def updateWith (f : Nat → Result Nat) (p : MutRawPtr Nat) : Result Unit := do
  let v ← RawPtr.read p
  let w ← f v
  MutRawPtr.write p w

@[step]
theorem updateWith.spec (f : Nat → Result Nat) (p : MutRawPtr Nat) (v w : Nat)
    (hf : f v ⦃ r => r = w ⦄) :
    ⦃ p ↦ v ⦄ updateWith f p ⦃⇓ p ↦ w⦄ := by
  unfold updateWith
  step as ⟨v', hv'⟩
  subst v'
  step*

example (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ updateWith bump p ⦃⇓ p ↦ v + 1⦄ := by
  step* +inferPost

example (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ updateWith bumpBoxed p ⦃⇓ p ↦ v + 1⦄ := by
  step* +inferPost

example (p : MutRawPtr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do updateWith bump p; bump n) v
      ⦃⇓ y => ⌜y = v + 1⌝ ∗ p ↦ v + 1⦄ := by
  apply callWith.spec
  step with (updateWith.spec (w := v + 1))
  · step*
  · step*

end Ex

example : ⦃ emp ⦄ MutRawPtr.alloc (0 : Nat) ⦃⇓ _ => ⌜True⌝⦄ := by
  step*

example : ¬ ∃ q, MutRawPtr.alloc (0 : Nat) = Result.ok q := by
  rintro ⟨q, hq⟩
  simp [Aeneas.Std.MutRawPtr.alloc, Aeneas.Std.RawPtr.allocArray,
    Result.guardedModify] at hq

namespace LegacyWPExamples

open Aeneas.Std (massert)
open Aeneas.Std.Result

example : ok 0 ⦃ r => r = 0 ⦄ := by step*
example : ispec emp (ok 0) (fun _ => ⌜True⌝) := by step*
example : ok 0 ⦃ _ => True ⦄ := by step*
example : ispec emp (ok (0, 1)) (fun (x, y) => ⌜x = 0 ∧ y = 1⌝) := by step*
example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by step*
example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by step*
example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by step*
example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z ⦄ := by step*
example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by step*

example : ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok (0, (1, 2)) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok (0, (1, 2)) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by step*
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by step*
example : ok ((0, 1), 2) ⦃ ((a, b), c) =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by step*
example : ok (0, (1, 2), (3, (4, 5))) ⦃ a (b, c) (d, (e, f)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ := by step*
example : ok ((0, (1, (2, 3))), 4) ⦃ ((a, (b, (c, d))), e) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄ := by step*

example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by step*
example : ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by step*
example : ok (0, (1, 2), ((3, 4, 5), 6)) ⦃ a (b, c) ((d, e, f), g) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ := by step*

section

variable (U32 : Type) [HAdd U32 U32 (Result U32)]
variable (x y : U32)

#elab x + y ⦃ _ => True ⦄
#elab True → x + y ⦃ _ => True ⦄
#elab True ∧ x + y ⦃ _ => True ⦄

example (f : Nat → Result (Nat × (Nat → Result Nat)))
    (_ : ∀ x, f x ⦃ (y, g) => y > 0 ∧ ∀ x, g x ⦃ z => z > y ⦄ ⦄ ∧ True) :
    True := by
  simp only

end

def add1 (x : Nat) := Result.ok (x + 1)

@[step]
theorem add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ := by
  unfold add1
  step*

example (x : Nat) :
    (do
      let y ← add1 x
      add1 y) ⦃ y => y = x + 2 ⦄ := by
  step
  step
  agrind

example (x : Nat) :
    (do
      let y ← add1 x
      add1 y) ⦃ y => y = x + 2 ⦄ := by
  step*

def add2 (x : Nat) := Result.ok (x + 1, x + 2)

@[step]
theorem add2_spec (x : Nat) :
    add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ := by
  unfold add2
  step*

example (x : Nat) :
    (do
      let (y, _) ← add2 x
      add2 y) ⦃ (y, _) => y = x + 2 ⦄ := by
  step*

@[step]
theorem add2_spec' (x : Nat) :
    add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ := by
  unfold add2
  step*

example (x : Nat) :
    (do
      let (y, _) ← add2 x
      add2 y) ⦃ y _ => y = x + 2 ⦄ := by
  step*

@[step]
private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
    massert b ⦃ _ => True ⦄ := by
  simp only [massert, h, ↓reduceIte]
  exact (spec_ok ()).mpr trivial

example :
    (do
      massert (0 < 1)
      massert (1 < 2)) ⦃ _ => True ⦄ := by
  step
  step

example (zero : List Nat → Result (List Nat))
    (zero_spec : ∀ s, zero s ⦃ s' =>
      ∃ (h : s'.length = s.length),
      (∀ i, (_ : i < s.length) → s'[i]'(by grind) = 0) ⦄)
    (s : List Nat) :
    (do
      let _ ← zero s
      pure ()) ⦃ _ => True ⦄ := by
  step*

end LegacyWPExamples

end PureSpecNotationTests
