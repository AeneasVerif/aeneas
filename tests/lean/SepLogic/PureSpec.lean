import Aeneas.Std.Alloc.Boxed
import Aeneas.Tactic.Step

namespace PureSpecNotationTests

open Aeneas
open Aeneas.Std (Error Result RustEffect RawPtr MutRawPtr U32)
open Aeneas.SepLogic
open Aeneas.Std.WP
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)

/-- The successor on the `U32` pointees of these tests: wrapping, so that the tests need no
overflow side conditions. -/
def inc (x : U32) : U32 := x.wrapping_add 1#u32

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = ispec emp m (fun x => ⌜p x⌝) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = (⦃ emp ⦄ m ⦃ x => ⌜p x⌝⦄) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄div) = (⦃ emp ⦄ m ⦃ x => ⌜p x⌝⦄div) := rfl

example (m : Result (Nat × Nat)) (p : Nat → Nat → Prop) :
    (m ⦃ x y => p x y ⦄) = ispec emp m (fun (x, y) => ⌜p x y⌝) := rfl

example (P : IProp) (m : Result (Nat × Nat)) (Q : Nat → Nat → IProp) :
    (⦃ P ⦄ m ⦃ x y => Q x y ⦄) = ispec P m (fun (x, y) => Q x y) := rfl

example (P : IProp) (m : Result (Nat × Nat)) (Q : Nat → Nat → IProp) :
    (⦃ P ⦄ m ⦃ (x, y) => Q x y ⦄) = ispec P m (fun (x, y) => Q x y) := rfl

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
⊢ Result.ok 0 ⦃ r => r = 0 ⦄div -/
#guard_msgs in example : Result.ok 0 ⦃ r => r = 0 ⦄div := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok 0
    ⦃ r => ⌜r = 0⌝ ⦄ -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok 0 ⦃ r => ⌜r = 0⌝ ⦄ := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok 0
    ⦃ r => ⌜r = 0⌝ ⦄div -/
#guard_msgs in
example : dispec emp (Result.ok 0) (fun r => ⌜r = 0⌝) := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok (0, 1)
    ⦃ x y => ⌜x = 0 ∧ y = 1⌝ ⦄ -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok (0, 1) ⦃ x y => ⌜x = 0 ∧ y = 1⌝ ⦄ := by done

/-- error: unsolved goals
⊢ ⦃ emp ⦄
    Result.ok (0, 1)
    ⦃ (x, y) => ⌜x = 0 ∧ y = 1⌝ ⦄div -/
#guard_msgs in
example : ⦃ emp ⦄ Result.ok (0, 1) ⦃ (x, y) => ⌜x = 0 ∧ y = 1⌝ ⦄div := by done

example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by
  step*

example : Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by
  step*

example : Result.ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄div := by
  step*

example : Result.ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄div := by
  step*

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 1 ⦄
    Result.ok (0, 1)
    ⦃ (x, y) => p ↦ f (x + y) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ (x, y) =>
      p ↦ f (x + y)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 1 ⦄
    Result.ok (0, 1)
    ⦃ x y => p ↦ f (x + y) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ x y =>
      p ↦ f (x + y)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 1 ⦄
    Result.ok (0, 1)
    ⦃ x y => p ↦ f (x + y) ⦄div -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ x y =>
      p ↦ f (x + y)
    ⦄div := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 3 ⦄
    Result.ok ((0, 1), 2)
    ⦃ (a, b) c => p ↦ f (a + b + c) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok ((0, 1), 2) ⦃ (a, b) c =>
      p ↦ f (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 3 ⦄
    Result.ok (0, 1, 2)
    ⦃ a b c => p ↦ f (a + b + c) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok (0, 1, 2) ⦃ a b c =>
      p ↦ f (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 3 ⦄
    Result.ok (0, 1, 2)
    ⦃ a (b, c) => p ↦ f (a + b + c) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok (0, 1, 2) ⦃ a (b, c) =>
      p ↦ f (a + b + c)
    ⦄ := by done

/-- error: unsolved goals
p : MutRawPtr U32
f : ℕ → U32
⊢ ⦃ p ↦ f 3 ⦄
    Result.ok (0, 1, 2)
    ⦃ (a, (b, c)) => p ↦ f (a + b + c) ⦄ -/
#guard_msgs in
example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok (0, 1, 2) ⦃ (a, (b, c)) =>
      p ↦ f (a + b + c)
    ⦄ := by done

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ (x, y) =>
      p ↦ f (x + y)
    ⦄ := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ (x, y) =>
      p ↦ f (x + y)
    ⦄div := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ x y =>
      p ↦ f (x + y)
    ⦄ := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 1 ⦄ Result.ok (0, 1) ⦃ x y =>
      p ↦ f (x + y)
    ⦄div := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok ((0, 1), 2) ⦃ ((x, y), z) =>
      p ↦ f (x + y + z)
    ⦄ := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok ((0, 1), 2) ⦃ (x, y) z =>
      p ↦ f (x + y + z)
    ⦄ := by
  step

example (p : MutRawPtr U32) (f : Nat → U32) :
    ⦃ p ↦ f 3 ⦄ Result.ok (0, 1, 2) ⦃ x (y, z) =>
      p ↦ f (x + y + z)
    ⦄div := by
  step

def incr (value : Nat) : Result Nat :=
  Result.ok (value + 1)

@[step]
theorem incr.spec (value : Nat) :
    ⦃ emp ⦄ incr value ⦃ result =>
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
    ⦃ result => ⌜result = value + (value + 1) + 1⌝ ⦄ := by
  unfold incrPair
  step as ⟨ output, hFirst, hSecond ⟩
  guard_hyp hFirst : output.1 = value
  guard_hyp hSecond : output.2 = value + 1
  step*

def pureSLTwice (value : Nat) : Result Nat := do
  let next ← incr value
  incr next

example (value : Nat) :
    ⦃ emp ⦄ pureSLTwice value ⦃ result => ⌜result = value + 2⌝⦄ := by
  unfold pureSLTwice
  step*

def pureSLPair (value : Nat) : Result Nat := do
  let (first, _) ← pair value
  incr first

example (value : Nat) :
    ⦃ emp ⦄ pureSLPair value ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold pureSLPair
  step*

def pureSLUnit (value : Nat) : Result Nat := do
  let _ ← (Result.ok () : Result Unit)
  incr value

example (value : Nat) :
    ⦃ emp ⦄ pureSLUnit value ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold pureSLUnit
  step*

def pureSLExists (value : Nat) : Result Nat :=
  Result.ok value

@[step]
theorem pureSLExists.spec (value : Nat) :
    ⦃ emp ⦄ pureSLExists value ⦃ result =>
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
      ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold consumePureSLExists
  step*

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄
    Result.ok 0
    ⦃ value => P ∗ ⌜value = 0⌝ ⦄ -/
#guard_msgs in
example (P : IProp) :
    ispec P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄
    Result.ok 0
    ⦃ value => P ∗ ⌜value = 0⌝ ⦄div -/
#guard_msgs in
example (P : IProp) :
    dispec P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

example (makeIncrement : Result (Nat → Result Nat)) : Prop :=
  ⦃ emp ⦄ makeIncrement ⦃ increment =>
    ⌜⦃ emp ⦄ increment 0 ⦃ value => ⌜value = 1⌝ ⦄⌝
  ⦄

example (makeIncrement : Result (Nat → Result Nat)) : Prop :=
  ⦃ emp ⦄ makeIncrement ⦃ increment =>
    ⌜∀ x, ⦃ emp ⦄ increment x ⦃ value => ⌜value = x + 1⌝ ⦄⌝
  ⦄

def increment (p : MutRawPtr U32) (_ : Unit) : Result U32 := do
  let value ← RawPtr.read p
  MutRawPtr.write p (inc value)
  pure (inc value)

@[step]
theorem increment.spec (p : MutRawPtr U32) (n : U32) :
    ⦃ p ↦ n ⦄ increment p () ⦃ value =>
      p ↦ inc n ∗ ⌜value = inc n⌝
    ⦄ := by
  unfold increment
  step*
  subst_vars
  iframe

def incrementTwiceSL (p : MutRawPtr U32) : Result U32 := do
  let _ ← increment p ()
  increment p ()

example (p : MutRawPtr U32) (n : U32) :
    ⦃ p ↦ n ⦄ incrementTwiceSL p ⦃ value =>
      p ↦ inc (inc n) ∗ ⌜value = inc (inc n)⌝
    ⦄ := by
  unfold incrementTwiceSL
  step*

def readPairSL (p : MutRawPtr U32) : Result (U32 × U32) := do
  let value ← RawPtr.read p
  pure (value, inc value)

@[step]
theorem readPairSL.spec (p : MutRawPtr U32) (n : U32) :
    ⦃ p ↦ n ⦄ readPairSL p ⦃ first second =>
      p ↦ n ∗ ⌜first = n ∧ second = inc n⌝
    ⦄ := by
  unfold readPairSL
  step*
  subst_vars
  simp

def usePairSL (p : MutRawPtr U32) : Result Unit := do
  let (_, next) ← readPairSL p
  MutRawPtr.write p next

example (p : MutRawPtr U32) (n : U32) :
    ⦃ p ↦ n ⦄ usePairSL p ⦃ p ↦ inc n⦄ := by
  unfold usePairSL
  step*
  subst_vars
  iframe

def updateTwiceSL (p : MutRawPtr U32) (n : U32) : Result Unit := do
  MutRawPtr.write p (inc n)
  MutRawPtr.write p (inc (inc n))

example (p : MutRawPtr U32) (n : U32) :
    ⦃ p ↦ n ⦄ updateTwiceSL p n ⦃ p ↦ inc (inc n)⦄ := by
  unfold updateTwiceSL
  step*

def makeCounter : Result (Unit → Result U32) :=
  Aeneas.Std.bind (into_raw ⟨0#u32⟩) fun p =>
    Result.ok (increment p)

@[step]
theorem makeCounter.spec :
  ⦃ emp ⦄ makeCounter ⦃ increment =>
    ∃ p : MutRawPtr U32,
      p ↦ 0#u32 ∗
      ⌜∀ n, ⦃ p ↦ n ⦄ increment () ⦃ value => p ↦ inc n ∗ ⌜value = inc n⌝ ⦄⌝
  ⦄ := by
  unfold makeCounter
  step as ⟨p⟩
  have hIncrement := increment.spec p
  step*

def countToFive : Result U32 :=
  Aeneas.Std.bind makeCounter fun increment => do
    let _ ← increment ()
    let _ ← increment ()
    let _ ← increment ()
    let _ ← increment ()
    increment ()

theorem countToFive.spec :
    ⦃ emp ⦄ countToFive ⦃ value => ⌜value = 5#u32⌝⦄ := by
  unfold countToFive
  step*
  have : value = 5#u32 := by subst_vars; rfl
  -- the counter is dropped (affine)
  iframe

def old_add1 (x : Nat) : Result Nat := Result.ok (x + 1)

@[step]
theorem old_add1.spec (x : Nat) :
    Aeneas.Std.WP.spec (old_add1 x) (fun y => y = x + 1) := by
  simp [old_add1]

example (v : Nat) (P : IProp) :
    ⦃ P ⦄ old_add1 v ⦃ y => P ∗ ⌜y = v + 1⌝ ⦄ := by
  step*

example (v : Nat) : old_add1 v ⦃ y => y = v + 1 ⦄ := by
  step with old_add1.spec
  assumption

example (m : Result Nat) (p : Nat → Prop) :
    Aeneas.Std.WP.spec m p = ispec emp m (fun value => ⌜p value⌝) := rfl

/-- Only running out of memory is allowed: the other errors are undefined behaviour or panics. -/
example (e : Error) (he : e ≠ .oom) (p : Nat → Prop) :
    ¬ Aeneas.Std.WP.spec (Result.fail e) p :=
  fun h => he ((spec_fail e).mp h)

example (p : Nat → Prop) : ¬ Aeneas.Std.WP.spec (Result.div : Result Nat) p :=
  spec_div.mp

example (e : Error) (he : e ≠ .oom) : ¬ (Result.fail e ⦃ (_ : Nat) => True ⦄) :=
  fun h => he ((spec_fail e).mp h)

example : Result.oom ⦃ (_ : Nat) => False ⦄ := spec_oom

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

def bumpW (x : U32) : Result U32 := pure (inc x)

@[step]
theorem bumpW.spec (x : U32) : bumpW x ⦃ y => y = inc x ⦄ := by
  unfold bumpW; step*

def bumpCell (p : MutRawPtr U32) : Result Unit := do
  let v ← RawPtr.read p
  let w ← bumpW v
  MutRawPtr.write p w

@[step]
theorem bumpCell.spec (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃ p ↦ inc v⦄ := by
  unfold bumpCell
  step*
  subst_vars
  iframe

def bumpBoxed (v : U32) : Result U32 := do
  let p ← into_raw ⟨v⟩
  bumpCell p
  let w ← RawPtr.read p
  let _ ← from_raw p
  pure w

@[step]
theorem bumpBoxed.spec (v : U32) :
    ⦃ emp ⦄ bumpBoxed v ⦃ r => ⌜r = inc v⌝⦄ := by
  unfold bumpBoxed
  step*

def mixedCall (p : MutRawPtr U32) : Result U32 := do
  bumpCell p
  let v ← RawPtr.read p
  bumpBoxed v

@[step]
theorem mixedCall.spec (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ mixedCall p ⦃ r => ⌜r = inc (inc v)⌝ ∗ p ↦ inc v⦄ := by
  unfold mixedCall
  step*
  subst_vars
  rfl

def pureCall (x : U32) : Result U32 := do
  let y ← bumpBoxed x
  let z ← bumpW y
  bumpBoxed z

example (x : U32) : ⦃ emp ⦄ pureCall x ⦃ r => ⌜r = inc (inc (inc x))⌝⦄ := by
  unfold pureCall
  step*
  subst_vars
  rfl

example (x : Nat) : bump x ⦃ y => y = x + 1 ⦄div := by step*

example (v : U32) : ⦃ emp ⦄ bumpBoxed v ⦃ r => ⌜r = inc v⌝⦄div := by step*

example (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃ p ↦ inc v⦄div :=
  ispec_dispec (bumpCell.spec p v)

def callWith {α : Type} (f : α → Result α) (x : α) : Result α := f x

theorem callWith.spec_pure {α : Type} (f : α → Result α) (x : α) (post : α → Prop)
    (hf : f x ⦃ y => post y ⦄) :
    callWith f x ⦃ y => post y ⦄ := by
  unfold callWith; exact hf

example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec_pure
  step*

example (x : U32) : ⦃ emp ⦄ callWith bumpBoxed x ⦃ y => ⌜y = inc x⌝⦄ := by
  apply callWith.spec_pure
  step*

example (p : MutRawPtr U32) (v x : U32) :
    ⦃ p ↦ v ⦄ callWith bumpBoxed x ⦃ y => ⌜y = inc x⌝ ∗ p ↦ v⦄ := by
  step with (callWith.spec_pure (post := fun y => y = inc x))
  · step*

theorem callWith.spec {α : Type} (f : α → Result α) (x : α) (P : IPre) (Q : IPost α)
    (hf : ⦃ P ⦄ f x ⦃ y => Q y⦄) :
    ⦃ P ⦄ callWith f x ⦃ y => Q y⦄ := by
  unfold callWith; exact hf

example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec
  step

example (p : MutRawPtr U32) (v w : U32) :
    ⦃ p ↦ v ⦄ callWith (fun n => do MutRawPtr.write p n; RawPtr.read p) w
      ⦃ y => ⌜y = w⌝ ∗ p ↦ w⦄ := by
  apply callWith.spec
  step*

example (p : MutRawPtr U32) (v w : U32) :
    ⦃ p ↦ v ⦄ callWith (fun n => do let m ← bumpW n; MutRawPtr.write p m; RawPtr.read p) w
      ⦃ y => ⌜y = inc w⌝ ∗ p ↦ inc w⦄ := by
  apply callWith.spec
  step*
  subst_vars
  iframe

def updateWith (f : U32 → Result U32) (p : MutRawPtr U32) : Result Unit := do
  let v ← RawPtr.read p
  let w ← f v
  MutRawPtr.write p w

@[step]
theorem updateWith.spec (f : U32 → Result U32) (p : MutRawPtr U32) (v w : U32)
    (hf : f v ⦃ r => r = w ⦄) :
    ⦃ p ↦ v ⦄ updateWith f p ⦃ p ↦ w⦄ := by
  unfold updateWith
  step as ⟨v', hv'⟩
  subst v'
  step*
  subst_vars
  iframe

example (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ updateWith bumpW p ⦃ p ↦ inc v⦄ := by
  step* +inferPost

example (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ updateWith bumpBoxed p ⦃ p ↦ inc v⦄ := by
  step* +inferPost

example (p : MutRawPtr U32) (v : U32) :
    ⦃ p ↦ v ⦄ callWith (fun n => do updateWith bumpW p; bumpW n) v
      ⦃ y => ⌜y = inc v⌝ ∗ p ↦ inc v⦄ := by
  apply callWith.spec
  step with (updateWith.spec (w := inc v))
  · step*
  · step*

end Ex

example : ⦃ emp ⦄ into_raw ⟨0#u32⟩ ⦃ _ => ⌜True⌝⦄ := by
  step*

example : ¬ ∃ q, into_raw ⟨0#u32⟩ = Result.ok q := by
  rintro ⟨q, hq⟩
  simp [into_raw, RawPtr.newBlock, Result.allocatingModify] at hq

namespace StepExamples

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

end StepExamples

end PureSpecNotationTests
