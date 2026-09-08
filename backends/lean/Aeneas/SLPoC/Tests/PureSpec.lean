import Aeneas.SLPoC.MutableData.Ptr

/-!
# The pure-computation notation

`Aeneas.SepLogic.WP` declares `⦃ ⦄` as *notation* for the separation-logic
triple that owns nothing:

```
m ⦃ x => p ⦄     is   ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄     is   triple emp m (fun x => ⌜p⌝)
m ⦃ x => p ⦄div  is   ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄div  is   dtriple emp m (fun x => ⌜p⌝)
```

There is no pure judgment, so there is nothing to bridge and nothing extra to
register with `step`: the `triple`/`dtriple` entries drive every proof below.

These tests cover the notation itself, the fact that the two forms are the
*same proposition*, the interoperability that buys — a pure specification used
inside a heap proof, a heap proof behind a pure specification, and both under
one `step*`, in higher-order settings too — and the one thing the design gives
up.

The file deliberately does not `open Aeneas`: the old `Aeneas.Std.WP` notation
is still in scope in this build and declares the identical surface for its own,
separate judgment.  §3 names that judgment on purpose, to record the gap this
notation closes.
-/

namespace PureSpecNotationTests

open Aeneas.Std (Error Result RustEffect)
open Aeneas.SepLogic
open Aeneas.SepLogic.WP

/-! ## 1. The two forms are the same proposition

`rfl` is the point: these are not two judgments related by a lemma. -/

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = triple emp m (fun x => ⌜p x⌝) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄) = (⦃ emp ⦄ m ⦃⇓ x => ⌜p x⌝⦄) := rfl

example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ x => p x ⦄div) = (⦃ emp ⦄ m ⦃⇓ x => ⌜p x⌝⦄div) := rfl

/-- Several binders destructure the returned tuple. -/
example (m : Result (Nat × Nat)) (p : Nat → Nat → Prop) :
    (m ⦃ x y => p x y ⦄) = triple emp m (fun (x, y) => ⌜p x y⌝) := rfl

/-- A postcondition given as a predicate is applied to the result. -/
example (m : Result Nat) (p : Nat → Prop) :
    (m ⦃ p ⦄) = triple emp m (fun value => ⌜p value⌝) := rfl

example (P : Prop) : (emp ⊢ ⌜P⌝) ↔ P :=
  entails_emp_ipure_iff P

example (P : Prop) (m : Result Nat) (Q : Nat → Prop) :
    triple ⌜P⌝ m (fun value => ⌜Q value⌝) ↔ (P → m ⦃ Q ⦄) :=
  triple_ipure_iff

example (P : Prop) (m : Result Nat) (Q : Nat → Prop) :
    dtriple ⌜P⌝ m (fun value => ⌜Q value⌝) ↔ (P → m ⦃ Q ⦄div) :=
  dtriple_ipure_iff

example (P Q : Nat → Prop) :
    (emp ⊢ (fun value => ⌜P value⌝) -∗+ fun value => ⌜Q value⌝) ↔
      ∀ value, P value → Q value :=
  entails_emp_postWand_ipure_iff P Q

/-! ## 2. Pretty-printing round trips -/

/-- error: unsolved goals
⊢ Result.ok 0 ⦃ r => r = 0 ⦄ -/
#guard_msgs in example : Result.ok 0 ⦃ r => r = 0 ⦄ := by done

/-- error: unsolved goals
⊢ Result.ok 0 ⦃ r => r = 0 ⦄div -/
#guard_msgs in example : Result.ok 0 ⦃ r => r = 0 ⦄div := by done

/-- error: unsolved goals
⊢ Result.ok 0 ⦃ x => True ⦄ -/
#guard_msgs in example : triple emp (Result.ok 0) (fun _ => ⌜True⌝) := by done

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

/-! ## 3. Separation-logic triple pretty-printing -/

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄ Result.ok 0 ⦃⇓ value => P ∗ ⌜value = 0⌝ ⦄ -/
#guard_msgs in
example (P : IProp) :
    triple P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

/-- error: unsolved goals
P : IProp
⊢ ⦃ P ⦄ Result.ok 0 ⦃⇓ value => P ∗ ⌜value = 0⌝ ⦄div -/
#guard_msgs in
example (P : IProp) :
    dtriple P (Result.ok 0) (fun value => P ∗ ⌜value = 0⌝) := by done

/-- error: unsolved goals
P : IProp
Q : IPost ℕ
m : Result ℕ
⊢ ⦃ P ⦄ m ⦃⇓ Q ⦄ -/
#guard_msgs in
example (P : IProp) (Q : IPost Nat) (m : Result Nat) :
    triple P m Q := by done

/-! ## 4. The gap the notation closes

`Aeneas.Std.WP.spec` is a judgment of its own, taken at the machine that
carries no state and answers no event.  Both halves of the boundary it creates
are recorded here. -/

def old_add1 (x : Nat) : Result Nat := Result.ok (x + 1)

/-- A specification in the separate pure judgment, as `Aeneas.Std` states its
scalar, slice and vector specifications. -/
@[step]
theorem old_add1.spec (x : Nat) :
    Aeneas.Std.WP.spec (old_add1 x) (fun y => y = x + 1) := by
  simp [old_add1]

/-- **Pure → separation.**  The specification is registered, it is about the
right program, and it is exactly what the goal asks for; `step` still cannot
use it, because `triple` declares no lifting from `Aeneas.Std.WP.spec`. -/
example (v : Nat) : old_add1 v ⦃ y => y = v + 1 ⦄ := by
  fail_if_success step with old_add1.spec
  unfold old_add1
  step*

/-- **Separation → pure.**  In this direction there is nothing to lift at all:
a program that performs an event is outright *false* under a judgment whose
machine answers none. -/
example (e : RustEffect.I) (k : RustEffect.O e → Result Nat) (p : Nat → Prop) :
    ¬ Aeneas.Std.WP.spec (Result.vis e k) p := by
  simp

/-- Concretely: `alloc` has no pure specification, however weak — so a function
that allocates has none either, however pure its interface. -/
example (p : Ptr Nat → Prop) : ¬ Aeneas.Std.WP.spec (alloc (0 : Nat)) p := by
  simp [alloc, allocArray, Result.guardedModify]

/-! ## 4. The computation rules

They are the rules of the triples, read at `emp` and a pure postcondition. -/

example : Result.ok 3 ⦃ r => r = 3 ⦄ := ret.spec 3

example (e : Error) : ¬ (Result.fail e ⦃ (_ : Nat) => True ⦄) :=
  fun hTriple => spec_fail e _ ∅ (triple_apply hTriple (h := ∅) trivial)

example : ¬ ((Result.div : Result Nat) ⦃ _ => True ⦄) := triple_div_elim

example : (Result.div : Result Nat) ⦃ _ => True ⦄div := dtriple_div_intro

/-- A pure-shaped triple about a return hands its postcondition back. -/
example (x : Nat) (h : Result.ok x ⦃ r => r = 3 ⦄) : x = 3 :=
  (pure_holds ∅).mp (triple_ok_apply (Q := fun r => ⌜r = 3⌝) h)

/-! ## 5. Interoperability

Every proof below is driven by `step`/`step*` through the `triple`/`dtriple`
registrations alone. -/

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

/-! ### A pure specification inside a heap proof

No lifting and no bridging lemma: `bump.spec` *is* a triple, so `step`'s
ramified-frame rule carries `p ↦ v` around it. -/

def bumpCell (p : Ptr Nat) : Result Unit := do
  let v ← read p
  let w ← bump v
  update p w

@[step]
theorem bumpCell.spec (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃⇓ p ↦ v + 1⦄ := by
  unfold bumpCell
  step*

/-! ### A heap proof behind a pure specification

`bumpBoxed` allocates, mutates and frees; its interface owns nothing, so its
specification is written in the pure notation — and that is a theorem, not a
wish, because the pure notation is a triple.  Under a separate pure judgment
the same statement is *false* (§3). -/

def bumpBoxed (v : Nat) : Result Nat := do
  let p ← alloc v
  bumpCell p
  let w ← read p
  free p
  pure w

@[step]
theorem bumpBoxed.spec (v : Nat) : bumpBoxed v ⦃ r => r = v + 1 ⦄ := by
  unfold bumpBoxed
  step*

/-! ### Both directions in one `step*` -/

def mixedCall (p : Ptr Nat) : Result Nat := do
  bumpCell p
  let v ← read p
  bumpBoxed v

@[step]
theorem mixedCall.spec (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ mixedCall p ⦃⇓ r => ⌜r = v + 2⌝ ∗ p ↦ v + 1⦄ := by
  unfold mixedCall
  step*

/-- A caller that owns nothing keeps a pure specification, though two of its
three calls allocate. -/
def pureCall (x : Nat) : Result Nat := do
  let y ← bumpBoxed x
  let z ← bump y
  bumpBoxed z

example (x : Nat) : pureCall x ⦃ r => r = x + 3 ⦄ := by
  unfold pureCall
  step
  step
  step

/-! ## 6. Total and partial correctness

`⦃ ⦄div` is `dtriple` at `emp`, so the registered `triple → dtriple` lifting
crosses the pure/heap boundary too. -/

example (x : Nat) : bump x ⦃ y => y = x + 1 ⦄div := by step*

example (v : Nat) : bumpBoxed v ⦃ r => r = v + 1 ⦄div := by step*

example (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ bumpCell p ⦃⇓ p ↦ v + 1⦄div :=
  triple_dtriple (bumpCell.spec p v)

/-! ## 7. Higher order

A combinator states its callee's contract once, as a precondition/postcondition
pair, and the pure case is that contract at `emp`.  With two disjoint judgments
each combinator needs two specifications and no call site may mix them. -/

def callWith (f : Nat → Result Nat) (x : Nat) : Result Nat := f x

/-- A *pure* contract. -/
theorem callWith.spec_pure (f : Nat → Result Nat) (x : Nat) (post : Nat → Prop)
    (hf : f x ⦃ y => post y ⦄) :
    callWith f x ⦃ y => post y ⦄ := by
  unfold callWith; exact hf

/-- Met by a closure that really is pure ... -/
example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec_pure
  step

/-- ... and by one that allocates, mutates and frees. -/
example (x : Nat) : callWith bumpBoxed x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec_pure
  step

/-- The whole higher-order call, pure contract and all, framed into a heap
proof by `step` — framing a triple is what `step` already does. -/
example (p : Ptr Nat) (v x : Nat) :
    ⦃ p ↦ v ⦄ callWith bumpBoxed x ⦃⇓ y => ⌜y = x + 1⌝ ∗ p ↦ v⦄ := by
  step with (callWith.spec_pure (post := fun y => y = x + 1))
  · step

/-- A *separating* contract.  One specification covers a pure closure, a heap
closure, and a closure that mixes them. -/
theorem callWith.spec (f : Nat → Result Nat) (x : Nat) (P : IPre) (Q : IPost Nat)
    (hf : ⦃ P ⦄ f x ⦃⇓ y => Q y⦄) :
    ⦃ P ⦄ callWith f x ⦃⇓ y => Q y⦄ := by
  unfold callWith; exact hf

example (x : Nat) : callWith bump x ⦃ y => y = x + 1 ⦄ := by
  apply callWith.spec
  step

example (p : Ptr Nat) (v w : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do update p n; read p) w
      ⦃⇓ y => ⌜y = w⌝ ∗ p ↦ w⦄ := by
  apply callWith.spec
  step*

example (p : Ptr Nat) (v w : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do let m ← bump n; update p m; read p) w
      ⦃⇓ y => ⌜y = w + 1⌝ ∗ p ↦ w + 1⦄ := by
  apply callWith.spec
  step*

/-! ### A pure contract on a heap-manipulating caller

`f` must own nothing — a real restriction, but one expressed in the same logic
as everything else, and `step` frames `p ↦ v` around it by itself. -/

def updateWith (f : Nat → Result Nat) (p : Ptr Nat) : Result Unit := do
  let v ← read p
  let w ← f v
  update p w

@[step]
theorem updateWith.spec (f : Nat → Result Nat) (p : Ptr Nat) (v w : Nat)
    (hf : f v ⦃ r => r = w ⦄) :
    ⦃ p ↦ v ⦄ updateWith f p ⦃⇓ p ↦ w⦄ := by
  unfold updateWith
  step*

example (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ updateWith bump p ⦃⇓ p ↦ v + 1⦄ := by
  step* +inferPost

/-- The crossing point: `bumpBoxed` allocates, mutates and frees, yet it meets
the *pure* contract of `updateWith.spec`. -/
example (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ updateWith bumpBoxed p ⦃⇓ p ↦ v + 1⦄ := by
  step* +inferPost

/-- Nesting: a higher-order call inside a higher-order call, pure contract on
the inside and a separating one on the outside. -/
example (p : Ptr Nat) (v : Nat) :
    ⦃ p ↦ v ⦄ callWith (fun n => do updateWith bump p; bump n) v
      ⦃⇓ y => ⌜y = v + 1⌝ ∗ p ↦ v + 1⦄ := by
  apply callWith.spec
  step with (updateWith.spec (w := v + 1))
  · step
  · step

end Ex

/-! ## 8. What the notation gives up

A pure-shaped triple no longer determines the program: `emp` owns nothing, but
an event that *needs* nothing is still permitted, and such an event is not a
`Result.ok`.  `triple_emp_eq_ok` recovers the old equivalence from the extra
hypothesis that the program performs no heap event. -/

/-- `alloc` satisfies a pure-shaped triple ... -/
example : alloc (0 : Nat) ⦃ _ => True ⦄ := by
  step*

/-- ... while not being a `Result.ok`. -/
example : ¬ ∃ q, alloc (0 : Nat) = Result.ok q := by
  rintro ⟨q, hq⟩
  have hNot : ¬ Aeneas.Std.WP.spec (alloc (0 : Nat)) (fun _ => True) := by
    simp [alloc, allocArray, Result.guardedModify]
  exact hNot (Aeneas.Std.WP.exists_imp_spec ⟨q, hq, trivial⟩)

/-- And the recovery, on a program that performs no heap event. -/
example (x : Nat) : ∃ y, Ex.bump x = Result.ok y ∧ y = x + 1 := by
  obtain ⟨y, hy, hp⟩ := triple_emp_eq_ok (Q := fun y => ⌜y = x + 1⌝)
    (by unfold Ex.bump; exact HeapFree.ok _) (Ex.bump.spec x)
  exact ⟨y, hy, (pure_holds ∅).mp hp⟩

/-! ## 9. Examples carried over from `Aeneas.Std.WP`

The statements below are the executable examples from the old pure judgment.
They confirm that the same notation, tuple destructuring, precedence and
higher-order postconditions elaborate against the triple-based notation.

The old proofs that explicitly call `spec_bind`, `spec_mono`, `qimp_spec` and
the related `imp` helpers are necessarily judgment-specific.  Their statements
remain unchanged; their proofs use the triple registration through `step`.
-/

namespace LegacyWPExamples

open Aeneas.Std (massert)
open Aeneas.Std.Result

/-! ### Notation and tuple binders -/

example : ok 0 ⦃ r => r = 0 ⦄ := by step*
example : triple emp (ok 0) (fun _ => ⌜True⌝) := by step*
example : ok 0 ⦃ _ => True ⦄ := by step*
example : triple emp (ok (0, 1)) (fun (x, y) => ⌜x = 0 ∧ y = 1⌝) := by step*
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

/-! The four old pretty-printing examples also elaborate as propositions. -/

example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by step*
example : ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by step*
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by step*
example : ok (0, (1, 2), ((3, 4, 5), 6)) ⦃ a (b, c) ((d, e, f), g) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ := by step*

/-! ### Precedence and nested specifications -/

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

/-! ### Bind and consequence examples -/

def add1 (x : Nat) := Result.ok (x + 1)

@[step]
theorem add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ := by
  unfold add1
  step

example (x : Nat) :
    (do
      let y ← add1 x
      add1 y) ⦃ y => y = x + 2 ⦄ := by
  step
  step

example (x : Nat) :
    (do
      let y ← add1 x
      add1 y) ⦃ y => y = x + 2 ⦄ := by
  step
  step

def add2 (x : Nat) := Result.ok (x + 1, x + 2)

@[step]
theorem add2_spec (x : Nat) :
    add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ := by
  unfold add2
  step

example (x : Nat) :
    (do
      let (y, _) ← add2 x
      add2 y) ⦃ (y, _) => y = x + 2 ⦄ := by
  step
  rcases y with ⟨y, z⟩
  step
  omega

@[step]
theorem add2_spec' (x : Nat) :
    add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ := by
  unfold add2
  step

example (x : Nat) :
    (do
      let (y, _) ← add2 x
      add2 y) ⦃ y _ => y = x + 2 ⦄ := by
  step
  rcases y with ⟨y, z⟩
  step
  omega

@[step]
private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
    massert b ⦃ _ => True ⦄ := by
  simp only [massert, h, ↓reduceIte]
  exact triple_ok_intro fun _ => trivial

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
  step
  step

end LegacyWPExamples

end PureSpecNotationTests
