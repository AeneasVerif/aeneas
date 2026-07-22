import Lean
import Aeneas.Std.Global
import Aeneas.Extract
import AeneasMeta.BvEnumToBitVec

namespace Aeneas

namespace Std

/-!
# Assert Command
-/

open Lean Elab Command Term Meta

syntax (name := assert) "#assert" term: command

@[command_elab assert]
unsafe
def assertImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    let r ← evalTerm Bool (mkConst ``Bool) stx[1]
    if not r then
      logInfo ("Assertion failed for:\n" ++ stx[1])
      throwError ("Expression reduced to false:\n"  ++ stx[1])
    pure ())

/--
info: true
-/
#guard_msgs in
#eval 2 == 2
#assert (2 == 2)

syntax (name := elabSyntax) "#elab" term: command

@[command_elab elabSyntax]
unsafe
def elabImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    /- Simply elaborate the syntax to check that it is correct -/
    let (_, _) ← Elab.Term.elabTerm stx[1] none |>.run
    pure ())

#elab 3

/-!
# Results and Monadic Combinators
-/

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | ub
  | div
deriving Repr, BEq

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/-!
# Helpers
-/

@[global_simps]
def ok? {α: Type u} (r: Result α): Bool :=
  match r with
  | ok _ => true
  | fail _ | ub | div => false

def div? {α: Type u} (r: Result α): Bool :=
  match r with
  | div => true
  | ok _ | fail _ | ub => false

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure

macro "prove_eval_global" : tactic => `(tactic| simp (failIfUnchanged := false) only [global_simps] <;> first | apply Eq.refl | decide)

@[global_simps]
def eval_global {α: Type u} (x: Result α) (_: ok? x := by prove_eval_global) : α :=
  match x with
  | fail _ | div => by contradiction
  | ok x => x

@[simp]
def Result.ofOption {a : Type u} (x : Option a) (e : Error) : Result a :=
  match x with
  | some x => ok x
  | none => fail e

@[simp] abbrev liftFun1 {α β} (f : α → β) : α → Result β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type} (f : α → β → γ) : α → β → Result γ := fun x y => ok (f x y)
@[simp] abbrev liftFun3 {α β γ δ} (f : α → β → γ → δ) : α → β → γ → Result δ := fun x y z => ok (f x y z)
@[simp] abbrev liftFun4 {α β γ δ ε} (f : α → β → γ → δ → ε) : α → β → γ → δ → Result ε := fun x y z a => ok (f x y z a)

/-!
# Do-DSL Support
-/

def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  match x with
  | ok v  => f v
  | fail v => fail v
  | ub => ub
  | div => div

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using pure x in do-blocks
instance : Pure Result where
  pure := fun x => ok x

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_ub (f : α → Result β) : bind .ub f = .ub := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_ub (f : α → Result β) :
  (do let y ← ub; f y) = ub := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, bind]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : Result a) (g :  a → Result b) (h : b → Result c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by
  simp [Bind.bind]
  cases e <;> simp

@[simp]
def bind_eq_iff (x : Result α) (y y' : α → Result β) :
  ((Bind.bind x y) = (Bind.bind x y')) ↔
  ∀ v, x = ok v → y v = y' v := by
  cases x <;> simp_all

instance : Monad Result where

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : PartialOrder (Result α) := inferInstanceAs (PartialOrder (FlatOrder .div))
noncomputable instance : CCPO (Result α) where
  has_csup hc := FlatOrder.instCCPO (b := Result.div).has_csup hc
noncomputable instance : MonoBind Result where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Result _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl
    . exact FlatOrder.rel.refl

end Order

/-- Aeneas-internal version of `Function.uncurry` for tuple destructuring in bind
continuations. We use our own copy so that none of the `simp`/`step` attribute
manipulations we perform on it impact user-written specs that use `Function.uncurry`
directly.

`uncurry` is purely internal to Aeneas' elaboration pipeline and should never
be directly manipulated by the user. -/
@[inline] def uncurry {α β γ} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

@[simp, grind =] theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (a : α) (b : β) :
    uncurry f (a, b) = f a b :=
  /- This proof is intentionally not `:= rfl`: `simp` would flag this lemma as
     a reflexivity lemma, meaning it would not apply it but would directly use
     `rfl` in the proofs, triggering unwanted whnf reductions in some calls
     to `step`. -/
  id rfl

/- reduction lemmas for `uncurry` restricted to functions whose end
result is `Prop`. Used by `step` to clean up spec post-conditions that
arrived as `uncurry p x` but where the call site didn't destructure further.

We restrict the final return type to `Prop` so the simp lemmas cannot fire on
bind continuations. `uncurry_eq_prop` handles the base case and
`uncurry_eq_prop_arrow` handles the curried case. -/

theorem uncurry_eq_prop {α β} (x : α × β) (p : α → β → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

theorem uncurry_eq_prop_arrow {α β σ} (x : α × β) (p : α → β → σ → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

/- Allow `partial_fixpoint` to see through `uncurry` in bind continuations.
This is needed because the custom `do` elaborator generates
`e >>= uncurry fun a b => rest` for tuple-destructuring `let (a, b) ← e`. -/
section
open Lean.Order

@[partial_fixpoint_monotone]
theorem monotone_uncurry
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x)) := by
  intro x y hxy p
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

@[partial_fixpoint_monotone]
theorem monotone_uncurry_applied
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ) (p : α × β)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x) p) := by
  intro x y hxy
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

end

attribute [simp, grind =] Function.uncurry_apply_pair

/-!
# Lift
-/

/-- We use this to lift pure function calls to monadic calls.
    We don't mark this as reducible so that **let-bindings don't get simplified away**.

    In the generated code if regularly happens that we want to lift pure function calls so
    that `step` can reason about them. For instance, `U32.wrapping_add` has type `U32 → U32 → U32`,
    but we provide a `step` theorem with an informative post-condition, and which matches the pattern
    `lift (wrapping_add x y)`. This theorem can only be looked up and appliced if the code is of the
    following shape:
    ```
    let z ← U32.wrapping_add x y
    ...
    ```

    The downside is that using `lift` forces users to write `step` theorems for pure expressions
    which appear inside a `lift`. As only a specific set of functions from the standard library are
    purified (i.e., don't live in `Result`), this should not be a big issue in practice.
  -/
def lift {α : Type u} (x : α) : Result α := Result.ok x

/-!
# Loops
-/

inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α) -- continue
  | done (v : β) -- break
deriving Repr, BEq

def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match body x with
  | ok r =>
    match r with
    | ControlFlow.cont x => loop body x
    | ControlFlow.done x => ok x
  | fail e => fail e
  | ub => ub
  | div => div
partial_fixpoint

/-!
# Misc
-/

/-- The Never type in Rust -/
inductive Never where

instance SubtypeBEq [BEq α] (p : α → Prop) : BEq (Subtype p) where
  beq v0 v1 := v0.val == v1.val

instance SubtypeLawfulBEq [BEq α] (p : α → Prop) [LawfulBEq α] : LawfulBEq (Subtype p) where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq]
  rfl := by intro a; cases a; simp [BEq.beq]

/- A helper function that converts failure to none and success to some
   TODO: move up to Core module? -/
def Option.ofResult {a : Type u} (x : Result a) :
  Option a :=
  match x with
  | ok x => some x
  | _ => none

/-!
# bv_decide
-/

#define_bv_decide_toBitVec PUnit

/-!
# Dyn
-/

structure Dyn (Trait : Type u → Type v) where
  /-- The type Self -/
  self : Type u
  /-- The trait instance -/
  inst : Trait self
  /-- The value itself -/
  value : self

end Std

end Aeneas
