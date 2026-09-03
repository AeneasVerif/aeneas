import Lean
import Aeneas.Std.Global
import Aeneas.Extract
import AeneasMeta.BvEnumToBitVec
import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect

namespace Aeneas

namespace Std

/-!
# Assert Command
-/

open Lean Elab Command Term Meta
open Aeneas.Data.Coinductive

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

inductive RustEffect.Input : Type where
| fail : Error → RustEffect.Input

def RustEffect.Output (i : RustEffect.Input) : Type :=
  match i with
  | .fail _ => PEmpty

def RustEffect : Effect := {
  I := RustEffect.Input
  O := RustEffect.Output
}

-- We need Result to be irreducble outside this file (to not break metaprograms which normalize types),
-- but reducible within. The `unseal` command only affects the local scope.
@[irreducible]
def Result (α : Type u) : Type u := ITree RustEffect α
unseal Result

def Result.ok {α} (a : α) : Result α := .ret a

def Result.vis {α} (eff : RustEffect.Input) (k : RustEffect.Output eff → Result α) : Result α := ITree.vis eff k

/- `Result.fail` is deliberately kept opaque: we do *not* mark it with `simp`/`grind` so that it
   never gets unfolded to a `Result.vis`. All the reasoning about `fail` should go through the
   dedicated lemmas below (`bind_fail`, `spec_fail`, ...). -/
def Result.fail {α} (e : Error) : Result α := Result.vis (.fail e) PEmpty.elim

theorem Result.fail_eq_vis {α} (e : Error) :
  (Result.fail e : Result α) = Result.vis (.fail e) PEmpty.elim := rfl

def Result.div {α} : Result α := ITree.div

def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  ITree.bind x f

instance : Monad Result where
  pure := .ok
  bind := bind

instance : LawfulMonad Result := instLawfulMonadITree

@[elab_as_elim, cases_eliminator]
def Result.cases {R}
    {motive : Result R → Sort v}
    (t : Result R)
    (ret : ∀ r, motive (Result.ok r))
    (vis : ∀ i k, motive (Result.vis i k))
    (div :  motive (Result.div))
    : motive t := ITree.cases ret div vis t

inductive MatchResult (α : Type u) : Type u where
| ok : (a : α) → MatchResult α
| div : MatchResult α
| vis : (eff : RustEffect.Input) → (RustEffect.Output eff → Result α) → MatchResult α

/-!
Can simulate a match on the Result type by matching on the output of this function.
-/
def Result.match.{u} {α : Type u} (r : Result α) : MatchResult α :=
  r.cases .ok .vis .div

@[simp, grind =]
theorem Result.match.ok {α : Type u} {a : α} : (Result.ok a).match = .ok a := by
  simp [Result.match, Result.ok, Result.cases]
@[simp, grind =]
theorem Result.match.vis {α : Type u} {e k} : (@Result.vis α e k).match = .vis e k := by
  simp [Result.match, Result.vis, Result.cases]
@[simp, grind =]
theorem Result.match.div {α : Type u} : Result.div.match = @MatchResult.div α := by
  simp [Result.match, Result.div, Result.cases]
@[simp, grind =]
theorem Result.match.fail {α : Type u} {e} :
  (Result.fail e : Result α).match = .vis (.fail e) PEmpty.elim := by
  simp [Result.fail_eq_vis]

/-!
`Result` not being an inductive type it has no built-in constructor facts that grind
can leverage. As we do not want to abuse e-matching, because it risks saturating
the context, we mark lemmas like `ok_not_vis` only as `simp`. This is not a problem
as only few proofs rely on this fact, and they should all be limited to the Aeneas
library (put aside rare cases, client code should not need these facts).

Injectivity is different: `@[grind inj]` is a specialized mechanism (it registers a left inverse
rather than an E-matching pattern), and it is stated purely in terms of the constructors, so it
does not reveal how `Result` is represented.
-/

@[grind inj]
theorem Result.ok_injective {α} : Function.Injective (@Result.ok α) := by
  intro a b h; simpa using congrArg Result.match h

/-- `Result.fail` is opaque, so its injectivity has to be stated separately. -/
@[grind inj]
theorem Result.fail_injective {α} : Function.Injective (@Result.fail α) := by
  intro a b h; simpa using congrArg Result.match h

/-! The disequality lemmas for the constructors of `Result`. They all follow from the fact that
`Result.match` maps the constructors to *distinct* constructors of the inductive `MatchResult`. -/

@[simp]
theorem ok_not_vis {α} {a : α} {eff k} : ¬ Result.ok a = .vis eff k := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem vis_not_ok {α} {a : α} {eff k} : ¬ .vis eff k = Result.ok a := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem ok_not_div {α} {a : α} : ¬ Result.ok a = .div := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem div_not_ok {α} {a : α} : ¬ Result.div = .ok a := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem vis_not_div {α} {eff k} : ¬ @Result.vis α eff k = .div := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem div_not_vis {α} {eff k} : ¬ .div = @Result.vis α eff k := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem ok_not_fail {α} {a : α} {e} : ¬ Result.ok a = .fail e := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem fail_not_ok {α} {a : α} {e} : ¬ Result.fail e = .ok a := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem fail_not_div {α} {e} : ¬ (Result.fail e : Result α) = .div := by
  intro h; simpa using congrArg Result.match h
@[simp]
theorem div_not_fail {α} {e} : ¬ (Result.div : Result α) = .fail e := by
  intro h; simpa using congrArg Result.match h

@[simp]
theorem Result.ok.injEq {α} {a b : α} : (Result.ok a = .ok b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => Result.ok_injective h, fun h => by simp [h]⟩

@[simp]
theorem Result.fail.injEq {α} {a b : Error} : ((Result.fail a : Result α) = .fail b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => Result.fail_injective h, fun h => by simp [h]⟩

-- TODO: when necessary, we may need a stronger version of this which outputs ≍ for the continuations
theorem Result.vis.injEq {α} {a b} {k1 k2} : (@Result.vis α a k1 = .vis b k2) → (a = b) := by
  intro h
  have h := congrArg Result.match h
  simp only [Result.match.vis, MatchResult.vis.injEq] at h
  exact h.left

@[simp]
theorem Result.match.isOk {α : Type u} {a : α} {r : Result α} : (r.match = .ok a) ↔ r = .ok a := by
  cases r <;> grind
@[simp]
theorem Result.match.isVis {α : Type u} {e k} {r : Result α} : (r.match = .vis e k) ↔ r = .vis e k := by
  cases r <;> grind
@[simp]
theorem Result.match.isDiv {α : Type u} {r : Result α} : (r.match = .div) ↔ r = .div := by
  cases r <;> grind

/-- `r.reducesTo expected` is `true` iff `r` evaluates to `ok expected`. -/
def Result.reducesTo {R : Type} [BEq R] (r : Result R) (expected : R) : Bool :=
  match r.match with
  | .ok x => x == expected
  | _ => false

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/-!
# Helpers
-/

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure

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

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x :=
  by simp [bind, ok]
@[simp] theorem bind_vis (e k) (f : α → Result β) : bind (.vis e k) f = .vis e (fun x => bind (k x) f) :=
  by simp [bind, vis]
     rfl
@[simp] theorem bind_fail (e : Error) (f : α → Result β) : bind (.fail e) f = .fail e := by
  simp only [Result.fail_eq_vis, bind_vis]
  apply congrArg
  funext x
  exact x.elim

@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind, div]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [bind, Bind.bind, ok]

@[simp] theorem bind_tc_vis (e k) (f : α → Result β) :
  (do let y ← Result.vis e k; f y) = .vis e (fun x => do let y ← k x; f y) := by
  simp [bind, Bind.bind, vis]
  rfl

@[simp] theorem bind_tc_fail (e : Error) (f : α → Result β) :
  (do let y ← Result.fail e; f y) = .fail e := by
  simp [Bind.bind]

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [bind, Bind.bind, div]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : Result a) (g :  a → Result b) (h : b → Result c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by apply bind_assoc

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : PartialOrder (Result α) := instPartialOrderCoIndOfInhabitedPUnit (ITreeF RustEffect α)
noncomputable instance : CCPO (Result α) := instCCPOCoIndOfInhabitedPUnit (ITreeF RustEffect α)
noncomputable instance : MonoBind Result := instMonoBindITree

@[partial_fixpoint_monotone]
theorem bind_mono {R : Type a} {α} {S : Type b} [PartialOrder α]
  (f : α → Result R) (g : α → R → Result S) :
  monotone f →
  monotone g →
  monotone (λ x => bind (f x) (g x)) := by
    simp [bind]
    apply Aeneas.Data.Coinductive.bind_mono

-- TODO: when we add more effects, use Aeneas.Data.Coinductive.ITree.vis_mono
-- to instantiate monotonicity theorems for those effects.
-- This will allow partial fixpoint definitions that call the effects.

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
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
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

/- A helper function that converts failure (and any effects) to none and success to some
   TODO: move up to Core module? -/
def Option.ofResult {a : Type u} (x : Result a) :
  Option a :=
  match x.match with
  | .ok x => .some x
  | _ => .none

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
