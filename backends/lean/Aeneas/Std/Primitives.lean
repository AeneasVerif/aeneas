module
public import Lean
public meta import Aeneas.Std.Global
public import Aeneas.Extract
public import AeneasMeta.BvEnumToBitVec
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public import Aeneas.Std.Heap
public section

namespace Aeneas

namespace Std

/-!
# Assert Command
-/

open Lean Elab Command Term Meta
open Aeneas.Data.Coinductive

syntax (name := elabSyntax) "#elab" term: command

@[command_elab elabSyntax]
meta unsafe
def elabImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    /- Simply elaborate the syntax to check that it is correct -/
    let (_, _) ← Elab.Term.elabTerm stx[1] none |>.run
    pure ())

#elab 3

/-!
# Results and Monadic Combinators
-/

@[expose] section

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

/-- The effects of Rust code running on the heap `H`. An answer lives one universe below `H`,
like the values in its heap. -/
inductive RustEffect.Input (H : Type (v + 1)) : Type (v + 1) where
| guardedModify (α : Type v) (pre : H → Prop)
    (modify : (h : H) → pre h → α × H) : RustEffect.Input H
| fail : Error → RustEffect.Input H

@[implicit_reducible]
def RustEffect.Output {H : Type (v + 1)} (i : RustEffect.Input H) : Type (v + 1) :=
  match i with
  | .guardedModify α _ _ => ULift.{v + 1} α
  | .fail _ => PEmpty

@[implicit_reducible]
def RustEffect (H : Type (v + 1)) : Effect := {
  I := RustEffect.Input H
  O := RustEffect.Output
}

-- We need ResultAt to be irreducible outside this file (to not break metaprograms which normalize
-- types), but reducible within. The `unseal` command only affects the local scope.
/-- The monad of Rust code running on the heap `H` (levels: `HeapStrat`). -/
@[irreducible]
def ResultAt (H : Type (v + 1)) (α : Type u) : Type (max u (v + 1)) := ITree (RustEffect H) α
unseal ResultAt
attribute [local implicit_reducible] ResultAt

/-- The monad of plain Rust code: it runs on the heap of level 0. -/
abbrev Result : Type u → Type (max u 1) := ResultAt Heap0

/-- Makes `Heap0` the default heap of the terms that don't fix it (`ok 0`, `massert b`, …), the way
numerals default to `Nat`: every heap is an instance, and the default instance picks `Heap0` when
nothing else determines the heap. -/
class HeapLevel (H : Type (uh + 1)) : Prop

instance (H : Type (uh + 1)) : HeapLevel H := ⟨⟩
@[default_instance] instance : HeapLevel Heap0 := ⟨⟩

variable {H : Type (uh + 1)}

def Result.ok [HeapLevel H] {α} (a : α) : ResultAt H α := .ret a

def Result.vis {α} (eff : RustEffect.Input H) (k : RustEffect.Output eff → ResultAt H α) : ResultAt H α := ITree.vis eff k

/- `Result.fail` is deliberately kept opaque: we do *not* mark it with `simp`/`grind` so that it
   never gets unfolded to a `Result.vis`. All the reasoning about `fail` should go through the
   dedicated lemmas below (`bind_fail`, `spec_fail`, ...). -/
def Result.fail [HeapLevel H] {α} (e : Error) : ResultAt H α := Result.vis (.fail e) PEmpty.elim

theorem Result.fail_eq_vis {α} (e : Error) :
  (Result.fail e : ResultAt H α) = Result.vis (.fail e) PEmpty.elim := rfl

def Result.div [HeapLevel H] {α} : ResultAt H α := ITree.div

/- `.ok`/`.fail`/… on `ResultAt H`; field-notation operations (`x.match`) live in `ResultAt`. -/
namespace ResultAt
export Result (ok vis fail div)
end ResultAt

def bind {α : Type u} {β : Type v} (x: ResultAt H α) (f: α → ResultAt H β) : ResultAt H β :=
  ITree.bind x f

instance : Monad (ResultAt H) where
  pure := .ok
  bind := bind

@[elab_as_elim, cases_eliminator]
def ResultAt.cases {R}
    {motive : ResultAt H R → Sort v}
    (t : ResultAt H R)
    (ret : ∀ r, motive (Result.ok r))
    (vis : ∀ i k, motive (Result.vis i k))
    (div :  motive (Result.div))
    : motive t := ITree.cases ret div vis t

/-- `ResultAt.cases` for `Result`: `cases` finds its eliminator by the head of the type, which is the
abbreviation `Result` rather than `ResultAt`. -/
@[elab_as_elim, cases_eliminator]
def Result.cases0 {R} {motive : Result R → Sort v} (t : Result R)
    (ret : ∀ r, motive (Result.ok r)) (vis : ∀ i k, motive (Result.vis i k))
    (div : motive Result.div) : motive t := ResultAt.cases t ret vis div

inductive MatchResult (H : Type (uh + 1)) (α : Type u) : Type (max u (uh + 1)) where
| ok : (a : α) → MatchResult H α
| div : MatchResult H α
| vis : (eff : RustEffect.Input H) → (RustEffect.Output eff → ResultAt H α) → MatchResult H α

/-!
Can simulate a match on the Result type by matching on the output of this function.
-/
def ResultAt.match {α : Type u} (r : ResultAt H α) : MatchResult H α :=
  r.cases .ok .vis .div

@[simp, grind =]
theorem ResultAt.match.ok {α : Type u} {a : α} : (Result.ok a : ResultAt H α).match = .ok a := by
  simp [ResultAt.match, Result.ok, ResultAt.cases]
@[simp, grind =]
theorem ResultAt.match.vis {α : Type u} {e k} : (@Result.vis H α e k).match = .vis e k := by
  simp [ResultAt.match, Result.vis, ResultAt.cases]
@[simp, grind =]
theorem ResultAt.match.div {α : Type u} : (Result.div : ResultAt H α).match = @MatchResult.div H α := by
  simp [ResultAt.match, Result.div, ResultAt.cases]
@[simp, grind =]
theorem ResultAt.match.fail {α : Type u} {e} :
  (Result.fail e : ResultAt H α).match = .vis (.fail e) PEmpty.elim := by
  simp [Result.fail_eq_vis]

/-- The `Repr` instance for `Result`, so that `#eval` on `Result`-producing expressions prints `Aeneas.Std.Result.ok`/`fail`/`div`. -/
instance Result.reprInst {α : Type u} [Repr α] : Repr (ResultAt H α) where
  reprPrec r _ :=
    match ResultAt.match r with
    | .ok a => "Aeneas.Std.Result.ok " ++ repr a
    | .div => "Aeneas.Std.Result.div"
    | .vis (.fail e) _ => "Aeneas.Std.Result.fail " ++ repr e
    | .vis (.guardedModify ..) _ => "Aeneas.Std.Result.guardedModify"

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
theorem Result.ok_injective {α} : Function.Injective (@Result.ok H _ α) := by
  intro a b h; simpa using congrArg ResultAt.match h

/-- `Result.fail` is opaque, so its injectivity has to be stated separately. -/
@[grind inj]
theorem Result.fail_injective {α} : Function.Injective (@Result.fail H _ α) := by
  intro a b h
  have h := congrArg ResultAt.match h
  simp only [ResultAt.match.fail, MatchResult.vis.injEq, RustEffect.Input.fail.injEq] at h
  exact h.1

/-! The disequality lemmas for the constructors of `Result`. They all follow from the fact that
`ResultAt.match` maps the constructors to *distinct* constructors of the inductive `MatchResult`. -/

@[simp]
theorem ok_not_vis {α} {a : α} {eff k} : ¬ (Result.ok a : ResultAt H α) = .vis eff k := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem vis_not_ok {α} {a : α} {eff k} : ¬ .vis eff k = (Result.ok a : ResultAt H α) := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem ok_not_div {α} {a : α} : ¬ (Result.ok a : ResultAt H α) = .div := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem div_not_ok {α} {a : α} : ¬ Result.div = (Result.ok a : ResultAt H α) := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem vis_not_div {α} {eff k} : ¬ @Result.vis H α eff k = .div := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem div_not_vis {α} {eff k} : ¬ .div = @Result.vis H α eff k := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem ok_not_fail {α} {a : α} {e} : ¬ (Result.ok a : ResultAt H α) = .fail e := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem fail_not_ok {α} {a : α} {e} : ¬ Result.fail e = (Result.ok a : ResultAt H α) := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem fail_not_div {α} {e} : ¬ (Result.fail e : ResultAt H α) = .div := by
  intro h; simpa using congrArg ResultAt.match h
@[simp]
theorem div_not_fail {α} {e} : ¬ (Result.div : ResultAt H α) = .fail e := by
  intro h; simpa using congrArg ResultAt.match h

@[simp]
theorem Result.ok.injEq {α} {a b : α} : ((Result.ok a : ResultAt H α) = .ok b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => Result.ok_injective h, fun h => by simp [h]⟩

@[simp]
theorem Result.fail.injEq {α} {a b : Error} : ((Result.fail a : ResultAt H α) = .fail b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => Result.fail_injective h, fun h => by simp [h]⟩

-- TODO: when necessary, we may need a stronger version of this which outputs ≍ for the continuations
theorem Result.vis.injEq {α} {a b} {k1 k2} : (@Result.vis H α a k1 = .vis b k2) → (a = b) := by
  intro h
  have h := congrArg ResultAt.match h
  simp only [ResultAt.match.vis, MatchResult.vis.injEq] at h
  exact h.left

@[simp]
theorem ResultAt.match.isOk {α : Type u} {a : α} {r : ResultAt H α} : (r.match = .ok a) ↔ r = .ok a := by
  cases r <;> grind
@[simp]
theorem ResultAt.match.isVis {α : Type u} {e k} {r : ResultAt H α} : (r.match = .vis e k) ↔ r = .vis e k := by
  cases r <;> grind
@[simp]
theorem ResultAt.match.isDiv {α : Type u} {r : ResultAt H α} : (r.match = .div) ↔ r = .div := by
  cases r <;> grind

/-- `r.reducesTo expected` is `true` iff `r` evaluates to `ok expected`. -/
def ResultAt.reducesTo {R : Type _} [BEq R] (r : ResultAt H R) (expected : R) : Bool :=
  match r.match with
  | .ok x => x == expected
  | _ => false

open Result

instance Result_Inhabited (α : Type u) : Inhabited (ResultAt H α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (ResultAt H α) :=
  Nonempty.intro div

/-!
# Helpers
-/

def massert [HeapLevel H] (b : Prop) [Decidable b] : ResultAt H Unit :=
  if b then ok () else fail assertionFailure

@[simp]
def Result.ofOption {a : Type u} (x : Option a) (e : Error) : ResultAt H a :=
  match x with
  | some x => ok x
  | none => fail e

@[simp] abbrev liftFun1 {α β} (f : α → β) : α → ResultAt H β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type _} (f : α → β → γ) : α → β → ResultAt H γ := fun x y => ok (f x y)
@[simp] abbrev liftFun3 {α β γ δ} (f : α → β → γ → δ) : α → β → γ → ResultAt H δ := fun x y z => ok (f x y z)
@[simp] abbrev liftFun4 {α β γ δ ε} (f : α → β → γ → δ → ε) : α → β → γ → δ → ResultAt H ε := fun x y z a => ok (f x y z a)

/-!
# Do-DSL Support
-/

@[simp] theorem bind_ok (x : α) (f : α → ResultAt H β) : bind (.ok x) f = f x :=
  by simp [bind, ok]
@[simp] theorem bind_vis (e k) (f : α → ResultAt H β) : bind (.vis e k) f = .vis e (fun x => bind (k x) f) :=
  by simp [bind, vis]
     rfl
@[simp] theorem bind_fail (e : Error) (f : α → ResultAt H β) : bind (.fail e) f = .fail e := by
  simp only [Result.fail_eq_vis, bind_vis]
  apply congrArg
  funext x
  exact x.elim

@[simp] theorem bind_div (f : α → ResultAt H β) : bind .div f = .div := by simp [bind, div]

/-- Left identity. -/
protected theorem pure_bind {α : Type u} {β : Type v} (x : α) (f : α → ResultAt H β) :
    bind (.ok x) f = f x := bind_ok x f

/-- Right identity. -/
@[simp] protected theorem bind_pure {α : Type u} (x : ResultAt H α) : bind x .ok = x := by
  change ITree.bind x ITree.ret = x
  exact _root_.bind_pure (m := ITree (RustEffect H)) x

/-- Associativity. -/
@[simp] protected theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (x : ResultAt H α) (f : α → ResultAt H β) (g : β → ResultAt H γ) :
    bind (bind x f) g = bind x (fun x => bind (f x) g) := by
  change ITree.bind (ITree.bind x f) g = ITree.bind x (fun x => ITree.bind (f x) g)
  ext n
  induction n generalizing x
  · rfl
  · rw [ITree.bind.eq_def x, ITree.bind.eq_def x]
    split
    · simp
    · simp
    · simp [*]

instance : LawfulMonad (ResultAt H) := LawfulMonad.mk' (ResultAt H)
  (id_map := Std.bind_pure)
  (pure_bind := Std.pure_bind)
  (bind_assoc := Std.bind_assoc)

/-- Normalize the typeclass bind (`>>=`) to `Std.bind`. -/
theorem bind_tc_eq {α β : Type u} (x : ResultAt H α) (f : α → ResultAt H β) :
    Bind.bind x f = bind x f := rfl

/-- Normalize the typeclass `pure` to `Result.ok`. -/
theorem pure_tc_eq {α : Type u} (x : α) : (pure x : ResultAt H α) = .ok x := rfl

@[simp] theorem bind_tc_ok (x : α) (f : α → ResultAt H β) :
  (do let y ← .ok x; f y) = f x := by simp [bind, Bind.bind, ok]

@[simp] theorem bind_tc_vis (e k) (f : α → ResultAt H β) :
  (do let y ← Result.vis e k; f y) = .vis e (fun x => do let y ← k x; f y) := by
  simp [bind, Bind.bind, vis]
  rfl

@[simp] theorem bind_tc_fail (e : Error) (f : α → ResultAt H β) :
  (do let y ← Result.fail e; f y) = .fail e := by
  simp [Bind.bind]

@[simp] theorem bind_tc_div (f : α → ResultAt H β) :
  (do let y ← div; f y) = div := by simp [bind, Bind.bind, div]

/-- `Std.bind_assoc` for the typeclass bind (whose computations live in the same universe). -/
@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : ResultAt H a) (g :  a → ResultAt H b) (h : b → ResultAt H c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := Std.bind_assoc e g h

end

unseal ResultAt
open Result

variable {H : Type (uh + 1)}

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : Lean.Order.PartialOrder (ResultAt H α) :=
  instPartialOrderCoIndOfInhabitedPUnit (ITreeF (RustEffect H) α)
noncomputable instance : CCPO (ResultAt H α) :=
  instCCPOCoIndOfInhabitedPUnit (ITreeF (RustEffect H) α)
noncomputable instance : MonoBind (ResultAt H) := instMonoBindITree

@[partial_fixpoint_monotone]
theorem bind_mono {R : Type a} {α} {S : Type b} [Lean.Order.PartialOrder α]
  (f : α → ResultAt H R) (g : α → R → ResultAt H S) :
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
@[expose, inline] def uncurry {α β γ} (f : α → β → γ) : α × β → γ :=
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
`bind e (uncurry fun a b => rest)` for tuple-destructuring `let (a, b) ← e`. -/
section
open Lean.Order

@[partial_fixpoint_monotone]
theorem monotone_uncurry
    {α : Type u} {β : Type v} {φ : Sort w} [Lean.Order.PartialOrder φ]
    {γ : Sort z} [Lean.Order.PartialOrder γ]
    (f : γ → α → β → φ)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x)) := by
  intro x y hxy p
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

@[partial_fixpoint_monotone]
theorem monotone_uncurry_applied
    {α : Type u} {β : Type v} {φ : Sort w} [Lean.Order.PartialOrder φ]
    {γ : Sort z} [Lean.Order.PartialOrder γ]
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
@[expose] def lift {α : Type u} (x : α) : Result α := Result.ok x

/-!
# Loops
-/

@[expose] section

inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α) -- continue
  | done (v : β) -- break
deriving Repr, BEq

def loop {α : Type u} {β : Type v} (body : α → ResultAt H (ControlFlow α β)) (x : α) : ResultAt H β := do
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
partial_fixpoint

def Result.guardedModify {α : Type uh} (pre : H → Prop)
    (modify : (h : H) → pre h → α × H) : ResultAt H α :=
  Result.vis (.guardedModify α pre modify) fun answer =>
    Result.ok answer.down

def Result.require (p : Prop) : ResultAt H Unit :=
  bind (Result.guardedModify (α := PUnit) (fun _ => p) fun h _ => (⟨⟩, h)) fun _ => .ok ()

/-- `H` has a layer `Heap.{u}` holding the values of `T : Type u`. No instance: `T` mentions the
monad of `H` itself (cyclic store), or generic code lacks `[Stores H T]`. -/
class Stores (H : Type (uh + 1)) (T : Type u) where
  /-- `Result.guardedModify` on the layer of `T`. -/
  modify {α : Type u} (pre : Heap.{u} → Prop) (f : (h : Heap.{u}) → pre h → α × Heap.{u}) :
    ResultAt H α

/-- A plain heap holds the values of its universe. -/
instance Stores.heap {T : Type u} : Stores Heap.{u} T := ⟨Result.guardedModify⟩

/-- `Heap0` is the default when nothing fixes the heap, like `HeapLevel`. Only level 0 has a
default: the plain heaps of the higher universes are not levels of the stratified heap. -/
@[default_instance]
instance Stores.heap0 {T : Type} : Stores Heap0 T := Stores.heap

/-- `Stores.modify` with an answer in `Type` (`Unit`, a pointer), lifted to the layer's universe. -/
def Stores.modifySmall (T : Type u) [Stores H T] {α : Type} (pre : Heap.{u} → Prop)
    (f : (h : Heap.{u}) → pre h → α × Heap.{u}) : ResultAt H α :=
  bind (Stores.modify (T := T) pre fun h hPre => let (a, h) := f h hPre; (ULift.up a, h))
    fun a => .ok a.down

end

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
@[expose] def Option.ofResult {a : Type u} (x : ResultAt H a) :
  Option a :=
  match x.match with
  | .ok x => .some x
  | _ => .none

/-!
# bv_decide
-/

#define_bv_decide_toBitVec PUnit
#define_bv_decide_toBitVec Ordering

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
