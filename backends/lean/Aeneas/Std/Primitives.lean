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

inductive RustEffect.I : Type where
| fail : Error → RustEffect.I

def RustEffect.O (i : RustEffect.I) : Type :=
  match i with
  | .fail _ => PEmpty

def RustEffect : Effect := {
  I := RustEffect.I
  O := RustEffect.O
}

-- We need Result to be irreducble outside this file (to not break metaprograms which normalize types),
-- but reducible within. The `unseal` command only affects the local context.
@[irreducible]
def Result (α : Type u) : Type u := ITree RustEffect α
unseal Result

def Result.ok {α} (a : α) : Result α := .ret a

def Result.vis {α} (eff : RustEffect.I) (k : RustEffect.O eff → Result α) : Result α := ITree.vis eff k

@[simp, grind .]
def Result.fail {α} (e : Error) : Result α := Result.vis (.fail e) PEmpty.elim

def Result.div {α} : Result α := ITree.div

-- TODO: maybe rename Result.bind
def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  ITree.bind x f

instance : Monad Result where
  pure := .ok
  bind := bind

instance : LawfulMonad Result := instLawfulMonadITree

-- TODO: is this not redundant with theorems below in this file?
theorem Result_ok_bind.{u} {A B : Type u} : ∀ (x : A) (f : A → Result B),
  bind (Result.ok x) f = f x := by
    intros x f
    let h := instLawfulMonadResult.pure_bind x f
    simp [Bind.bind] at h
    assumption

@[simp, grind .]
theorem ok_not_vis {α} {a : α} {eff k} : ¬ Result.ok a = .vis eff k := by grind [Result.ok, Result.vis]
@[simp, grind .]
theorem vis_not_ok {α} {a : α} {eff k} : ¬ .vis eff k = Result.ok a := by grind [Result.ok, Result.vis]
@[simp, grind .]
theorem ok_not_div {α} {a : α} : ¬ Result.ok a = .div := by grind [Result.ok, Result.div]
@[simp, grind .]
theorem div_not_ok {α} {a : α} : ¬ Result.div = .ok a := by grind [Result.ok, Result.div]
@[simp, grind .]
theorem vis_not_div {α} {eff k} : ¬ @Result.vis α eff k = .div := by grind [Result.div, Result.vis]
@[simp, grind .]
theorem div_not_vis {α} {eff k} : ¬ .div = @Result.vis α eff k := by grind [Result.div, Result.vis]
@[simp, grind .]
theorem Result.ok.injEq {α} {a b : α} : (Result.ok a = .ok b) = (a = b) := by
  grind [Result.ok]
-- TODO: do we need the stronger version of this that has the continuations with ≍?
@[grind .]
theorem Result.vis.injEq {α} {a b} {k1 k2} : (@Result.vis α a k1 = .vis b k2) → (a = b) := by
  grind [Result.vis, vis_inj_effect]


-- #check ITree.cases
@[elab_as_elim, cases_eliminator]
def Result.cases {R}
    {motive : Result R → Sort v}
    (t : Result R)
    (ret : ∀ r, motive (Result.ok r))
    (vis : ∀ i k, motive (Result.vis i k))
    (div :  motive (Result.div))
    : motive t := ITree.cases ret div vis t

-- inductive MatchResult : ∀ {α : Type u}, Result α → Type _ where
-- | ok {α} : (a : α) → MatchResult (Result.ok a)
-- | div : ∀ {α}, @MatchResult α .div
-- | fail : ∀ {α}, (e : Error) → @MatchResult α (.fail e)

inductive MatchResult (α : Type u) : Type u where
| ok : (a : α) → MatchResult α
| div : MatchResult α
| vis : (eff : RustEffect.I) → (RustEffect.O eff → Result α) → MatchResult α

def Result.match.{u} {α : Type u} (r : Result α) : MatchResult α :=
  r.cases .ok .vis .div

@[simp, grind .]
theorem Result.match.ok {α : Type u} {a : α} : (Result.ok a).match = .ok a := by
  simp [Result.match, Result.ok, Result.cases]
@[simp, grind .]
theorem Result.match.vis {α : Type u} {e k} : (@Result.vis α e k).match = .vis e k := by
  simp [Result.match, Result.vis, Result.cases]
@[simp, grind .]
theorem Result.match.div {α : Type u} : Result.div.match = @MatchResult.div α := by
  simp [Result.match, Result.div, Result.cases]

@[simp]
theorem Result.match.is_ok {α : Type u} {a : α} {r : Result α} : (r.match = .ok a) ↔ r = .ok a := by
  cases r <;> grind
@[simp]
theorem Result.match.is_vis {α : Type u} {e k} {r : Result α} : (r.match = .vis e k) ↔ r = .vis e k := by
  cases r <;> grind
@[simp]
theorem Result.match.is_div {α : Type u} {r : Result α} : (r.match = .div) ↔ r = .div := by
  cases r <;> grind

-- -- Before ITrees, Result was an inductive with ok, div, and fail cases only.
-- -- this function can be used in many cases to replace pattern matching on that inductive:
-- -- NOTE about split: to work with the `split` tactic, the name must start with "match_", the motive must come
-- -- before the Result input, and the div case must input a Unit.
-- -- If we commit to not needing split, we can change these things.
-- @[elab_as_elim, cases_eliminator]
-- def Result.match_dep {α}
--   {motive : Result α → Sort v}
--   (r : Result α)
--   (m : ∀ {r'}, MatchResult r' → motive r')
--   : motive r := ITree.cases (fun x => m (.ok x)) (m .div) (
--       fun e k => match e with
--         | .fail e => by
--             have same : k = PEmpty.elim := by funext x; contradiction
--             simp [same]
--             let h := (@m (.fail e) (.fail e))
--             simp [fail] at h
--             apply h
--     ) r

-- @[simp]
-- theorem Result.match.ok {R motive m x}
--   : @Result.match_dep R motive (.ok x) m = (m (.ok x)) := ITree.cases.ret

-- @[simp]
-- theorem Result.match.div {R motive m}
--   : @Result.match_dep R motive .div m = m .div := ITree.cases.div

-- @[simp]
-- theorem Result.match.fail {R motive m}
--   : @Result.match_dep R motive (.fail e) m = m (.fail e) := ITree.cases.vis

def Result.is_ok {R : Type} [BEq R] (r : Result R) (expected : R) : Bool :=
  match r.match with
  | .ok x => x == expected
  | _ => false

-- def Result.match_dep' {α}
--   {motive : Result α → Sort v}
--   (r : Result α)
--   (ok : ∀ x, r = .ok x → motive (.ok x))
--   (fail : ∀ e, r = .fail e → motive (.fail e))
--   (div : r = .div → motive (.div))
--   : motive r :=
--     Result.match_dep (motive := fun r' => r = r' -> motive r') r ok fail (fun _ => div) rfl

-- @[simp]
-- theorem Result.match_dep'.ok {R motive v r d f x}
--   (h : v = Result.ok x)
--   : @Result.match_dep' R motive v r f d = cast (congrArg motive (Eq.symm h)) (r x h) := by
--   cases v <;> unfold match_dep' <;> simp <;> grind

-- @[simp]
-- theorem Result.match_dep'.fail {R motive v r d f e}
--   (h : v = Result.fail e)
--   : @Result.match_dep' R motive v r f d = cast (congrArg motive (Eq.symm h)) (f e h) := by
--   cases v <;> unfold match_dep' <;> simp <;> grind

-- @[simp]
-- theorem Result.match_dep'.div {R motive v r d f}
--   (h : v = .div)
--   : @Result.match_dep' R motive v r f d = cast (congrArg motive (Eq.symm h)) (d h) := by
--   cases v <;> unfold match_dep' <;> simp <;> grind

-- TODO: do we need this?
-- instance {T} [Repr T] : Repr (Result T) where
--   reprPrec x n := x.match_dep fun x => match x with
--     | .ok t => .append (.text "ok ") (reprPrec t n)
--     | .fail e => .append (.text "fail ") (reprPrec e n)
--     | .div => .text "div"

-- TODO: this is how to register for split, but we probably won't use that
-- run_meta
--   Lean.Meta.Match.addMatcherInfo ``Result.match_dep {
--     numParams := 1
--     numDiscrs := 1
--     altInfos := #[
--       {
--         numFields := 1
--         numOverlaps := 0
--         hasUnitThunk := false
--       },
--       {
--         numFields := 1
--         numOverlaps := 0
--         hasUnitThunk := false
--       },
--       {
--         numFields := 0
--         numOverlaps := 0
--         hasUnitThunk := true
--       }
--     ]
--     uElimPos? := .some 0
--     discrInfos := #[{ hName? := none }]
--     overlaps := { map := Std.HashMap.ofList [] }
--   }

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
-- @[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x :=
--   by simp [bind, vis]
--      apply congrArg
--      funext x
--      contradiction
@[simp] theorem bind_vis (e k) (f : α → Result β) : bind (.vis e k) f = .vis e (fun x => bind (k x) f) :=
  by simp [bind, vis]
     rfl

@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind, div]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [bind, Bind.bind, ok]

-- TODO: will this create backwards compatibility issues?
-- @[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
--   (do let y ← fail x; f y) = fail x := by
--   simp [bind, Bind.bind, vis]
--   apply congrArg
--   funext x
--   contradiction
@[simp] theorem bind_tc_vis (e k) (f : α → Result β) :
  (do let y ← Result.vis e k; f y) = .vis e (fun x => do let y ← k x; f y) := by
  simp [bind, Bind.bind, vis]
  rfl

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

instance : PartialOrder (Result α) := instPartialOrderCoIndOfInhabitedPUnit (ITreeF RustEffect α) -- by unfold Result; infer_instance
  -- instPartialOrderCoIndOfInhabitedPUnit _
noncomputable instance : CCPO (Result α) := instCCPOCoIndOfInhabitedPUnit (ITreeF RustEffect α) -- by unfold Result; infer_instance
  -- instCCPOCoIndOfInhabitedPUnit _
noncomputable instance : MonoBind Result := instMonoBindITree

@[partial_fixpoint_monotone]
theorem bind_mono {R : Type a} {α} {S : Type b} [PartialOrder α]
  (f : α → Result R) (g : α → R → Result S) :
  monotone f →
  monotone g →
  monotone (λ x => bind (f x) (g x)) := by
    simp [bind]
    apply Aeneas.Data.Coinductive.bind_mono

-- TODO: when we add more effects, use Aeneas.Data.Coinductive.vis_mono
-- to instantiate monotonicity theorems for those effects.

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

-- TODO: will this make sense when we add more effects, given that .vis returns none?
/- A helper function that converts failure to none and success to some
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
