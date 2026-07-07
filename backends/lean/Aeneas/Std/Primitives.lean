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

-- TODO: delete this
-- inductive Result (α : Type u) where
--   | ok (v: α): Result α
--   | fail (e: Error): Result α
--   | div
-- deriving Repr, BEq

inductive RustEffect.I : Type where
| fail : Error → RustEffect.I
-- there is an issue that both threads have to return the return type.
-- maybe this is fine, and you can just bind an operation that returns Unit?
-- i could make a generalized ITree definition which allows you to do stuff to the return type in Effect?

def RustEffect.O (i : RustEffect.I) : Type :=
  match i with
  | .fail _ => PEmpty

def RustEffect : Effect := {
  I := RustEffect.I
  O := RustEffect.O
}

def Result (α : Type u) : Type u := ITree RustEffect α

instance : Monad Result := instMonadITree
instance : Bind Result where
  bind := ITree.bind
instance : LawfulMonad Result := instLawfulMonadITree

def Result.ok {α} (a : α) : Result α := .ret a

def Result.fail {α} (e : Error) : Result α := .vis (.fail e) PEmpty.elim

def Result.div {α} : Result α := ITree.div

-- TODO: adding these to simp set messes up some things
-- @[simp, grind .]
theorem ok_not_fail {α} {a : α} {e} : ¬ Result.ok a = .fail e := by grind [Result.ok, Result.fail, not_vis_ret]
-- @[simp, grind .]
theorem ok_not_div {α} {a : α} : ¬ Result.ok a = .div := by grind [Result.ok, Result.div, not_ret_div]
-- @[simp, grind .]
@[simp]
theorem Result.ok.injEq {α} {a b : α} : (Result.ok a = .ok b) = (a = b) := by
  grind [Result.ok, ret_inj]

-- previously Result was an inductive with ok, div, and fail cases only.
-- this function can be used in many cases to replace pattern matching on that inductive:
-- TODO: why do things error when this is def instead of abbrev?
@[elab_as_elim, cases_eliminator]
abbrev Result.match {α} (r : Result α)
  {motive : Result α → Sort v}
  (ok : ∀ r, motive (.ok r))
  (fail : ∀ e, motive (.fail e))
  (div :  motive (.div))
  -- will add more inputs as we add effects
  : motive r := ITree.cases ok div (
      fun e k => match e with
        | .fail e => by
            have same : k = PEmpty.elim := by funext x; contradiction
            simp [same]
            exact (fail e)
    ) r

@[simp]
theorem Result.match.ok {R motive r d f x}
  : @Result.match R (.ok x) motive r f d = r x := ITree.cases.ret

@[simp]
theorem Result.match.div {R motive r d f}
  : @Result.match R .div motive r f d = d := ITree.cases.div

@[simp]
theorem Result.match.fail {R motive r d f e}
  : @Result.match R (.fail e) motive r f d = f e := ITree.cases.vis

-- TODO: do we need both versions? I had problems with motives not being correct using the
-- dependent version, and maybe you can't use this one as a cases eliminator. TODO
def Result.nmatch {α} (r : Result α)
  {Out : Sort v}
  (ok : α  → Out)
  (fail : Error → Out)
  (div :  Out)
  -- will add more inputs as we add effects
  : Out := ITree.cases ok div (
      fun e _k => match e with
        | .fail e => fail e
    ) r

@[simp]
theorem Result.nmatch.ok {R Out r d f x}
  : @Result.nmatch R (.ok x) Out r f d = r x := ITree.cases.ret

@[simp]
theorem Result.nmatch.div {R Out r d f}
  : @Result.nmatch R .div Out r f d = d := ITree.cases.div

@[simp]
theorem Result.nmatch.fail {R Out r d f e}
  : @Result.nmatch R (.fail e) Out r f d = f e := ITree.cases.vis

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/-!
# Helpers
-/

-- TODO: where these ever used anywhere? not sure yet.
-- @[global_simps]
-- def ok? {α: Type u} (r: Result α): Bool :=
--   ITree.cases
--     (fun o =>
--       match o with
--       | .ok _ => true
--       | .fail _ => false
--     )
--     false
--     (fun _ _ => false)
--     r

-- def div? {α: Type u} (r: Result α): Bool :=
--   ITree.cases
--     (fun _ => false)
--     true
--     (fun _ _ => false)
--     r

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure

macro "prove_eval_global" : tactic => `(tactic| simp (failIfUnchanged := false) only [global_simps] <;> first | apply Eq.refl | decide)

-- @[global_simps]
-- def eval_global {α: Type u} (x: Result α) (_: ok? x := by prove_eval_global) : α :=
--   -- match x with
--   -- | fail _ | div => by contradiction
--   -- | ok x => x

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

-- TODO: in addition to type levels, does it cause issues that bind comes from the Monad instance?
-- -- TODO: is it ok to not have β be at a different level `v`?
def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  ITree.bind x f

-- TODO: should this just be deleted to clean things up now, or left for backwards compatibility?
-- def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
--   @Bind.bind Result _ α β x f

-- -- Allows using Result in do-blocks
-- instance : Bind Result where
  -- bind := bind

-- Allows using pure x in do-blocks
instance : Pure Result where
  pure := fun x => ok x

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x :=
  by simp [bind, ok]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x :=
  by simp [bind, fail]
     apply congrArg
     funext x
     contradiction

@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind, div]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, ok]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by
  simp [Bind.bind, fail]
  apply congrArg
  funext x
  contradiction

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, div]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : Result a) (g :  a → Result b) (h : b → Result c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by apply bind_assoc

-- TODO: i think that this is false for the ITree version?
-- because if x = `vis _ k`, then the rhs of the ↔ says exactly nothing,
-- and the lhs says that y = y'.
-- @[simp]
-- def bind_eq_iff (x : Result α) (y y' : α → Result β) :
--   ((Bind.bind x y) = (Bind.bind x y')) ↔
--   ∀ v, x = ok v → y v = y' v := by
  -- -- cases x <;> simp_all
  -- constructor
  -- · intros
  --   subst_vars
  --   simp at *
  --   assumption
  -- · intros h
  --   revert h
  --   refine ITree.cases ?_ ?_ ?_ x
  --   ·
  --     intros r h
  --     refine (.trans (pure_bind _ _) (.trans ?_ (Eq.symm (pure_bind _ _))))
  --     apply h
  --     simp [pure]
  --     rfl
  --   · intros h
  --     simp [bind, itree_div_bind]
  --   ·
  --     intros
  --     sorry

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : PartialOrder (Result α) := instPartialOrderCoIndOfInhabitedPUnit _
noncomputable instance : CCPO (Result α) := instCCPOCoIndOfInhabitedPUnit _
noncomputable instance : MonoBind Result := instMonoBindITree

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

-- TODO: will the fact that β now has level u instead of v cause problems?
def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  ITree.bind (body x) fun r =>
  -- let r ← body x
  -- _
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
partial_fixpoint


-- TODO: this is original, delete this
-- def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
--   match body x with
--   | ok r =>
--     match r with
--     | ControlFlow.cont x => loop body x
--     | ControlFlow.done x => ok x
--   | fail e => fail e
--   | div => div
-- partial_fixpoint

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

-- TODO: will this make sense, given that .vis now returns none?
/- A helper function that converts failure to none and success to some
   TODO: move up to Core module? -/
def Option.ofResult {a : Type u} (x : Result a) :
  Option a :=
  x.nmatch
    .some
    (fun _ => .none)
    .none

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
