import Aeneas.Std.Primitives
import Std.Do
import Aeneas.Grind.Init

namespace Aeneas.Std.WP

open Std Result

def Post α := (α -> Prop)
def Pre := Prop

def Wp α := Post α → Pre

def wp_return (x:α) : Wp α := fun p => p x

def wp_bind (m:Wp α) (k:α -> Wp β) : Wp β :=
  fun p => m (fun r => k r p)

def wp_ord (wp1 wp2:Wp α) :=
  forall p, wp1 p → wp2 p

def theta (m:Result α) : Wp α :=
  match m with
  | ok x => wp_return x
  | fail _ => fun _ => False
  | div => fun _ => False

def p2wp (post:Post α) : Wp α :=
  fun p => forall r, post r → p r

def spec_general (x:Result α) (p:Post α) :=
  wp_ord (p2wp p) (theta x)

def spec {α} (x:Result α) (p:Post α) :=
  theta x p

/-- Auxiliary helper that we use to decompose tuples in post-conditions.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to `spec (f 0) (predn fun x => predn fun y z => ...)`.

**Remark:** an alternative would be to parameterize `predn` with a list of types, e.g.:
```lean
def prednTy (tys : List α) : Type :=
  match tys with
  | [] => Prop
  | ty :: tys => ty → prednTy tys

def prodTy (tys : List α) : Type :=
  match tys with
  | [] => ()
  | [x] => x
  | ty :: tys => (ty, prodTy tys)

def predn {tys : List α} (p : prednTy tys) : prodTy tys → Prop
```
but there are two issues:
- this kind of dependent types is hard to work with
- it forces all the types to live in the same universe, which is especially cumbersome as we do not have
  universe cumulativity
-/
def predn {α β} (p : α → β → Prop) : α × β → Prop :=
  fun (x, y) => p x y

@[simp] theorem predn_pair x y (p : α → β → Prop) : predn p (x, y) = p x y := by simp [predn]
@[defeq] theorem predn_eq x (p : α → β → Prop) : predn p x = p x.fst x.snd := by simp [predn]

@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x := by simp [spec, theta, wp_return]

@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False := by simp [spec, theta]

@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False := by simp [spec, theta]

theorem spec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind

theorem spec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
  spec m Pₘ →
  (forall x, Pₘ x → spec (k x) Pₖ) →
  spec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    apply Hm
  · simp
    apply Hm
  · simp
    apply Hm

/-- Small helper to currify functions -/
def curry {α β γ} (f : α × β → γ) (x : α) : β → γ := fun y => f (x, y)

/-- Implication -/
def imp (P Q : Prop) : Prop := P → Q

@[simp]
theorem imp_and_iff (P0 P1 Q : Prop) : imp (P0 ∧ P1) Q ↔ P0 → imp P1 Q := by simp [imp]

/-- Implication with quantifier -/
def qimp {α} (P₀ P₁ : Post α) : Prop := ∀ x, P₀ x → P₁ x

/-- We use this lemma to decompose nested `predn` predicates into a sequence of universal quantifiers. -/
@[simp]
def qimp_predn {α₀ α₁} (P : α₀ → α₁ → Prop) (Q : α₀ × α₁ → Prop) :
  qimp (predn P) Q ↔ ∀ x, qimp (P x) (curry Q x) := by
  simp [qimp, curry]

/-- We use this lemma to eliminate `imp` after we decomposed the nested `predn` -/
theorem qimp_iff {α} (P₀ P₁ : Post α) : qimp P₀ P₁ ↔ ∀ x, imp (P₀ x) (P₁ x) := by simp [qimp, imp]

/-- Alternative to `spec_mono`: we control the introduction of universal quantifiers by introducing `imp`. -/
theorem spec_mono' {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
  qimp P₀ P₁ → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind [qimp]

/-- Implication of a `spec` predicate with quantifier -/
def qimp_spec {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) : Prop :=
  ∀ x, P x → spec (k x) Q

/-- This alternative to `spec_bind` controls the introduction of universal quantifiers with `imp_spec`. -/
theorem spec_bind' {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
  spec m Pₘ →
  (qimp_spec Pₘ k Pₖ) →
  spec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    apply Hm
  · simp
    apply Hm
  · simp
    apply Hm

/-- We use this lemma to decompose nested `predn` predicates into a sequence of universal quantifiers. -/
@[simp]
def qimp_spec_predn {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → Result β) (Q : β → Prop) :
  qimp_spec (predn P) k Q ↔ ∀ x, qimp_spec (P x) (curry k x) Q := by
  simp [qimp_spec, curry]

/-- We use this lemma to eliminate `imp_spec` after we decomposed the nested `predn` -/
def qimp_spec_iff {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) :
  qimp_spec P k Q ↔ ∀ x, imp (P x) (spec (k x) Q) := by
  simp [qimp_spec, imp]

/--
error: unsolved goals
⊢ ∀ (x : Nat), qimp_spec (fun y => 0 < x + y) (curry (fun x => ok (x.fst + x.snd)) x) fun z => 0 < z
-/
#guard_msgs in
example : qimp_spec (predn fun x y => x + y > 0) (fun (x, y) => .ok (x + y)) (fun z => z > 0) := by
  simp

@[simp]
theorem qimp_exists {α β} (P₀ : β → Post α) (P₁ : Post α) :
  qimp (fun x => ∃ y, P₀ y x) P₁ ↔ ∀ x, qimp (P₀ x) P₁ := by
  simp only [qimp, forall_exists_index]; grind

@[simp]
theorem qimp_spec_exists {α β γ} (P : γ → α → Prop) (k : α → Result β) (Q : β → Prop) :
  qimp_spec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_spec (P x) k Q := by
  simp only [qimp_spec, forall_exists_index]; grind

theorem spec_equiv_exists (m:Result α) (P:Post α) :
  spec m P ↔ (∃ y, m = ok y ∧ P y) := by
  cases m <;> simp [spec, theta, wp_return]

theorem spec_imp_exists {m:Result α} {P:Post α} :
  spec m P → (∃ y, m = ok y ∧ P y) := by
  exact (spec_equiv_exists m P).1

theorem exists_imp_spec {m:Result α} {P:Post α} :
  (∃ y, m = ok y ∧ P y) → spec m P := by
  exact (spec_equiv_exists m P).2

end Aeneas.Std.WP

/-
We want the notations to live in the namespace `Aeneas`, not `Aeneas.Std.WP`
TODO: use https://github.com/leanprover/lean4/pull/11355
-/
namespace Aeneas

open Std WP Result

/-!
# Hoare triple notation and elaboration
-/

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄" : term

open Lean PrettyPrinter

/-- Macro expansion for a single element -/
macro_rules
  | `($e ⦃ $x => $p ⦄) => do `(_root_.Aeneas.Std.WP.spec $e fun $x => $p)

/-- Macro expansion for multiple elements -/
macro_rules
  | `($e ⦃ $x $xs:term* => $p ⦄) => do
    let mut xs : List (TSyntax `term) := x :: xs.toList
    let rec run (xs : List (TSyntax `term)) : MacroM (TSyntax `term) := do
      match xs with
      | [] => `($p)
      | [x] => `(fun $x => $p)
      | x :: xs =>
        let xs ← run xs
        `(_root_.Aeneas.Std.WP.predn fun $x => $xs)
    let post ← run xs
    `(Aeneas.Std.WP.spec $e $post)

/-- Macro expansion for predicate with no arrow -/
macro_rules
  | `($e ⦃ $p ⦄) => do `(_root_.Aeneas.Std.WP.spec $e $p)

/-!
# Pretty-printing
-/

open Delaborator SubExpr

/--
Small helper to decompose nested `predn`s: we strip all the variables bound in a lambda inside the `predn`s.
-/
partial def telescopePredn (vars : Array SubExpr) (e : SubExpr) (k : Array SubExpr → SubExpr → Delab) : Delab :=
  e.expr.consumeMData.withApp fun app args => do
  if h: app.isConstOf ``predn ∧ args.size = 3 then
    let pred := args[2]
    Meta.lambdaTelescope pred.consumeMData fun args body => do
    let pos := e.pos.push 1
    if h: args.size = 1 ∧ body.isAppOf ``predn then
      let vars := vars.push { expr := args[0], pos := pos.push 0 }
      telescopePredn vars { expr := body, pos := pos.push 1} k
    else
      let mut vars := vars
      let mut pos := e.pos
      for arg in args do
        vars := vars.push { expr := arg, pos := pos.push 0 }
        pos := pos.push 1
      k vars { expr := body, pos }
  else do
    Meta.lambdaTelescope e.expr.consumeMData fun args body => do
    let mut vars := vars
    let mut pos := e.pos
    for arg in args do
      vars := vars.push { expr := arg, pos := pos.push 0 }
      pos := pos.push 1
    k vars { expr := body, pos }

def elabSubExpr (e : SubExpr) : Delab := withTheReader SubExpr (fun _ => e) delab

@[scoped delab app.Aeneas.Std.WP.spec]
def delabSpec : Delab := do
  let e ← getExpr
  let pos ← getPos
  guard $ e.isAppOfArity' ``spec 3 -- only delab full applications this way
  let args := e.getAppArgs
  let monadExpr ← elabSubExpr { expr := args[1]!, pos := (pos.push 0).push 1 }
  let post : SubExpr := { expr := args[2]!, pos := pos.push 1 }
  telescopePredn #[] post fun vars post => do
  let vars ← vars.mapM elabSubExpr
  let post ← elabSubExpr post
  if vars.size = 0 then
    -- This is the case where the post-condition doesn't have a lambda
    `($monadExpr ⦃ $post ⦄)
  else
    --
    let var := vars[0]!
    let vars := vars.drop 1
    `($monadExpr ⦃ $var $vars* => $post ⦄)

/-!
# Tests
-/

example : ok 0 ⦃ r => r = 0 ⦄ := by simp
example : spec (ok 0) fun _ => True := by simp
example : ok 0 ⦃ _ => True ⦄ := by simp
example : spec (ok (0, 1)) fun (x, y) => x = 0 ∧ y = 1 := by simp
example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by simp
example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by simp
example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by simp
example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z ⦄ := by simp
example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by simp

end Aeneas

namespace Aeneas.Std.WP

section
  variable (U32 : Type) [HAdd U32 U32 (Result U32)]
  variable (x y : U32)

  #elab x + y ⦃ _ => True ⦄
  #elab True → x + y ⦃ _ => True ⦄
  #elab True ∧ x + y ⦃ _ => True ⦄

  -- Checking what happpens if we put post-conditions inside post-conditions
  example (f : Nat → Result (Nat × (Nat → Result Nat)))
          (_ : ∀ x, f x ⦃ (y, g) => y > 0 ∧ ∀ x, g x ⦃ z => z > y ⦄ ⦄ ∧ True)
   : True := by simp only
end

def add1 (x : Nat) := Result.ok (x + 1)
theorem  add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ :=
  by simp [add1]

/-- Example without `imp` -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro y h
    -- progress as ⟨ y1, z1⟩
    apply spec_mono (add1_spec _)
    intro y' h
    --
    grind

/-- Example with `imp` -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind' (add1_spec _)
    simp -failIfUnchanged only -- introduce the quantifiers
    simp only [qimp_spec_iff] -- eliminate `qimp_spec`
    intro y h
    -- progress as ⟨ y1, z1⟩
    apply spec_mono' (add1_spec _)
    simp -failIfUnchanged only -- introduce the quantifiers
    simp only [qimp_iff] -- eliminate `qimp_spec`
    simp only [imp] -- eliminate `imp`
    intro y' h
    --
    grind

def add2 (x : Nat) := Result.ok (x + 1, x + 2)

theorem  add2_spec (x : Nat) : add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- Example without `imp` -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ (y, _) => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec
    intro tmp h
    split at h
    rename_i tmp y z
    clear tmp
    -- progress as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec
    intro tmp h
    split at h
    rename_i tmp y1 z1
    clear tmp
    --
    grind

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- Example with `imp` -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ y _ => y = x + 2 ⦄ := by
    -- progress as ⟨ y, z ⟩
    apply spec_bind'
    . apply add2_spec'
    simp -failIfUnchanged only [qimp_spec_predn] -- introduce the quantifiers
    simp only [qimp_spec_iff, curry] -- eliminate `qimp_spec` and `curry`
    simp only [imp] -- eliminate `imp`
    intro y z h0
    -- progress as ⟨ y1, z1⟩
    apply spec_mono'
    . apply add2_spec'
    simp -failIfUnchanged only [qimp_predn] -- introduce the quantifiers
    simp only [qimp_iff, curry, predn] -- eliminate `qimp_spec` and `curry`
    simp only [imp]
    intros y z h
    --
    grind

private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  grind [massert]

@[simp]
theorem qimp_spec_unit {α} (P : Unit → Prop) (k : Unit → Result α) (Q : α → Prop) :
  qimp_spec P k Q ↔ (P () → k () ⦃ Q ⦄) := by
  grind [qimp_spec]

@[simp]
theorem qimp_unit (P Q : Unit → Prop) :
  qimp P Q ↔ (P () → Q ()) := by
  grind [qimp]

/-- Example with a function outputting `()` (we need to eliminate the quantifier) -/
example :
  (do
    massert (0 < 1);
    massert (1 < 2)
    ) ⦃ _ => True ⦄
  := by
  --
  apply spec_bind'
  · apply massert_spec'; omega
  simp -failIfUnchanged only [qimp_spec_unit, forall_const]
  --
  apply spec_mono'
  · apply massert_spec'; omega
  simp -failIfUnchanged only [qimp_unit, forall_const]

end Aeneas.Std.WP

namespace Aeneas.Std.WP

/-!
# mvcgen
-/

open Std Result
open Std.Do

instance Result.instWP : WP (Result) (.except Error .pure) where
    wp
        | .ok v => wp (pure v : Except Error _)
        | .fail e => wp (throw e : Except Error _)
        | .div => PredTrans.const ⌜False⌝

instance : LawfulMonad Result where
    map_const := by intros; rfl
    id_map := by intros _ x; cases x <;> rfl
    seqLeft_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    seqRight_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    pure_seq := by intros _ _ _ x; cases x <;> rfl
    pure_bind := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    bind_assoc := by intros _ _ _ x _ _; cases x <;> rfl

instance : WPMonad Result (.except Error .pure) where
  wp_pure := by
    intros
    ext Q
    simp [wp, PredTrans.pure, pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [Result.instWP]
    ext Q
    cases x <;> simp [PredTrans.const]

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e)⌝⟩) → P x := by
  intro hspec
  simp only [instWP] at hspec
  split at hspec <;> simp_all

end Aeneas.Std.WP

namespace Aeneas.Std

/-!
# Loops
-/

/-- General spec for loops with a termination measure.

It is meant to derive lemmas to reason about loops: in most situations, one shouldn't
have to use it directly when verifying programs.
-/
theorem loop.spec {α : Type u} {β : Type v} {γ : Type w}
  (measure : α → γ)
  [wf : WellFoundedRelation γ]
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ wf.rel (measure x') (measure x) ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  suffices ∀ x' x, measure x = x' → inv x → loop body x ⦃ post ⦄
    by apply this <;> first | rfl | assumption
  apply @wf.wf.fix γ (fun x' =>
    ∀ x, measure x = x' →
    inv x → loop body x ⦃ post ⦄)
  grind [loop]

end Aeneas.Std
