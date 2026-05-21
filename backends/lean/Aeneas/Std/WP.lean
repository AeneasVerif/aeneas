import Aeneas.Std.Primitives
import Aeneas.Std.Delab
import Std.Do
import Aeneas.Tactic.Solver.Grind.Init

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

/-- Variant of `uncurry` used to decompose tuples in post-conditions.

Similar to `uncurry` but specialized for `Prop` and delaborated differently:
`uncurry'` is delaborated as `x y => ...` (separate binders), while
`uncurry` is delaborated as `(x, y) => ...` (tuple binder).
We use this in the Hoare triple notation `⦃ ⦄`.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to
`spec (f 0) (uncurry' fun x => uncurry' fun y z => ...)`.
-/
def uncurry' {α β} (p : α → β → Prop) : α × β → Prop :=
  fun (x, y) => p x y

@[simp] theorem uncurry'_pair x y (p : α → β → Prop) : uncurry' p (x, y) = p x y := by simp [uncurry']
@[defeq] theorem uncurry'_eq x (p : α → β → Prop) : uncurry' p x = p x.fst x.snd := by simp [uncurry']

@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x := by simp [spec, theta, wp_return]

@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False := by simp [spec, theta]

@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False := by simp [spec, theta]

/-! ### `spec_*` for tuple posts

Needed now with the new `uncurry`-based pattern matching. -/

@[simp, grind =, agrind =]
theorem spec_ok_pair {α β} (a : α) (b : β) (f : α → β → Prop) :
    spec (ok (a, b)) (uncurry f) ↔ f a b := by
  simp [spec_ok]

@[simp, grind =, agrind =]
theorem spec_fail_pair (e : Error) (f : α → β → Prop) :
    spec (fail e) (uncurry f) ↔ False := by simp

@[simp, grind =, agrind =]
theorem spec_div_pair (f : α → β → Prop) :
    spec div (uncurry f) ↔ False := by simp

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

/-- We use this lemma to decompose nested `uncurry'` predicates into a sequence of universal quantifiers. -/
@[simp]
def qimp_uncurry' {α₀ α₁} (P : α₀ → α₁ → Prop) (Q : α₀ × α₁ → Prop) :
  qimp (uncurry' P) Q ↔ ∀ x, qimp (P x) (curry Q x) := by
  simp [qimp, curry]

/-- We use this lemma to eliminate `imp` after we decomposed the nested `uncurry'` -/
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

/-- We use this lemma to decompose nested `uncurry'` predicates into a sequence of universal quantifiers. -/
@[simp]
def qimp_spec_uncurry' {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → Result β) (Q : β → Prop) :
  qimp_spec (uncurry' P) k Q ↔ ∀ x, qimp_spec (P x) (curry k x) Q := by
  simp [qimp_spec, curry]

/-- We use this lemma to eliminate `imp_spec` after we decomposed the nested `uncurry'` -/
def qimp_spec_iff {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) :
  qimp_spec P k Q ↔ ∀ x, imp (P x) (spec (k x) Q) := by
  simp [qimp_spec, imp]

/--
error: unsolved goals
⊢ ∀ (x : Nat), qimp_spec (fun y => 0 < x + y) (curry (fun x => ok (x.fst + x.snd)) x) fun z => 0 < z
-/
#guard_msgs in
example : qimp_spec (uncurry' fun x y => x + y > 0) (fun (x, y) => .ok (x + y)) (fun z => z > 0) := by
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

/-- Partial-correctness variant of `spec`.

`spec_partial x p_ok p_fail p_div` reads as: "if `x` reduces to `ok a` then `p_ok a` holds; if it
reduces to `fail e` then `p_fail e` holds; if it diverges then `p_div` holds". Unlike `spec`, it
does not assume the program terminates without exception. -/
def spec_partial {α} (x : Result α)
    (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) : Prop :=
  match x with
  | ok a   => p_ok a
  | fail e => p_fail e
  | div    => p_div

@[simp, grind =, agrind =]
theorem spec_partial_ok (a : α) (p_ok : α → Prop) p_fail p_div :
    spec_partial (ok a) p_ok p_fail p_div ↔ p_ok a := by
  simp [spec_partial]

@[simp, grind =, agrind =]
theorem spec_partial_fail (e : Error) p_ok p_fail p_div :
    spec_partial (α := α) (fail e) p_ok p_fail p_div ↔ p_fail e := by
  simp [spec_partial]

@[simp, grind =, agrind =]
theorem spec_partial_div (p_ok : α → Prop) p_fail p_div :
    spec_partial div p_ok p_fail p_div ↔ p_div := by
  simp [spec_partial]

/-- Derive a total-correctness `spec` from `spec_partial` by ruling out the failure and divergence
cases. Used by `@[step]` to generate a step-tactic lemma from a `spec_partial` theorem. -/
theorem spec_of_spec_partial
    {α} {x : Result α} {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : spec_partial x p_ok p_fail p_div)
    (h_fail : ∀ e, ¬ p_fail e) (h_div : ¬ p_div) :
    spec x p_ok := by
  cases x <;> simp_all [spec_partial, spec, theta, wp_return]

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

/-- Build a `Std.uncurry` chain wrapping a curried lambda over `xs`.

Given `x0`, ..., `xn` and `body`, generates the (syntactic) term `fun (x0, ..., xn) => body`.
-/
partial def buildUncurryLam (xs : List (TSyntax `term)) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let uncurryIdent := mkIdent ``Std.uncurry
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildUncurryLam rest body
    `($uncurryIdent (fun $a => $inner))

/-- Helper to elaborate `binder => body` when binder is a tuple - this supports nested tuples. -/
partial def mkBinderFun (depth : Nat) (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        -- Fresh identifier from depth + index
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkBinderFun (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildUncurryLam leafIdents wrappedBody
  | _ => `(fun $binder => $body)

/-- Macro expansion for a single element -/
macro_rules
  | `($e ⦃ $x => $p ⦄) => do
    let post ← mkBinderFun 0 x p
    `(Aeneas.Std.WP.spec $e $post)

/-- Macro expansion for multiple elements -/
macro_rules
  | `($e ⦃ $x $xs:term* => $p ⦄) => do
    let xs := x :: xs.toList
    let rec run (depth : Nat) (xs : List Term) : MacroM Term := do
      match xs with
      | [] => `($p)
      | [x] => mkBinderFun depth x p
      | x :: xs =>
        let xs ← run (depth + 1) xs
        let inner ← mkBinderFun depth x xs
        `(uncurry' $inner)
    let post ← run 0 xs
    `(Aeneas.Std.WP.spec $e $post)

/-- Macro expansion for predicate with no arrow -/
macro_rules
  | `($e ⦃ $p ⦄) => do `(_root_.Aeneas.Std.WP.spec $e $p)

/-!
# Pretty-printing

The `⦃ ⦄` macro produces postconditions using three wrappers:
- `uncurry' (fun x => ...)` — separate binders, printed as `x y z => ...`
- `uncurry (fun a b => ...)` — tuple binder, printed as `(a, b) => ...`
- Plain `fun x => ...` — scalar binder

`uncurry'` is never nested: it only appears at the outermost level to separate
top-level product components. `uncurry` can be nested inside `uncurry'` or other
`uncurry` applications (for sub-tuples like `((a, b), c)`).

**Examples of elaborated postconditions:**

| Source | Elaborated form |
|---|---|
| `⦃ r => body ⦄` | `fun r => body` |
| `⦃ (a, b) => body ⦄` | `uncurry (fun a b => body)` |
| `⦃ x y z => body ⦄` | `uncurry' (fun x => uncurry' (fun y z => body))` |
| `⦃ (a, b) c => body ⦄` | `uncurry' (uncurry (fun a b => fun c => body))` |
| `⦃ a (b, c) => body ⦄` | `uncurry' (fun a => uncurry (fun b c => body))` |
| `⦃ ((a,b), c) => body ⦄` | `uncurry (fun _p c => (uncurry (fun a b => body)) _p)` |
| `⦃ ((a,b), (c,d)) => body ⦄` | `uncurry (fun _p₀ _p₁ => (uncurry (fun a b => (uncurry (fun c d => body)) _p₁)) _p₀)` |

The delaborator reverses this: given a `spec e post` expression, it peels the
wrapper layers to recover the binder patterns and body, producing `⦃ ... => ... ⦄`.

The `uncurry`/lambda machinery (`enterLams`, `enterUncurryChain`, `delabBinders`)
is reused from `Do.Delab` (which handles the same `uncurry` chains in `do`-notation).
The only WP-specific logic is the `uncurry'`-peeling loop on top.
-/

open Delaborator SubExpr
open Std.Delab (enterLams enterUncurryChain delabBinders buildTupleTerm delabUncurryAsTuple)

/-- Enter exactly the binders of a single `uncurry` level (up to 2).
Unlike `enterUncurryChain` (which flattens everything), this stops after 2 binders
so the continuation lambdas are left untouched.

Example: on `fun a b => fun c => body`, collects `[a, b]` and leaves the reader
at `fun c => body`. -/
private partial def enterUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterUncurryOnce acc' k
      else enterUncurryOnce acc' k
  | _ => k acc

/-- Is the expression an `uncurry'` or `uncurry` wrapper? -/
private def isPostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | uncurry' _ _ _ => true
  | uncurry _ _ _ _ => true
  | _ => false

/-- Walk the postcondition expression, peeling `uncurry'`/`uncurry`/lambda layers.
Returns `(binders, bodyTerm)` where each binder is a `Term` (either a plain
name like `x` or a (potentially nested) tuple pattern like `(a, b)`).
-/
private partial def delabPostBinders : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | uncurry' _ _ _ =>
    /- `uncurry' f`: dive into `f` (arg 2) and peel one binder.
       If `f = uncurry g`, the binder is a tuple `(a, b)`.
       If `f = fun x => rest`, the binder is scalar `x`. -/
    withNaryArg 2 do
      match_expr (← getExpr).consumeMData with
      | uncurry _ _ _ _ =>
        -- Tuple binder: peel one uncurry level, then recurse for more binders
        withAppArg <| enterUncurryOnce #[] fun tupleBinders => do
          let (pats, (moreBinders, body)) ← delabBinders tupleBinders.toList delabPostBinders
          let tupleTerm ← buildTupleTerm pats
          return (#[tupleTerm] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | uncurry _ _ _ _ =>
    /- Single tuple binder `(a, b) => body` (no `uncurry'` wrapper). -/
    let tuplePos ← getPos
    withAppArg do
      let (tupleTerm, body) ← delabUncurryAsTuple delab
      let tupleTerm : Term := annotatePos tuplePos tupleTerm
      addTermInfo tuplePos tupleTerm.raw (← getExpr) (isBinder := true)
      return (#[tupleTerm], body)
  | _ => delabLamsThenRecurse
where
  /-- Peel plain lambda binders, then either recurse or terminate.

  This is used in two situations:
  - Inside `uncurry'`, when the argument is a plain lambda (not `uncurry`):
    e.g., `uncurry' (fun x => uncurry' (fun y z => body))` — after entering
    `fun x =>`, the body starts with another `uncurry'`, so we recurse.
  - At the top level, when the postcondition is a plain lambda without any
    `uncurry'`/`uncurry` wrapper: e.g., `fun r => body`.

  The key logic: if `enterLams` peels exactly one lambda and the body is a
  wrapper (`uncurry'` or `uncurry`), this lambda is a scalar binder in a
  multi-binder postcondition — recurse via `delabPostBinders` to peel more.
  Otherwise these are terminal binders (e.g., `fun y z => body` at the last
  `uncurry'` level) — delab the body directly. -/
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    if (← getExpr).consumeMData.isLambda then
      enterLams #[] fun binders => do
        if binders.size == 1 && isPostBinderWrapper (← getExpr) then
          let (pats, (moreBinders, body)) ← delabBinders binders.toList delabPostBinders
          return (pats ++ moreBinders, body)
        else
          let (pats, body) ← delabBinders binders.toList delab
          return (pats, body)
    else
      return (#[], ← delab)

/-- Delaborator for `WP.spec e post` → `e ⦃ binders => body ⦄`. -/
@[scoped delab app.Aeneas.Std.WP.spec]
def delabSpec : Delab := do
  guard $ (← getExpr).isAppOfArity' ``spec 3
  let monadExpr ← withNaryArg 1 delab
  let (binders, bodyTerm) ← withNaryArg 2 delabPostBinders
  if binders.size == 0 then
    `($monadExpr ⦃ $bodyTerm ⦄)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $bodyTerm ⦄)

/-!
# Tests
-/

/-- error: unsolved goals
⊢ ok 0 ⦃ r => r = 0 ⦄ -/
#guard_msgs in example : ok 0 ⦃ r => r = 0 ⦄ := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : spec (ok 0) fun _ => True := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : ok 0 ⦃ _ => True ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x✝ =>
    match x✝ with
    | (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : spec (ok (0, 1)) fun (x, y) => x = 0 ∧ y = 1 := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = true ⦄ -/
#guard_msgs in example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z ⦄ := by done
/-- error: unsolved goals
⊢ let P := fun x => x = 0;
  ok 0 ⦃ P ⦄ -/
#guard_msgs in example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by done

/-! ### Mixed tuple / scalar binders -/

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Tuple followed by scalar
example : ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Scalar followed by tuple
example : ok (0, (1, 2)) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok (0, (1, 2)) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two tuples in sequence
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- A single nested tuple
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two nested tuples
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), 3, 4, 5) ⦃ a (b, c) (d, (e, f)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ -/
#guard_msgs in -- Scalar, tuple, nested tuple
example : ok (0, (1, 2), (3, (4, 5))) ⦃ a (b, c) (d, (e, f)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1, 2, 3), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄ -/
#guard_msgs in -- More nesting
example : ok ((0, (1, (2, 3))), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄
  := by done

/-! ### Pretty-printing round-trip checks -/

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in example : ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), (3, 4, 5), 6) ⦃ a (b, c) ((d, e, f), g) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ -/
#guard_msgs in example : ok (0, (1, 2), ((3, 4, 5), 6)) ⦃ a (b, c) ((d, e, f), g) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ := by done

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
    -- step as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro y h
    -- step as ⟨ y1, z1⟩
    apply spec_mono (add1_spec _)
    intro y' h
    --
    grind

/-- Example with `imp` -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind' (add1_spec _)
    simp -failIfUnchanged only -- introduce the quantifiers
    simp only [qimp_spec_iff] -- eliminate `qimp_spec`
    intro y h
    -- step as ⟨ y1, z1⟩
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
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec
    rintro ⟨y, z⟩ h
    simp at h
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec
    rintro ⟨y1, z1⟩ h
    simp at h
    grind

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- Example with `imp` -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ y _ => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind'
    . apply add2_spec'
    simp -failIfUnchanged only [qimp_spec_uncurry'] -- introduce the quantifiers
    simp only [qimp_spec_iff, curry] -- eliminate `qimp_spec` and `curry`
    simp only [imp] -- eliminate `imp`
    intro y z h0
    -- step as ⟨ y1, z1⟩
    apply spec_mono'
    . apply add2_spec'
    simp -failIfUnchanged only [qimp_uncurry'] -- introduce the quantifiers
    simp only [qimp_iff, curry, uncurry'] -- eliminate `qimp_spec` and `curry`
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

@[simp]
theorem imp_exists_iff {α} (P : α → Prop) (Q : Prop) :
  imp (∃ x, P x) Q ↔ (∀ x, imp (P x) Q) := by
  simp only [imp, forall_exists_index]

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

/- Example with a post-condition manipulating an ∃ -/
example (zero : List Nat → Result (List Nat))
    (zero_spec : ∀ s, zero s ⦃ s' =>
      ∃ (h : s'.length = s.length),
      (∀ i, (_ : i < s.length) → s'[i]'(by grind) = 0) ⦄)
    (s : List Nat) :
    (do
      let _ ← zero s
      pure ()) ⦃ _ => True ⦄ := by
  apply spec_bind'
  · apply zero_spec
  simp -failIfUnchanged only [qimp_spec_iff, imp_exists_iff]
  rintro s' h0 h1
  --
  simp only [pure, spec_ok]


end Aeneas.Std.WP

namespace Aeneas.Std.WP

/-!
# mvcgen
-/

open Std Result
open Std.Do

abbrev postShape : PostShape := (.except (ULift Error) (.except PUnit .pure))

instance Result.instWP : WP Result.{u} postShape where
  wp x := {
    trans Q := match x with | .ok a => Q.1 a | .fail e => Q.2.1 (ULift.up e) | .div => Q.2.2.1 .unit
    conjunctiveRaw Q₁ Q₂ := by
      apply SPred.bientails.of_eq
      cases x <;> simp
  }

abbrev willYield {α : Type u} (r : α) (Q : PostCond α postShape) : Prop := (Q.1 r).down
abbrev willFail {α : Type u} (e : Error) (Q : PostCond α postShape) : Prop := (Q.2.1 (.up e)).down
abbrev willDiverge {α : Type u} (Q : PostCond α postShape) : Prop := (Q.2.2.1 .unit).down

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

instance Result.instWPMonad : WPMonad Result (.except (ULift Error) (.except PUnit .pure)) where
  wp_pure a := by apply PredTrans.ext; intro Q; simp [PredTrans.apply, wp, WP.wp]; rfl
  wp_bind x f := by apply PredTrans.ext; intro Q; simp [PredTrans.apply, wp, WP.wp]; cases x <;> rfl

theorem Result.of_wp {α : Type u} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ (fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e.down)⌝,
                  fun .unit => ⌜P .div⌝, .unit)) → P x := by
  intro hspec
  simp only [WP.wp, PredTrans.apply] at hspec
  split at hspec <;> simp_all

/-- Lift an Aeneas step spec to an mvcgen-compatible `Triple`. -/
theorem spec_to_mvcgen {α : Type u} {x : Result α} {Q : α → Prop}
    (h : spec x Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  obtain ⟨v, hx, hQv⟩ := spec_imp_exists h
  subst hx
  simp [Triple, WP.wp, PredTrans.apply, hQv]

/-- Lift an Aeneas partial-correctness spec to an mvcgen-compatible `Triple`. -/
theorem spec_partial_to_mvcgen {α : Type u} {x : Result α}
    {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : spec_partial x p_ok p_fail p_div)
    {Q : PostCond α postShape}
    (h_ok   : ∀ r, p_ok r → willYield r Q)
    (h_fail : ∀ e, p_fail e → willFail e Q)
    (h_div  : p_div → willDiverge Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ Q ⦄ := by
  cases x
    <;> simp only [spec_partial] at h
    <;> simp [Triple, WP.wp, PredTrans.apply, h_ok, h_fail, h_div, h]

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

theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  have := loop.spec measure inv post body x hBody hInv
  apply this

end Aeneas.Std
