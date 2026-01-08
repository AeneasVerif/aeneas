import Aeneas.Std.Primitives
import Std.Do

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

@[simp, grind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x := by simp [spec, theta, wp_return]

@[simp, grind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False := by simp [spec, theta]

theorem spec_bind {k:α -> Result β} {Pₖ:Post β} {m:Result α} {Pₘ:Post α} :
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

def imp {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) : Prop :=
  ∀ x, P x → spec (k x) Q

/-- This alternative to `spec_bind` controls the introduction of universal quantifiers with `imp`. -/
theorem spec_bind' {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
  spec m Pₘ →
  (imp Pₘ k Pₖ) →
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

def curry {α β γ} (f : α × β → γ) (x : α) : β → γ := fun y => f (x, y)

/-- We use this lemma to decompose nested `predn` predicates into a sequence of universal quantifiers. -/
@[simp]
def imp_predn {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → Result β) (Q : β → Prop) :
  imp (predn P) k Q ↔ ∀ x, imp (P x) (curry k x) Q := by
  simp [imp, curry]

/-- We use this lemma to eliminate `imp` at the very end -/
def imp_iff {α β} (P : α → Prop) (k : α → Result β) (Q : β → Prop) :
  imp P k Q ↔ ∀ x, P x → spec (k x) Q := by
  simp [imp]

/--
error: unsolved goals
⊢ ∀ (x : Nat), imp (fun y => 0 < x + y) (curry (fun x => ok (x.fst + x.snd)) x) fun z => 0 < z
-/
#guard_msgs in
example : imp (predn fun x y => x + y > 0) (fun (x, y) => .ok (x + y)) (fun z => z > 0) := by
  simp

theorem spec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind

theorem spec_equiv_exists (m:Result α) (P:Post α) :
  spec m P ↔ (∃ y, m = ok y ∧ P y) :=
  by
    cases m
    · simp [spec, theta, wp_return]
    · simp [spec, theta]
    · simp [spec, theta]

theorem spec_imp_exists {m:Result α} {P:Post α} :
  spec m P → (∃ y, m = ok y ∧ P y) := by
  exact (spec_equiv_exists m P).1

theorem exists_imp_spec {m:Result α} {P:Post α} :
  (∃ y, m = ok y ∧ P y) → spec m P := by
  exact (spec_equiv_exists m P).2

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 (name := specSyntax) term:55 " ⦃ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:54 (name := specSyntaxPred) term:55 " ⦃ " term " ⦄" : term

macro_rules
  | `($x ⦃ $r => $P⦄)  => `(Aeneas.Std.WP.spec $x (fun $r => $P))
  | `($x ⦃ $P:term⦄)  => `(Aeneas.Std.WP.spec $x $P)

@[app_unexpander spec]
def unexpSpec : Lean.PrettyPrinter.Unexpander
  | `($_ $e fun $v => $P) | `($_ $e (fun $v => $P)) => `($e ⦃ $v => $P ⦄)
  | `($_ $e $P:term) => `($e ⦃ $P ⦄)
  | _ => throw ()

example : ok 0 ⦃ r => r = 0 ⦄ := by simp
example : spec (ok 0) fun _ => True := by simp
example : ok 0 ⦃ _ => True ⦄ := by simp
example : spec (ok (0, 1)) fun (x, y) => x = 0 ∧ y = 1 := by simp
example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by simp
example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by simp

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

def add2 (x : Nat) := Result.ok (x + 1, x + 2)
theorem  add2_spec (x : Nat) : add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

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
