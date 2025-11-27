import Aeneas.Std

namespace Aeneas

-- TODO: make the tree parametric in the type of the action
inductive Action : (α : Type) -> Type 2 where
| Let {α : Type} (x : α) : Action α
--| ReadPtr (addr : Nat) (α : Type) : Action α
--| WritePtr (addr : Nat) {α : Type} (x : α) : Action Unit

/-
Comes from Coq:
inductive itree (R : Type) (E : Type -> Type) : Type where
  | RetF (r : R)
  | TauF (t : itree R E)
  | VisF {X : Type} (e : E X) (k : X -> itree R E)
-/

namespace Test
  inductive Tree (α : Type) : Type 1 where
  | Ret (x : α)
  | Act {β : Type} (f : β → Tree α)
end Test

inductive Tree (α : Type u) where
| Ret (x: α)
| Fail
| Act {β : Type} (a : Action β) (f : β → Tree α) -- TODO: the continuation introduces to universe issues
| Div
-- Missing: Par (from PulseCore paper)
-- Missing: Tau (necessary?)

/-namespace test
  inductive itreeAux (R : Type) (E : Type -> Type) (itree : Type) : Type where
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : Type} (e : E X) (k : X -> itree)

end test-/

-- TODO: there are universe issues
def ITree (α : Type u) := ℕ → Tree α

open Tree

def bindAux {α : Type u} {β : Type v} (x: ITree α) (f: α → ITree β) (n : ℕ) : Tree β :=
  match n with
  | 0 => Div
  | n + 1 =>
    match x n with
    | .Ret x => f x n
    | .Fail => .Fail
    | .Div => Tree.Div
    | .Act a f' =>
      Tree.Act a (fun x => bindAux (fun _ => f' x) f (n - 1))

def bind {α : Type u} {β : Type v} (x: ITree α) (f: α → ITree β) : ITree β :=
  bindAux x f

-- Allows using ITree in do-blocks
instance : Bind ITree where
  bind := bind

instance : Pure ITree where
  pure := fun x => fun _ => .Ret x

instance : Monad ITree where

def div α : ITree α := fun _ => .Div

section Order

open Lean.Order

-- TODO: change order to take step-indexing into account (don't use FlatOrder)
instance : Lean.Order.PartialOrder (ITree α) := inferInstanceAs (Lean.Order.PartialOrder (FlatOrder (div α)))
noncomputable instance : CCPO (ITree α) := inferInstanceAs (CCPO (FlatOrder (div α)))
noncomputable instance : MonoBind ITree where
  bind_mono_left h := by
    cases h
    · simp [Bind.bind, bind]
      sorry
      --exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    sorry
    /-cases ‹ITree _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl-/

end Order

/- TODO: there are many properties to prove. For instance (and maybe those only work up to
   some equivalence relation):

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

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
-/

open Std

def UScalar.add {ty} (x y : UScalar ty) : ITree (UScalar ty) :=
  match Std.UScalar.add x y with
  | .ok z => fun _ => .Ret z
  | _ => fun _ => .Fail

instance {ty} : HAdd (UScalar ty) (UScalar ty) (ITree (UScalar ty)) where
  hAdd x y := UScalar.add x y

structure State where
  -- TODO: want something similar to PulseCore, that is:
  -- - a heap

/- TODO: we should define the semantics through an inductive, it is more natural
   to model non-deterministic behavior and for doing proofs. It would be nice to
   be able to run tests, though.

   TODO: we need to think about a good model for the heap. RustBelt is interesting
   in that regard. Standard way: map from addresses to blocks, which would probably
   be arrays of (potentially non-initialized) values in our case.

   Note that unless we use a deep-embedding I don't see how we can reason about `transmute`.
   Then how do we add the ghost heap on top of that? How does Iris do that?

   About the concurrent accesses: RustBelt does that (it seems standard?) by adding
   a lock state to the locations, which looks like this (`reading n` means `n` threads
   are doing a non-atomic read while `writing` means a thread is doing a non-atomic write;
   the default is `reading 0`; if attempting to write when the state is `reading (succ n)`
   then we get stuck):
   `inductive LockState where | reading : ℕ → LockState | writing`
-/
def run {α} (s : State) (fuel : ℕ) (x : ITree α) : Result (State × α) :=
  match x fuel with
  | .Ret x => .ok (s, x)
  | .Fail => .fail .panic
  | .Div => .div
  | .Act _ _ => sorry

/- For total correctness: -/
def post {α} (hp0 : State → Prop) (x : ITree α) (hp1 : α → State → Prop) (p : α → Prop) : Prop :=
  ∀ s0, hp0 s0 →
  (∃ n s1 res, run s0 n x = .ok (s1, res)) ∧
  (∀ n s1 res, run s0 n x = .ok (s1, res) →
   hp1 res s1 ∧ p res)

abbrev HProp := State → Prop

def emp : HProp := fun _ => True

notation " ∅ " => emp

@[simp]
def pure_post {α} (x : ITree α) (p : α → Prop) : Prop :=
  post ∅ x (fun _ => ∅) p

macro:max x:term:max " {{ " p:term " }} "    : term => `(pure_post $x $p)

macro:max " ⦃ " p0:term " ⦄" x:term:max " ⦃ " p1:term " ⦄" " {{ " p:term " }} " : term => `(post $p0 $x $p1 $p)

-- TODO: line break?
open Lean.PrettyPrinter in
@[app_unexpander pure_post]
def unexpPurePost : Unexpander | `($_ $x $p) => `($x {{ $p }}) | _ => throw ()

open Lean.PrettyPrinter in
@[app_unexpander post]
def unexpPost : Unexpander | `($_ $p0 $x $p1 $p) => `(⦃ $p0 ⦄ $x ⦃ $p1 ⦄ {{ $p }}) | _ => throw ()

theorem UScalar.add_spec {ty : UScalarTy} (x y : UScalar ty)
  (h : x.val + y.val ≤ UScalar.max ty) :
  (UScalar.add x y) {{ fun z => z.val = x.val + y.val }} :=
  by
  simp [add]
  have ⟨ z, h0, h1 ⟩ := Std.UScalar.add_spec h
  simp [HAdd.hAdd] at h0
  simp [h0, post, emp]
  intros s0
  split_conjs
  . exists 1, s0
    simp [run]
  . intros n s1 res
    simp [run]
    intro hz
    simp_all

theorem pure_post_bind {x : ITree α} {px : α → Prop}
  {f : α → ITree β} {pf : β → Prop}
  (h0 : pure_post x px)
  (h1 : ∀ z, px z → pure_post (f z) pf) :
  pure_post (Bind.bind x f) pf := by sorry

-- TODO: notation for pure_post
theorem pure_post_ret {x : ITree α} {px : α → Prop}
  (h0 : pure_post x px)
  (h1 : ∀ z, px z → px' z) :
  pure_post x px' := by sorry

axiom sep : HProp → HProp → HProp
axiom sep_symm : sep x y = sep y x
axiom sep_assoc : sep (sep x y) z = sep x (sep y z)

axiom mwand : HProp → HProp → HProp
axiom entail : HProp → HProp → Prop

-- TODO: or use HMul?
instance : HMul HProp HProp HProp where
  hMul := sep

--macro:max x:term " * " y:term   : term => `(sep $x $y)
macro:max x:term " -* " y:term : term => `(mwand $x $y)
macro:max x:term " ==> " y:term : term => `(entail $x $y)

open Lean.PrettyPrinter in
@[app_unexpander entail]
def unexpEntail : Unexpander | `($_ $x $y) => `($x ==> $y) | _ => throw ()

open Lean.PrettyPrinter in
@[app_unexpander mwand]
def unexpMWand : Unexpander | `($_ $x $y) => `($x -* $y) | _ => throw ()

example (x y : HProp) : HProp := x -* y

def RawPtr (_ : Type) := ℕ
axiom ptr {α} : RawPtr α → α → HProp

macro:max x:term " ~> " y:term : term => `(ptr $x $y)

open Lean.PrettyPrinter in
@[app_unexpander ptr]
def unexpPtr : Unexpander | `($_ $x $y) => `($x ~> $y) | _ => throw ()

example (x y : RawPtr ℕ) (xv yv : ℕ) : HProp := (x ~> xv) * (y ~> yv)


/-
fn choose<'a, T>(b : bool, x : &'a mut T, y : &'a mut T) -> &'a mut T {
  if b { x } else { y }
}

let x = 0;
let y = 1;
let z = choose(true, &mut x, &mut y);
*z = 2;
assert!(x == 2);
assert!(y == 1);

def choose {T} (b : Bool) (x y : T) : T × (T → (T × T))

fn incr(x : &mut u32) {
  *x = *x + 1;
}

def incr (x : u32) : U32
-/

/- fn mut_to_raw<'a, T>(x : &'a mut T) -> *T -/
axiom mut_to_raw {α} (x : α) : ITree (RawPtr α)
axiom mut_to_raw.spec {α} (x : α) : ⦃ ∅ ⦄ (mut_to_raw x) ⦃ fun p => p ~> x ⦄ {{ fun _ => True }}

/-
def mut_to_raw {α} (x : α) : ITree (RawPtr α × ITree α)
  ⦃ ∅ ⦄
  ⦃ fun (p, back) => p ~> x * (∀ x', ⦃ p ~> x' ⦄ back ⦃ fun x => x = x' ⦄) ⦄

// Rust
let x = 0;
let px = &mut x;
let p = px.mut_to_raw();
*p = 1;
assert!(x == 1);

let x = 0
let px = x
// ∅
let (p, back) ← mut_raw px
// p ~> px
write_ptr p 1
// p ~> 1
let x ← back
// ∅ * pure(x = 1)
massert (x == 1)
-/

axiom end_mut_to_raw {α} (p : RawPtr α) : ITree α
axiom end_mut_to_raw.spec {α : Type} {x : α} (p : RawPtr α) :
  ⦃ p ~> x ⦄ (end_mut_to_raw p) ⦃ fun _ => ∅ ⦄ {{ fun x' => x' = x }}

theorem post_bind {α β : Type} {F : HProp} {x : ITree α}
  {p0 p0' : HProp} {p1' : α → HProp} {pp : α → Prop} {p1 : β → HProp}
  {f : α → ITree β} {pf : β → Prop}
  (h0 : post p0' x p1' pp)
  (h1 : p0 ==> (p0' * F))
  (h2 : ∀ z, pp z → post ((p1' z) * F) (f z) p1 pf) :
  post p0 (Bind.bind x f) p1 pf := by sorry

theorem post_ret {x : ITree α} {p0 p0' : HProp} {p1' : α → HProp} {pp : α → Prop} {p1 : α → HProp}
  {pf : α → Prop}
  (h0 : post p0' x p1' pp)
  (h1 : p0 ==> (p0' * F))
  (h2 : ∀ z, (pp z → (((p1' z) * F) ==> (p1 z)) ∧ pf z)) :
  post p0 x p1 pf := by
  sorry

/-macro_rules
| `(tactic| xprogress) =>
  `(tactic| (first | apply post_bind | apply post_ret); xdischarge)-/

axiom read_ptr {α : Type} (p : RawPtr α) : ITree α
axiom write_ptr {α : Type} (p : RawPtr α) (x : α) : ITree Unit

axiom read_ptr.spec {α} {x : α} {p : RawPtr α} :
  ⦃ p ~> x ⦄ (read_ptr p) ⦃ fun _ => p ~> x ⦄ {{ fun x' => x' = x }}

axiom write_ptr.spec {α} {x x' : α} {p : RawPtr α} :
  ⦃ p ~> x ⦄ (write_ptr p x') ⦃ fun _ => p ~> x' ⦄ {{ fun () => True }}

axiom ex : (α → HProp) → HProp

-- TODO: notation for this (no idea how to make it work)
axiom ex_intro {α} {v : α} (h : ∀ v, ⦃ p0 v ⦄ x ⦃ p1 ⦄ {{ pp }}) :
  ⦃ ex p0 ⦄ x ⦃ p1 ⦄ {{ pp }}

axiom pure_hprop : Prop → HProp

macro:max "⌜" p:term "⌝" : term => `(pure_hprop $p)

axiom pure_intro {α} {v : α} (h : p → ⦃ p0 ⦄ x ⦃ p1 ⦄ {{ pp }}) :
  ⦃ ⌜p⌝ * p0 ⦄ x ⦃ p1 ⦄ {{ pp }}

open Lean.PrettyPrinter in
@[app_unexpander pure_hprop]
def unexpPureHProp : Unexpander | `($_ $x) => `(⌜$x⌝) | _ => throw ()

axiom entail_emp : p ==> (p * emp)

@[simp] axiom emp_sep : (∅ * p) = p
@[simp] axiom sep_emp : (p * ∅) = p

axiom emp_entail_sep : ∅ ==> (∅ * ∅)
axiom p_entail_empty_sep_p : p ==> (∅ * p)
axiom p_entail_p_sep_empty : p ==> (p * ∅)
axiom ptr_sep_entail_ptr_sep : ((p ~> x) * h) ==> ((p ~> x) * h)
axiom ptr_entail_ptr_emp : (p ~> x) ==> ((p ~> x) * ∅)

axiom ptr_sep_ptr_entail_sym : ((px ~> x) * (py ~> y)) ==> ((py ~> y) * (px ~> x))

axiom entail_ex (h : ∃ x, entail p (p' x)) : entail p (ex p')
axiom entail_pure_sep (h : pp ∧ entail p0 p1) : entail p0 (⌜pp⌝ * p1)

@[simp] axiom emp_entail_emp : ∅ ==> ∅

@[simp]
axiom entail_ptr (p : RawPtr α) (x y : α) : entail (p ~> x) (p ~> y) ↔  x = y

syntax "xprogress" : tactic
syntax "xlookup" : tactic
syntax "xdischarge" : tactic
syntax "xframe" : tactic

syntax "xprogress" "with" ident : tactic

macro_rules
| `(tactic| xprogress) =>
  `(tactic| (first | apply post_bind | apply post_ret) <;> (try xlookup) <;> (try xdischarge) <;> (try xframe) <;> simp -failIfUnchanged)

macro_rules
| `(tactic| xprogress with $x) =>
  `(tactic| (first | apply post_bind | apply post_ret) <;> (try apply $x) <;> (try xdischarge) <;> (try xframe) <;> simp -failIfUnchanged)

macro_rules
| `(tactic| xlookup) =>
  `(tactic| apply UScalar.add_spec)

macro_rules
| `(tactic| xdischarge) =>
  `(tactic| scalar_tac)

macro_rules
| `(tactic| xframe) =>
  `(tactic|
    (try simp) <;>
    (first | apply ptr_sep_entail_ptr_sep
           | apply entail_emp
           | apply p_entail_empty_sep_p
           | apply p_entail_p_sep_empty
           | apply ptr_entail_ptr_emp
           | apply ptr_sep_ptr_entail_sym))

axiom hor : HProp → HProp → HProp
macro:max x:term " ∨ " y:term : term => `(hor $x $y)

open Lean.PrettyPrinter in
@[app_unexpander hor]
def unexpHOr : Unexpander | `($_ $x $y) => `($x ∨ $y) | _ => throw ()

axiom or_entail (h0 : p0 ==> p) (h1 : p1 ==> p) : (p0 ∨ p1) ==> p
axiom or_post {p0 p1 : HProp} {p : α → HProp} {pp : α → Prop}
  (h0 : ⦃ p0 ⦄ x ⦃ p ⦄ {{ pp }})
  (h1 : ⦃ p1 ⦄ x ⦃ p ⦄ {{ pp }}) :
  ⦃ hor p0 p1 ⦄ x ⦃ p ⦄ {{ pp }}

syntax "xor" : tactic
macro_rules
| `(tactic| xor) => `(tactic| first | apply or_entail | apply or_post)

axiom pure.spec (x : α) : pure_post (pure x) (fun y => y = x)

macro_rules
| `(tactic| xlookup) =>
  `(tactic|
    first | apply read_ptr.spec
          | apply write_ptr.spec
          | apply mut_to_raw.spec
          | apply end_mut_to_raw.spec
          | apply pure.spec)

axiom entail_left (h : p ==> p0) : p ==> (p0 ∨ p1)
axiom entail_right (h : p ==> p1) : p ==> (p0 ∨ p1)

syntax "xleft" : tactic
macro_rules
| `(tactic| xleft) => `(tactic| apply entail_left)

syntax "xright" : tactic
macro_rules
| `(tactic| xright) => `(tactic| apply entail_right)

axiom entail_post (h0 : p0 ==> p0') (h1 : post p0' x p1 pp) : post p0 x p1 pp

@[simp] axiom entail_refl : p ==> p

axiom star_symm (x y : HProp) : x * y = y * x

axiom ex_post {p0 : β → HProp} {p : α → HProp} {pp : α → Prop}
  (h1 : ∀ y, ⦃ p0 y ⦄ x ⦃ p ⦄ {{ pp }}) :
  ⦃ ex p0 ⦄ x ⦃ p ⦄ {{ pp }}

syntax "xintro" : tactic
macro_rules
| `(tactic| xintro) => `(tactic| first | apply entail_ex; constructor | apply ex_post; intro)

axiom pure_pre_post {p0 : Prop} {p1 : HProp} {p : α → HProp} {pp : α → Prop}
  (h1 : p0 → ⦃ p1 ⦄ x ⦃ p ⦄ {{ pp }}) :
  ⦃ ⌜p0⌝ * p1 ⦄ x ⦃ p ⦄ {{ pp }}

syntax "xpure" : tactic
macro_rules
| `(tactic| xpure) => `(tactic| first | apply entail_pure_sep | apply pure_pre_post; intro)

syntax "xsimp" : tactic
macro_rules
| `(tactic| xsimp) =>
  `(tactic| (repeat (first | xintro | xpure)); simp -failIfUnchanged [*])

/-! # Example of Functions -/

def mul2_add1 (x : U32) : ITree U32 :=
  do
  let i ← UScalar.add x x -- TODO: the + notation doesn't work??
  UScalar.add i 1#u32

def choose {T : Type} (b : Bool) (x : T) (y : T) : ITree (T × (T → (T × T))) :=
  if b
  then let back := fun ret => (ret, y)
       pure (x, back)
  else let back := fun ret => (x, ret)
       pure (y, back)

def loop : ITree Unit := do
  loop
partial_fixpoint

noncomputable
def incr_ptr (p : RawPtr U32) : ITree Unit := do
  let x0 ← read_ptr p
  let x1 ← UScalar.add x0 1#u32
  write_ptr p x1

/-! # Verification of Pure Functions -/

theorem mul2_add1.spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :
  pure_post (mul2_add1 x) (fun y => y.val = 2 * x.val + 1) := by
  unfold mul2_add1
  xprogress; intros i hi
  xprogress; intros i' hi'
  scalar_tac

/-! # Verification of an unsafe function -/

def incr_ptr.spec (p : RawPtr U32) (x : U32) (h : x.val < U32.max) :
  ⦃ p ~> x ⦄
  (incr_ptr p)
  ⦃ fun _ => ex (fun (x' : U32) => ⌜x'.val = x.val + 1⌝ * p ~> x') ⦄ {{ fun () => True }}
  := by
  unfold incr_ptr
  xprogress
  xprogress; intros x1 hx1
  xprogress
  xsimp
  tauto

/-
# Conversion from mutable borrow to raw pointer
TODO: recheck, but I believe it is useful for instance for our allocation patterns.

fn mut_to_raw<T>(x : &mut T) -> *T

fn incr_borrow<'a>(x : &'a mut u32) {
  let xp = mut_to_raw(&mut (*x)); // there is a re-borrow here
  let xv = *xp;
  let xv = xv + 1;
  *xp = xv;
  // re-borrow expires here
}

fn incr_borrow<'a>(x : &'a mut u32) {
  *x += 1;
}
-/

-- This is the model we want Aeneas to generate for `incr_borrow`:
noncomputable
def incr_borrow (x : U32) : ITree U32 := do
  let xp ← mut_to_raw x
  let xv ← read_ptr xp
  let xv1 ← UScalar.add xv 1#u32
  let _ ← write_ptr xp xv1
  end_mut_to_raw xp -- inserted by Aeneas as the backward function for `mut_to_raw`:

theorem incr_borrow.spec (x : U32) (hx : x.val < U32.max) :
  (incr_borrow x) {{ fun y => y.val = x.val + 1 }} := by
  unfold incr_borrow
  xprogress; intros xp
  xprogress
  xprogress; intros xv hxv
  xprogress
  xprogress
  scalar_tac

/-
# Equal or disjoint

unsafe
fn incr_eq_or_disj(src : *u32, dst: *u32) {
  let v = *src;
  let v1 = v + 1;
  *dst = v1;
}

fn incr_eq(x : &mut u32) {
  let xp = mut_to_raw(x);
  incr_eq_or_disj(xp, xp);
}

fn incr_disj(x : &mut u32, y : &mut u32) {
  let xp = mut_to_raw(x);
  let yp = mut_to_raw(y);
  incr_eq_or_disj(xp, yp);
}

fn f(k : &mut Key) { ... }

⦃ inv k ⦄
f k
⦃ inv k ⦄ {{ fun k => k = ... }}

fn split(x: &mut [u32; 2]) -> (&mut u32, &mut u32) {
  let p = as_raw(x);
  let x0 = p;
  let x1 = p + 1;
  // p ~> ...
  let x0 = as_mut x0;
  // ∅
  let x1 = as_mut x1;
  (x0, x1)
}

let split (x : [u32; 2]) -> u32 × u32 × ((u32 → u32 → [u32; 2])) {
  let p = as_raw x
  let x0 = p
  let x1 = p + 1
  ...
}

-/

def eq_or_disj {α} (xp yp : RawPtr α) (v : α)
  (updt : Bool) -- Did we perform an update to yp or not? In the case of slices: we would use an index
  : HProp :=
  -- TODO: we need better notations for this
  if updt then -- The value was updated
    -- Equal
    (⌜yp = xp⌝ * (xp ~> v))
    -- Disjoint
    ∨ (ex (fun (xv : α) => (xp ~> xv) * (yp ~> v)))
  else
    -- Equal
    (⌜yp = xp⌝ * (xp ~> v))
    -- Disjoint
    ∨ (ex (fun (yv : α) => (xp ~> v) * (yp ~> yv)))

theorem read_ptr.spec' {α} {v : α} {xp yp : RawPtr α} :
  ⦃ eq_or_disj xp yp v false ⦄ (read_ptr xp) ⦃ fun _ => eq_or_disj xp yp v false ⦄ {{ fun x => x = v }} := by
  simp [eq_or_disj]
  xor
  . xsimp
    xprogress
    xleft
    xsimp
  . xintro
    xprogress
    xright
    xintro
    xframe

theorem write_ptr.spec' {α} {v v' : α} {xp yp : RawPtr α} :
  ⦃ eq_or_disj xp yp v false ⦄ (write_ptr yp v') ⦃ fun _ => eq_or_disj xp yp v' true ⦄ {{ fun () => True }} := by
  simp [eq_or_disj]
  xor
  . xsimp
    xprogress
    xleft
    xsimp
  . xintro
    xprogress
    xright
    xintro
    xframe

theorem eq_entail_eq_or_disj : (p ~> v) ==> eq_or_disj p p v false := by sorry
theorem disj_entail_eq_or_disj : ((xp ~> xv) * (yp ~> yv)) ==> eq_or_disj xp yp xv false := by sorry

theorem eq_or_disj_entail_eq : (eq_or_disj xp xp xv true) ==> (xp ~> xv) := by sorry
theorem eq_or_disj_entail_disj {α : Type} {yv : α} (xp yp : RawPtr α) :
  (eq_or_disj xp yp yv true) ==> (ex fun (xv : α) => (xp ~> xv) * (yp ~> yv)) := by sorry

noncomputable
def incr_eq_or_disj (x y : RawPtr U32) : ITree Unit := do
  let v ← read_ptr x
  let v1 ← UScalar.add v 1#u32
  write_ptr y v1

noncomputable
def incr_eq (x : U32) : ITree U32 := do
  let xp ← mut_to_raw x
  incr_eq_or_disj xp xp
  end_mut_to_raw xp

noncomputable
def incr_disj (x y : U32) : ITree (U32 × U32) := do
  let xp ← mut_to_raw x
  let yp ← mut_to_raw y
  incr_eq_or_disj xp yp
  let y1 ← end_mut_to_raw yp
  let x1 ← end_mut_to_raw xp
  pure (x1, y1)

theorem incr_eq_or_disj.spec (x y : RawPtr U32) (v : U32) (hv : v.val < U32.max) :
  ⦃ eq_or_disj x y v false ⦄
  (incr_eq_or_disj x y)
  ⦃ fun _ => ex (fun (v' : U32) => (⌜v'.val = v.val + 1⌝) * (eq_or_disj x y v' true)) ⦄
  {{ fun _ => True }} := by
  unfold incr_eq_or_disj
  xprogress with read_ptr.spec'
  xprogress; intros v' hv'
  xprogress with write_ptr.spec'
  xintro
  xsimp
  split_conjs
  . apply hv'
  . simp

theorem incr_eq.spec (x : U32) (hv : x.val < U32.max) :
  (incr_eq x) {{ fun x' => x'.val = x.val + 1 }} := by
  unfold incr_eq
  xprogress; intros xp
  --
  apply entail_post
  apply eq_entail_eq_or_disj
  --
  xprogress with incr_eq_or_disj.spec; scalar_tac
  xsimp; rename_i y hy
  --
  apply entail_post
  apply eq_or_disj_entail_eq
  --
  xprogress
  scalar_tac

theorem incr_disj.spec (x y : U32) (hv : x.val < U32.max) :
  (incr_disj x y) {{ fun (_, y') => y'.val = x.val + 1 }} := by
  unfold incr_disj
  xprogress; intros xp
  xprogress; intros yp
  --
  apply entail_post
  rw [star_symm]
  apply disj_entail_eq_or_disj
  --
  xprogress with incr_eq_or_disj.spec; scalar_tac
  xsimp; rename_i y hy
  --
  apply entail_post
  apply eq_or_disj_entail_disj
  xsimp; rename_i x
  --
  xprogress
  xprogress
  xprogress
  scalar_tac

/-! # Raw pointer to borrow

## Rust
struct CustomBox<T> {
  p: *T,
}

fn CustomBox::new<T>(x : T) -> CustomBox<T> {
  let b = RawPtr::new_uninitialized();
  *b = move x;
}

fn CustomBox::deref_mut<'a>(b : &'a mut CustomBox<T>) -> &'a mut T {
  &mut *b.p
}

## Lean



-/

axiom raw_to_mut (x : RawPtr α) : ITree (α × (α → ITree Unit)) -- TODO: the backward function is stateful!
axiom raw_to_mut_back (x : RawPtr α) (v : α) : ITree Unit

axiom raw_to_mut.spec {x : RawPtr α} :
  ⦃ x ~> v ⦄
  (raw_to_mut x)
  ⦃ fun _ => ∅ ⦄
  {{ fun (v', b) =>
     v' = v ∧
     ∀ v'', ⦃ ∅ ⦄ (b v'') ⦃ fun _ => x ~> v'' ⦄ {{ fun _ => True }} }}

structure CustomBox (α : Type) where
  p : RawPtr α

axiom non_null : RawPtr α → HProp
macro:max p:term " ~> " "∅" : term => `(non_null $p)

-- TODO: line break?
open Lean.PrettyPrinter in
@[app_unexpander non_null]
def unexpNonNull : Unexpander | `($_ $x) => `($x ~> ∅) | _ => throw ()

axiom RawPtr.new_uninitialized (α : Type) : ITree (RawPtr α)
axiom RawPtr.new_uninitialized.spec (α : Type) :
  ⦃ ∅ ⦄
  (RawPtr.new_uninitialized α)
  ⦃ fun p => p ~> ∅ ⦄
  {{ fun _ => True }}

noncomputable
def CustomBox.new (x : T) : ITree (CustomBox T) := do
  let b ← RawPtr.new_uninitialized T
  write_ptr b x
  pure ⟨ b ⟩

-- TODO: is it really what we want?
axiom move_ptr {α : Type} (p : RawPtr α) : ITree α
axiom move_ptr.spec {α : Type} {v : α} (p : RawPtr α) :
  ⦃ p ~> v ⦄
  (move_ptr p)
  ⦃ fun _ => ∅ ⦄
  {{ fun v' => v' = v }}

/- TODO: universe issues with the backward functions
   The problem is that `T` has type `Type` while `T → ITree (CustomBox T)` has type `Type 2`,
   and `Bind.bind` only allows manipulating types belonging to the same universe.
   What should we do? It seems to work if we introduce our own, custom notation for monadic
   let-bindings (see below). In particular, it should be possible to do something quite simple as we
   don't need the full power of the monadic notations of Lean.

noncomputable
def CustomBox.deref_mut' {T : Type} (b : CustomBox T) : ITree (T × (T → ITree (CustomBox T))) := do
  /- The symbolic execution of `&mut *x` is subtle.

     We likely have to introduce an abstraction with no input borrows (i.e.,
     an abstraction which can live as long as we want), and end it eagerly
     when the borrow becomes unusable (it is moved to an anonymous value).

     When creating the borrow, we probably just want a `read_ptr` but which takes
     ownership (so a `move_ptr`?), and when ending the borrow we probably just want
     to use a `write_ptr`.
  -/
  -- ⦃ box b x ⦄ ↔ ⦃ ptr b.p ~> x ⦄
  let (p : T) ← move_ptr b.p -- TYPE MISMATCH: `p` has type `T : Type` but it is expected to have type `?m : Type 2`
  let back := fun x => do
    -- ⦃ p ~> ∅ ⦄
    write_ptr b.p x
    -- ⦃ p ~> x ⦄
    pure b
  -- TODO: we probably need a magic wand? Or not?
  -- Which guarantees are enforced by the translation?
  -- ⦃ p ~> ∅ ⦄ ∧ p = x
  pure (p, back)
-/

-- We can also use a different arrow, such as: ⇐
-- If we use ← we may want to use a scoped notation to prevent conflicts.
macro:max "let " x:ident " ← " e:term "; " f:term : term => `(bind $e (fun $x => $f))

noncomputable
def test (px py : RawPtr ℕ) : ITree ℕ :=
  let x ← read_ptr px;
  let y ← read_ptr py;
  if x < y then
    let x' ← pure x;
    pure x'
  else
    pure y

-- TODO: unexpander
#print test

noncomputable
def CustomBox.deref_mut {T : Type} (b : CustomBox T) : ITree (T × (T → ITree (CustomBox T))) :=
  /- The symbolic execution of `&mut *x` is subtle.

     We likely have to introduce an abstraction with no input borrows (i.e.,
     an abstraction which can live as long as we want), and end it eagerly
     when the borrow becomes unusable (it is moved to an anonymous value).

     When creating the borrow, we probably just want a `read_ptr` but which takes
     ownership (so a `move_ptr`?), and when ending the borrow we probably just want
     to use a `write_ptr`.
  -/
  -- ⦃ box b x ⦄ ↔ ⦃ ptr b.p ~> x ⦄
  let p ← move_ptr b.p;
  let back := fun x => do
    -- ⦃ p ~> ∅ ⦄
    write_ptr b.p x
    -- ⦃ p ~> x ⦄
    pure b
  -- TODO: we probably need a magic wand? Or not?
  -- Which guarantees are enforced by the translation?
  -- ⦃ p ~> ∅ ⦄ ∧ p = x
  pure (p, back)

/- # Shallow view of a data-type

# In Rust

#[aeneas::type_view(T)] // or: #[aeneas::type_view(ShallowBox<T>)]
struct CustomBox<T> {
  p: *T, // fields must be private
}

fn CustomBox::new<T>(x : T) -> CustomBox<T> {
  let b = RawPtr::new_uninitialized();
  *b = move x;
}

fn CustomBox::deref_mut(b : &mut CustomBox<T>) -> &mut T {
  &mut *x
}

# In Lean

## Deep Model:

struct Deep.CustomBox T where
  p : RawPtr T

## Shallow Model:

abbrev Shallow.CustomBox T := T

## Deep Functions

def CustomBox.new {T} (x : T) : ITree (Shallow.CustomBox T) := do
  -- ⦃ ∅ ⦄
  let b ← new_uninitialized T
  -- ⦃ ptr b ~> ∅ ⦄
  write_ptr b x
  -- ⦃ ptr b ~> x ⦄
  let bv ← CustomBox.get_view b -- the view is user defined
  -- ⦃ ptr b ~> x * ⌜bv = x⌝⦄
  close_inv CustomBox.inv b bv -- the inv is user defined
  -- ⦃ ⌜bv = x⌝ ⦄
  pure bv

-/


/-
# Self-Ref

use std::ptr::NonNull;

// Invariant:
// ⦃ alloc ~> ∅ *  ⦄
struct S {
    /// Uniqueness of pointer enforced if Box<[u32]>?
    /// Being debated...
    alloc : NonNull<[u32]>,
    /// & *self.alloc mut [u32]
    x : *mut [u32],
}

fn alloc() -> S {
    let b = Box::new([0; 32];
    // b -> [0; 32]
    let alloc = Box::into_non_null(move b);
    // ⦃ alloc ~> b ⦄
    let x = unsafe { &raw mut *alloc.as_ptr() };
    // ⦃ alloc ~> ∅ * x ~> b.to_slice ⦄
    S { alloc, x }
}

fn free(s : S) {
    unsafe {
        Box::from_non_null(s.alloc);
    }
}

fn main() {
    let mut s = alloc();
    let p = unsafe { s.x.as_mut() };

    println!("Hello, world!");
}

-/

/-! # TODO: Interior Mutability (Cell)

-/

/-! # TODO: Higher-Order Predicates (`Rc<RefCell<T>>`)

-/

/-! # TODO: Transmute?
This is hard because we likely need a deep-embedding of the types, as well as layout information,
so I'm not sure we can do anything about it. For now, the use-case I have in mind is the custom
allocator, even though in the case of cryptographic applications we might manage to make it work
by allocating arrays of u8 then doing safer conversions. So maybe it's not really necessary for
what we want to do.

Remark: when using deep models and shallow models we might actually want to switch between a deep
embedding and a shallow embedding, but: 1. reasoning about deep embeddings is really really hard,
2. this is basically tantamount to redoing (something even bigger than) RustBelt, which is definitely
not something we want to do.
-/

/-! # Concurrent semantics
TODO: memory accesses?
How to model the fact that we may want to access different *cells* of an array concurrently?
One issue when reasoning about non-concurrent accesses is that reads and writes are non-atomic
in many situations (for instance, reading from a structure). We need to model that!

-/

/-! # Mutable Iterator for Doubly Linked List -/

/-
let p = null;
if b {
  p = malloc(...);
}

if b {
  // p ~> x
  free(p);
}
-/

/- # Remarks:

In RustBelt it is possible to change the type of a pointer by writing to it,
provided the types have the same size. Is it really needed in our case?
RustBelt needs it because it is a type system and needs to perform strong
updates.
For instance:

let x = new(1);
// x : own ∅
*x = 1;
// x : own int

RustBelt: the rule `C-Reborrow` allows to reborrow a reference. Is it
possible to reborrow "deeply"? i.e.: &mut **x
I also note that *x is not a path in RustBelt.
Answer: it works through rules `S-Deref-Bor-Mut` and others, which allow
dereferencing a reference whose inner type is not `Copy`. But I don't fully
understand this rule: it seems we have to end the reborrow at the same
time as the outer borrow. I guess we have to reborrow the outer reference first?

`Send` and `Sync`? Do we need to explicitly model and reason about them?

`C-Split-Own` allows splitting a `p ◃ own ∏τ` to `∏ p.m ◃ own τ`

`F-Equalize` is needed to typecheck the problem #3 from Niko Matsakis' blog
post on non-lexical lifetimes. (this rule is probably very similar to merging
region abstractions)

What happens if we have a copiable stateful type, which contains a non copyable
type? Something like `Rc<Box<T>>`? (is `Rc` copyable?)

In RustBelt, ownership is thread relative. A type is `Send` if its predicate
`OWN` does not depend on the thread id.

**Timeless** propositions.

About atomic vs non-atomic accesses in RustBelt (p134):
by some protocol that is enforced by an invariant, and it is
the invariant that owns the memory."

The CAS rule only works for integers and locations, which makes sense.

The product × uses separating conjunction (p135). It seems to imply that
the cells are not adjacent in memory? But ok if used in conjunction with
another type like `own`, which enforces that there exists a location `l`
which maps to a list of values, which must thus be adjacent in memory.

The `own` predicate uses the later modality.

The lifetime logic provides a nice way of handling the shared references:
shared references use fractional permission, and it can be annoying to keep
track of the fractions of permissions; reasoning about the lifetime provides
a more uniform treatment of that. But actually we need to use lifetime tokens
to prove that a lifetime is still live, and those use fractional permissions
I think. But yet, useful because we can split borrows into smaller borrows,
while using the same lifetime for all of them.

`LftL-Borrow`: there is a later on the left. A note says that otherwise there
are unsoundnesses with impredicativity. (but of course ok if the predicate
is timeless)

`LftL-bor-split`: split a borrow of `P * Q` into borrows of `P` and `Q`.
Useful for instance to split a slice.

`LftL-Tok-Inter`: when is that necessary?

`LftL-bor-acc`: the lifetime token is consumed (and lost)? But then it prevents
us from using the viewshift in `LftL-Begin` to introduce a dead lifetime token?
There is probably a way of reverting back (hidden in the rules for the α operator).

Full borrows require higher-order ghost state (note 20 p149).

What happens if we put a borrow in a `Mutex` or a `RwLock` (or a `Cell`)?

The definition of atomic borrows (p150) contains an invariant.

Namespaces.

-/

#check Vector.ofFn

def MyArray.ofFn {n} (f : Fin n → α) : Array α := go 0 (Array.emptyWithCapacity n) where
  /-- Auxiliary for `ofFn`. `ofFn.go f i acc = acc ++ #[f i, ..., f(n - 1)]` -/
  @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < n then go (i+1) (acc.push (f ⟨i, h⟩)) else acc
  decreasing_by simp_wf; decreasing_trivial_pre_omega

/- Testing what happens with recursive types -/
inductive PtrTree (α : Type) where
| Leaf (x : α)
| Node (children : List (RawPtr (PtrTree α)))

end Aeneas
