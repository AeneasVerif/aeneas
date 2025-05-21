import Aeneas.Std

namespace Aeneas

-- TODO: make the tree parametric in the type of the action
inductive Action : (α : Type) -> Type 2 where
| Let {α : Type} (x : α) : Action α
--| ReadPtr (addr : Nat) (α : Type) : Action α
--| WritePtr (addr : Nat) {α : Type} (x : α) : Action Unit

inductive Tree (α : Type u) where
| Ret (x: α)
| Fail
| Act {β : Type} (a : Action β) (f : β → Tree α)
| Div
-- Missing: Par (from PulseCore paper)
-- Missing: Tau (necessary?)

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

instance : Lean.Order.PartialOrder (ITree α) := inferInstanceAs (Lean.Order.PartialOrder (FlatOrder (div α)))
  noncomputable instance : CCPO (ITree α) := inferInstanceAs (CCPO (FlatOrder (div α)))
  noncomputable instance : MonoBind ITree where
    bind_mono_left h := by
      cases h
      · sorry
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

structure State where
  -- TODO: want something similar to PulseCore, that is:
  -- - a heap
  -- - a random tape

def run (s : State) (fuel : ℕ) (x : ITree α) : Result (State × α) :=
  match x fuel with
  | .Ret x => .ok (s, x)
  | .Fail => .fail .panic
  | .Div => .div
  | .Act _ _ => sorry

/- For total correctness: -/
def post (hp0 : State → Prop) (x : ITree α) (hp1 : α → State → Prop) (p : α → Prop) : Prop :=
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
  (UScalar.add x y) {{ fun z => z.val = x.val + y.val }} := by
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

def RawPtr := ℕ
axiom ptr {α} : RawPtr → α → HProp

macro:max x:term " ~> " y:term : term => `(ptr $x $y)

open Lean.PrettyPrinter in
@[app_unexpander ptr]
def unexpPtr : Unexpander | `($_ $x $y) => `($x ~> $y) | _ => throw ()

example (x y : RawPtr) (xv yv : ℕ) : HProp := (x ~> xv) * (y ~> yv)

/- fn mut_to_raw<T>(x : &mut T) -> *T -/
axiom mut_to_raw {α} (x : α) : ITree (RawPtr)
axiom mut_to_raw.spec {α} (x : α) : ⦃ ∅ ⦄ (mut_to_raw x) ⦃ fun p => p ~> x ⦄ {{ fun _ => True }}

axiom end_mut_to_raw {α} (p : RawPtr) : ITree α
axiom end_mut_to_raw.spec {α : Type} {x : α} (p : RawPtr) :
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

axiom read_ptr {α : Type} (p : RawPtr) : ITree α
axiom write_ptr {α : Type} (p : RawPtr) (x : α) : ITree Unit

axiom read_ptr.spec {α} {x : α} {p : RawPtr} :
  ⦃ p ~> x ⦄ (read_ptr p) ⦃ fun _ => p ~> x ⦄ {{ fun x' => x' = x }}

axiom write_ptr.spec {α} {x x' : α} {p : RawPtr} :
  ⦃ p ~> x ⦄ (write_ptr p x') ⦃ fun _ => p ~> x' ⦄ {{ fun () => True }}

noncomputable
def incr_ptr (p : RawPtr) : ITree Unit := do
  let x ← read_ptr p
  let x1 ← UScalar.add x 1#u32
  write_ptr p x1

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
axiom entail_ptr (p : RawPtr) (x y : α) : entail (p ~> x) (p ~> y) ↔  x = y

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

theorem mul2_add1.spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :
  pure_post (mul2_add1 x) (fun y => y.val = 2 * x.val + 1) := by
  unfold mul2_add1
  xprogress; intros i hi
  xprogress; intros i' hi'
  scalar_tac

axiom pure.spec (x : α) : pure_post (pure x) (fun y => y = x)

macro_rules
| `(tactic| xlookup) =>
  `(tactic|
    first | apply read_ptr.spec
          | apply write_ptr.spec
          | apply mut_to_raw.spec
          | apply end_mut_to_raw.spec
          | apply pure.spec)

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

def incr_ptr.spec (p : RawPtr) (x : U32) (h : x.val < U32.max) :
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

fn incr_borrow(x : &mut u32) {
  let xp = mut_to_raw(x);
  let xv = *xp;
  let xv = xv + 1;
  *xp = xv
  // borrow expires here (actually, it expires later, but let's skip the details)
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
fn incr_eq_or_disj(x : *u32, y: *u32) {
  let v = *x;
  let v1 = v + 1;
  *y = v1;
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
-/

axiom entail_left (h : p ==> p0) : p ==> (p0 ∨ p1)
axiom entail_right (h : p ==> p1) : p ==> (p0 ∨ p1)

syntax "xleft" : tactic
macro_rules
| `(tactic| xleft) => `(tactic| apply entail_left)

syntax "xright" : tactic
macro_rules
| `(tactic| xright) => `(tactic| apply entail_right)

def eq_or_disj {α} (xp yp : RawPtr) (v : α)
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

theorem read_ptr.spec' {α} {v : α} {xp yp : RawPtr} :
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

theorem write_ptr.spec' {α} {v v' : α} {xp yp : RawPtr} :
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
theorem eq_or_disj_entail_disj {α : Type} {yv : α} (xp yp : RawPtr) :
  (eq_or_disj xp yp yv true) ==> (ex fun (xv : α) => (xp ~> xv) * (yp ~> yv)) := by sorry

noncomputable
def incr_eq_or_disj (x y : RawPtr) : ITree Unit := do
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

axiom entail_post (h0 : p0 ==> p0') (h1 : post p0' x p1 pp) : post p0 x p1 pp

@[simp] axiom entail_refl : p ==> p

theorem incr_eq_or_disj.spec (x y : RawPtr) (v : U32) (hv : v.val < U32.max) :
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

axiom star_symm (x y : HProp) : x * y = y * x

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

end Aeneas
