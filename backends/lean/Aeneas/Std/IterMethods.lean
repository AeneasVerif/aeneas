/- Models of the `Iterator` methods `map`, `flatten`, `position` and `find_map`, the
   `slice::Iter` overrides of the last two, and the list-level semantics of `next` that
   their specifications, and those of `fold`, `rev` and `collect`, are stated with. -/
module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public import Aeneas.Std.Alloc.Vec.IntoIter
public section

@[expose] section

namespace Aeneas.Std

open Result WP

/-! ## List-level semantics of `next` -/

/-- `Advances next s l s'`: calling `next` on `s` returns the items of `l` in order, without
    returning `none` before the last one, and leaves the iterator in state `s'`. -/
def core.iter.traits.iterator.Advances {Self Item : Type _}
    (next : Self → Result ((Option Item) × Self)) : Self → List Item → Self → Prop
  | s, [], s' => s' = s
  | s, x :: xs, s' =>
    ∃ s1, next s = ok (some x, s1) ∧ core.iter.traits.iterator.Advances next s1 xs s'

/-- `Yields next s l s'`: `next` returns the items of `l` in order from `s`, then `none`, and
    the iterator ends in state `s'`. This is how an iterator is related to the list it
    stands for in the specifications of its consumers and adapters. -/
def core.iter.traits.iterator.Yields {Self Item : Type _}
    (next : Self → Result ((Option Item) × Self)) (s : Self) (l : List Item) (s' : Self) : Prop :=
  ∃ s1, core.iter.traits.iterator.Advances next s l s1 ∧ next s1 = ok (none, s')

theorem core.iter.traits.iterator.Yields.nil_iff {Self Item : Type _}
    (next : Self → Result ((Option Item) × Self)) (s s' : Self) :
    core.iter.traits.iterator.Yields next s [] s' ↔ next s = ok (none, s') := by
  simp [core.iter.traits.iterator.Yields, core.iter.traits.iterator.Advances]

theorem core.iter.traits.iterator.Yields.cons_iff {Self Item : Type _}
    (next : Self → Result ((Option Item) × Self)) (s s' : Self) (x : Item) (xs : List Item) :
    core.iter.traits.iterator.Yields next s (x :: xs) s' ↔
      ∃ s1, next s = ok (some x, s1) ∧ core.iter.traits.iterator.Yields next s1 xs s' := by
  simp only [core.iter.traits.iterator.Yields, core.iter.traits.iterator.Advances]
  constructor
  · rintro ⟨s2, ⟨s1, h1, h2⟩, h3⟩; exact ⟨s1, h1, s2, h2, h3⟩
  · rintro ⟨s1, h1, s2, h2, h3⟩; exact ⟨s2, ⟨s1, h1, h2⟩, h3⟩

/-- Two states whose `next` agrees yield the same lists. -/
theorem core.iter.traits.iterator.Yields.of_next_eq {Self Item : Type _}
    (next : Self → Result ((Option Item) × Self)) (s s0 t : Self) (l : List Item)
    (h : next s = next s0) (hy : core.iter.traits.iterator.Yields next s0 l t) :
    core.iter.traits.iterator.Yields next s l t := by
  cases l with
  | nil =>
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy ⊢
    rw [h]; exact hy
  | cons x xs =>
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    rw [core.iter.traits.iterator.Yields.cons_iff]
    exact ⟨s1, by rw [h]; exact hn, hy1⟩

/-- `CallsMut inst f args outs f'`: calling the closure `f` through `inst.call_mut` on the
    arguments `args` in order returns `outs` and leaves the closure in state `f'`. For a
    pure closure the outputs are the `List.map` of its function, see `CallsMut.of_pure`. -/
def core.iter.traits.iterator.CallsMut {F Args B : Type _}
    (inst : core.ops.function.FnMut F Args B) : F → List Args → List B → F → Prop
  | f, [], bs, f' => bs = [] ∧ f' = f
  | f, x :: xs, bs, f'' =>
    ∃ b f1 bs', inst.call_mut f x = ok (b, f1) ∧
      core.iter.traits.iterator.CallsMut inst f1 xs bs' f'' ∧ bs = b :: bs'

theorem core.iter.traits.iterator.CallsMut.of_pure {F Args B : Type _}
    (inst : core.ops.function.FnMut F Args B) (g : Args → B)
    (h : ∀ f x, inst.call_mut f x = ok (g x, f)) :
    ∀ (f : F) (l : List Args), core.iter.traits.iterator.CallsMut inst f l (l.map g) f := by
  intro f l
  induction l with
  | nil => simp [core.iter.traits.iterator.CallsMut]
  | cons x xs ih =>
    simp only [core.iter.traits.iterator.CallsMut, List.map_cons]
    exact ⟨g x, f, xs.map g, h f x, ih, rfl⟩

/-- The default `fold` over an iterator that yields `l` is the monadic left fold of the closure
    over `l`, threading the closure's state. -/
theorem core.iter.traits.iterator.Iterator.fold.default.loop.eq_foldlM_of_yields
    {Self Item Acc F : Type _}
    (next : Self → Result ((Option Item) × Self))
    (FnMutInst : core.ops.function.FnMut F (Acc × Item) Acc) :
    ∀ (l : List Item) (self : Self) (init : Acc) (f : F) (self' : Self),
      core.iter.traits.iterator.Yields next self l self' →
      core.iter.traits.iterator.Iterator.fold.default.loop next FnMutInst self init f =
        (do
          let s ← l.foldlM (fun (s : Acc × F) x => FnMutInst.call_mut s.2 (s.1, x)) (init, f)
          ok s.1) := by
  intro l
  induction l with
  | nil =>
    intro self init f self' h
    rw [core.iter.traits.iterator.Yields.nil_iff] at h
    unfold core.iter.traits.iterator.Iterator.fold.default.loop
    rw [Aeneas.Std.loop]
    simp [core.iter.traits.iterator.Iterator.fold.default.body, h]
    show ok init = Std.bind (ok (init, f)) (fun s => ok s.1)
    simp
  | cons x xs ih =>
    intro self init f self' h
    obtain ⟨s1, hn, hy⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 h
    unfold core.iter.traits.iterator.Iterator.fold.default.loop
    rw [Aeneas.Std.loop]
    simp [core.iter.traits.iterator.Iterator.fold.default.body, hn, uncurry, Std.bind_tc_eq,
      Std.bind_assoc]
    congr 1
    funext p
    exact ih s1 p.1 p.2 self' hy

/-! ## `map` -/

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.trait_default
  {Self B F Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Item)
  (_FnMutInst : core.ops.function.FnMut F Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F) :=
  core.iter.traits.iterator.Iterator.map.default

/-- `Map<I, F>::next` (`map.rs`): `self.iter.next().map(&mut self.f)`. The closure state is
    threaded through each call. -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  {B I F Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item)
  (FnMutInst : core.ops.function.FnMut F Item B) :
  core.iter.adapters.map.Map I F →
    Result ((Option B) × core.iter.adapters.map.Map I F) :=
  fun self => do
    let (o, iter) ← IteratorInst.next self.iter
    match o with
    | none => ok (none, ⟨iter, self.f⟩)
    | some x => do
      let (b, f) ← FnMutInst.call_mut self.f x
      ok (some b, ⟨iter, f⟩)

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>"]
impl_def core.iter.traits.iterator.IteratorMap {B I F Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (FnMutInst : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B := {
  next := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    IteratorInst FnMutInst
}

@[step]
theorem core.iter.traits.iterator.Iterator.map.default.spec
    {Self F : Type _} (self : Self) (f : F) :
    core.iter.traits.iterator.Iterator.map.default self f
    ⦃ m => m.iter = self ∧ m.f = f ⦄ := by
  simp [core.iter.traits.iterator.Iterator.map.default, WP.spec_ok]

@[step]
theorem core.iter.traits.iterator.Iterator.map.trait_default.spec
    {Self B F Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (FnMutInst : core.ops.function.FnMut F Item B) (self : Self) (f : F) :
    core.iter.traits.iterator.Iterator.map.trait_default IteratorInst FnMutInst self f
    ⦃ m => m.iter = self ∧ m.f = f ⦄ :=
  core.iter.traits.iterator.Iterator.map.default.spec self f

/-- One step of `Map::next`: the inner iterator is advanced; on an item the closure runs on it. -/
@[step]
theorem core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next.spec
    {B I F Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (FnMutInst : core.ops.function.FnMut F Item B)
    (m : core.iter.adapters.map.Map I F)
    (nextPost : Option Item × I → Prop)
    (callPost : Item → B × F → Prop)
    (hnext : IteratorInst.next m.iter ⦃ nextPost ⦄)
    (hcall : ∀ x it, nextPost (some x, it) → FnMutInst.call_mut m.f x ⦃ callPost x ⦄) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      IteratorInst FnMutInst m
    ⦃ r => ∃ o it, nextPost (o, it) ∧
      match o with
      | none => r = (none, ⟨it, m.f⟩)
      | some x => ∃ b f, callPost x (b, f) ∧ r = (some b, ⟨it, f⟩) ⦄ := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  apply WP.spec_bind hnext
  intro ⟨o, it⟩ ho
  cases o with
  | none =>
    simp only [uncurry, WP.spec_ok]
    exact ⟨none, it, ho, rfl⟩
  | some x =>
    simp only [uncurry]
    apply WP.spec_bind (hcall x it ho)
    intro ⟨b, f⟩ hbf
    simp only [uncurry, WP.spec_ok]
    exact ⟨some x, it, ho, b, f, hbf, rfl⟩

/-- `map` yields the closure's results on the items of the inner iterator, in order
(`List.map` when the closure is pure, see `CallsMut.of_pure`). -/
theorem core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next.yields
    {B I F Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (FnMutInst : core.ops.function.FnMut F Item B) :
    ∀ (l : List Item) (it it' : I) (f f' : F) (bs : List B),
      core.iter.traits.iterator.Yields IteratorInst.next it l it' →
      core.iter.traits.iterator.CallsMut FnMutInst f l bs f' →
      core.iter.traits.iterator.Yields
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
          IteratorInst FnMutInst) ⟨it, f⟩ bs ⟨it', f'⟩ := by
  intro l
  induction l with
  | nil =>
    intro it it' f f' bs hy hc
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy
    simp only [core.iter.traits.iterator.CallsMut] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [core.iter.traits.iterator.Yields.nil_iff]
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next, hy]
  | cons x xs ih =>
    intro it it' f f' bs hy hc
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    simp only [core.iter.traits.iterator.CallsMut] at hc
    obtain ⟨b, f1, bs', hcall, hrest, rfl⟩ := hc
    rw [core.iter.traits.iterator.Yields.cons_iff]
    refine ⟨⟨s1, f1⟩, ?_, ih s1 it' f1 f' bs' hy1 hrest⟩
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next, hn, hcall]

/-! ## `Rev` -/

/-- `rev` yields the items the inner `next_back` yields, in the same order: for a slice
iterator these are the remaining elements reversed, see
`IteratorSliceIter.next_back.yields`. -/
theorem core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next.yields
    {I Item : Type _} (DEInst : core.iter.traits.double_ended.DoubleEndedIterator I Item) :
    ∀ (l : List Item) (it it' : I),
      core.iter.traits.iterator.Yields DEInst.next_back it l it' →
      core.iter.traits.iterator.Yields
        (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next DEInst)
        ⟨it⟩ l ⟨it'⟩ := by
  intro l
  induction l with
  | nil =>
    intro it it' hy
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy ⊢
    simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next, hy]
  | cons x xs ih =>
    intro it it' hy
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    rw [core.iter.traits.iterator.Yields.cons_iff]
    refine ⟨⟨s1⟩, ?_, ih s1 it' hy1⟩
    simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next, hn]

/-! ## `position` and `find_map` -/

/-- One step of the default `Iterator::position` (`iterator.rs`, via `try_fold`): the state is
    the iterator, the index of the next item and the predicate. The index is incremented with
    overflow checks, as the standard library does under `rustc_inherit_overflow_checks`. -/
def core.iter.traits.iterator.Iterator.position.default.body
  {Self Item P : Type _}
  (next : Self → Result ((Option Item) × Self))
  (FnMutInst : core.ops.function.FnMut P Item Bool) :
  (Self × Usize × P) → Result (ControlFlow (Self × Usize × P) ((Option Usize) × Self))
  | (self, i, p) => do
    let (o, self1) ← next self
    match o with
    | none => ok (.done (none, self1))
    | some x => do
      let (b, p1) ← FnMutInst.call_mut p x
      if b then ok (.done (some i, self1))
      else do
        let i1 ← i + 1#usize
        ok (.cont (self1, i1, p1))

def core.iter.traits.iterator.Iterator.position.default.loop
  {Self Item P : Type _}
  (next : Self → Result ((Option Item) × Self))
  (FnMutInst : core.ops.function.FnMut P Item Bool)
  (self : Self) (p : P) : Result ((Option Usize) × Self) :=
  Aeneas.Std.loop (core.iter.traits.iterator.Iterator.position.default.body next FnMutInst)
    (self, 0#usize, p)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::position"]
def core.iter.traits.iterator.Iterator.position.trait_default
  {Self P Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
  (FnMutInst : core.ops.function.FnMut P Item Bool)
  (self : Self) (p : P) : Result ((Option Usize) × Self) :=
  core.iter.traits.iterator.Iterator.position.default.loop IteratorInst.next FnMutInst self p

/-- One step of the default `Iterator::find_map`: stops at the first item the closure maps to
    `some`. The iterator is advanced past that item. -/
def core.iter.traits.iterator.Iterator.find_map.default.body
  {Self Item B F : Type _}
  (next : Self → Result ((Option Item) × Self))
  (FnMutInst : core.ops.function.FnMut F Item (Option B)) :
  (Self × F) → Result (ControlFlow (Self × F) ((Option B) × Self))
  | (self, f) => do
    let (o, self1) ← next self
    match o with
    | none => ok (.done (none, self1))
    | some x => do
      let (r, f1) ← FnMutInst.call_mut f x
      match r with
      | some b => ok (.done (some b, self1))
      | none => ok (.cont (self1, f1))

def core.iter.traits.iterator.Iterator.find_map.default.loop
  {Self Item B F : Type _}
  (next : Self → Result ((Option Item) × Self))
  (FnMutInst : core.ops.function.FnMut F Item (Option B))
  (self : Self) (f : F) : Result ((Option B) × Self) :=
  Aeneas.Std.loop (core.iter.traits.iterator.Iterator.find_map.default.body next FnMutInst)
    (self, f)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find_map"]
def core.iter.traits.iterator.Iterator.find_map.trait_default
  {Self B F Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
  (FnMutInst : core.ops.function.FnMut F Item (Option B))
  (self : Self) (f : F) : Result ((Option B) × Self) :=
  core.iter.traits.iterator.Iterator.find_map.default.loop IteratorInst.next FnMutInst self f

/-- `position` from the index `i`, over an iterator that yields `l`, with a closure that is the
    pure predicate `g`: the result is `List.findIdx?` shifted by `i`, and the iterator has
    consumed the items up to and including the match. -/
theorem core.iter.traits.iterator.Iterator.position.default.loop_from.spec
    {Self Item P : Type _}
    (next : Self → Result ((Option Item) × Self))
    (FnMutInst : core.ops.function.FnMut P Item Bool) (g : Item → Bool) :
    ∀ (l : List Item) (self : Self) (i : Usize) (p : P) (self' : Self),
      core.iter.traits.iterator.Yields next self l self' →
      (∀ p x, x ∈ l → FnMutInst.call_mut p x = ok (g x, p)) →
      i.val + l.length ≤ Usize.max →
      Aeneas.Std.loop
          (core.iter.traits.iterator.Iterator.position.default.body next FnMutInst)
          (self, i, p)
        ⦃ r => r.1.map (·.val) = (l.findIdx? g).map (· + i.val) ∧
          match l.findIdx? g with
          | none => r.2 = self'
          | some k => core.iter.traits.iterator.Advances next self (l.take (k + 1)) r.2 ⦄ := by
  intro l
  induction l with
  | nil =>
    intro self i p self' hy _ _
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy
    rw [Aeneas.Std.loop]
    simp [core.iter.traits.iterator.Iterator.position.default.body, hy, uncurry]
  | cons x xs ih =>
    intro self i p self' hy hg hlen
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    have hx := hg p x (by simp)
    rw [Aeneas.Std.loop]
    cases hgx : g x with
    | true =>
      simp [core.iter.traits.iterator.Iterator.position.default.body, hn, hx, hgx, uncurry,
        List.findIdx?_cons, core.iter.traits.iterator.Advances]
    | false =>
      simp [core.iter.traits.iterator.Iterator.position.default.body, hn, hx, hgx, uncurry,
        List.findIdx?_cons]
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by simp at hlen ⊢; scalar_tac))
      intro i1 hv
      have hv' : i1.val = i.val + 1 := by simpa using hv
      apply WP.spec_mono (ih s1 i1 p self' hy1 (fun p y hy => hg p y (by simp [hy]))
        (by simp at hlen; omega))
      rintro r ⟨hr1, hr2⟩
      refine ⟨?_, ?_⟩
      · cases hk : xs.findIdx? g with
        | none => simp [hk] at hr1 ⊢; exact hr1
        | some k =>
          simp [hk] at hr1 ⊢
          obtain ⟨a, ha, hav⟩ := hr1
          exact ⟨a, ha, by omega⟩
      · cases hk : xs.findIdx? g with
        | none => simp [hk] at hr2 ⊢; exact hr2
        | some k =>
          simp [hk, core.iter.traits.iterator.Advances] at hr2 ⊢
          exact ⟨s1, hn, hr2⟩

/-- `find_map` over an iterator that yields `l`, with a closure that is the pure function `g`:
    the result is `List.findSome?`, and the iterator has consumed the items up to and
    including the first one `g` maps to `some`. -/
theorem core.iter.traits.iterator.Iterator.find_map.default.loop.spec
    {Self Item B F : Type _}
    (next : Self → Result ((Option Item) × Self))
    (FnMutInst : core.ops.function.FnMut F Item (Option B)) (g : Item → Option B) :
    ∀ (l : List Item) (self : Self) (f : F) (self' : Self),
      core.iter.traits.iterator.Yields next self l self' →
      (∀ f x, x ∈ l → FnMutInst.call_mut f x = ok (g x, f)) →
      Aeneas.Std.loop
          (core.iter.traits.iterator.Iterator.find_map.default.body next FnMutInst) (self, f)
        ⦃ r => r.1 = l.findSome? g ∧
          match l.findIdx? (fun x => (g x).isSome) with
          | none => r.2 = self'
          | some k => core.iter.traits.iterator.Advances next self (l.take (k + 1)) r.2 ⦄ := by
  intro l
  induction l with
  | nil =>
    intro self f self' hy _
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy
    rw [Aeneas.Std.loop]
    simp [core.iter.traits.iterator.Iterator.find_map.default.body, hy, uncurry]
  | cons x xs ih =>
    intro self f self' hy hg
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    have hx := hg f x (by simp)
    rw [Aeneas.Std.loop]
    cases hgx : g x with
    | some b =>
      simp [core.iter.traits.iterator.Iterator.find_map.default.body, hn, hx, hgx, uncurry,
        List.findIdx?_cons, core.iter.traits.iterator.Advances]
    | none =>
      simp [core.iter.traits.iterator.Iterator.find_map.default.body, hn, hx, hgx, uncurry,
        List.findIdx?_cons]
      apply WP.spec_mono (ih s1 f self' hy1 (fun p y hy => hg p y (by simp [hy])))
      rintro r ⟨hr1, hr2⟩
      refine ⟨hr1, ?_⟩
      cases hk : xs.findIdx? (fun x => (g x).isSome) with
      | none => simp [hk] at hr2 ⊢; exact hr2
      | some k =>
        simp [hk, core.iter.traits.iterator.Advances] at hr2 ⊢
        exact ⟨s1, hn, hr2⟩

/-! ## Collect -/

/-- A successful specification turns into an equation: the computation returns a value. -/
theorem WP.spec_exists_ok {α : Type _} {m : Result α} {p : α → Prop} (h : m ⦃ p ⦄) :
    ∃ y, m = ok y ∧ p y := by
  cases m with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

theorem alloc.vec.FromIteratorVec.iterToList.eq_of_yields
    {T IntoIter : Type _}
    (iterInst : core.iter.traits.iterator.Iterator IntoIter T) :
    ∀ (l : List T) (iter iter' : IntoIter) (acc : List T),
      core.iter.traits.iterator.Yields iterInst.next iter l iter' →
      alloc.vec.FromIteratorVec.iterToList iterInst iter acc = ok (acc.reverse ++ l) := by
  intro l
  induction l with
  | nil =>
    intro iter iter' acc hy
    rw [core.iter.traits.iterator.Yields.nil_iff] at hy
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp [hy]
  | cons x xs ih =>
    intro iter iter' acc hy
    obtain ⟨s1, hn, hy1⟩ := (core.iter.traits.iterator.Yields.cons_iff _ _ _ _ _).1 hy
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp [hn, ih s1 iter' (x :: acc) hy1]

/-- `from_iter` into a `Vec` returns exactly the items the iterator yields. -/
theorem alloc.vec.FromIteratorVec.from_iter.spec
    {T I IntoIter : Type _}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter)
    (input : I) (j j' : IntoIter) (l : List T)
    (hj : IntoIteratorInst.into_iter input = ok j)
    (hy : core.iter.traits.iterator.Yields IntoIteratorInst.iteratorInst.next j l j')
    (hlen : l.length ≤ Usize.max) :
    alloc.vec.FromIteratorVec.from_iter IntoIteratorInst input ⦃ v => v.val = l ⦄ := by
  unfold alloc.vec.FromIteratorVec.from_iter
  simp [hj, alloc.vec.FromIteratorVec.iterToList.eq_of_yields _ l j j' [] hy, hlen]

/-- `collect::<Vec<_>>()` returns exactly the items the iterator yields. -/
theorem core.iter.traits.iterator.Iterator.collect.default.spec_vec
    {Self T : Type} (IteratorInst : core.iter.traits.iterator.Iterator Self T)
    (self self' : Self) (l : List T)
    (hy : core.iter.traits.iterator.Yields IteratorInst.next self l self')
    (hlen : l.length ≤ Usize.max) :
    core.iter.traits.iterator.Iterator.collect.default IteratorInst
      (core.iter.traits.collect.FromIteratorVec T) self ⦃ v => v.val = l ⦄ := by
  unfold core.iter.traits.iterator.Iterator.collect.default core.iter.traits.collect.FromIteratorVec
  exact alloc.vec.FromIteratorVec.from_iter.spec
    (core.iter.traits.collect.IntoIterator.Blanket IteratorInst) self self self' l
    (by simp [core.iter.traits.collect.IntoIterator.Blanket.into_iter]) hy hlen

/-! ## Slice iterators -/

/-- A slice iterator yields the elements from its index on. -/
theorem core.slice.iter.IteratorSliceIter.next.yields {T : Type _} :
    ∀ (k : Nat) (it : core.slice.iter.Iter T), it.i + k = it.slice.val.length →
      core.iter.traits.iterator.Yields core.slice.iter.IteratorSliceIter.next it
        (it.slice.val.drop it.i) { it with i := it.slice.val.length } := by
  intro k
  induction k with
  | zero =>
    intro it h
    have hge : ¬ it.i < it.slice.val.length := by omega
    have hdrop : it.slice.val.drop it.i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, core.iter.traits.iterator.Yields.nil_iff]
    obtain ⟨s, i⟩ := it
    have hi : i = s.val.length := by simp at h; omega
    simp_all [core.slice.iter.IteratorSliceIter.next]
  | succ k ih =>
    intro it h
    have hlt : it.i < it.slice.val.length := by omega
    have hdrop : it.slice.val.drop it.i =
        it.slice.val[it.i] :: it.slice.val.drop (it.i + 1) := List.drop_eq_getElem_cons hlt
    rw [hdrop, core.iter.traits.iterator.Yields.cons_iff]
    obtain ⟨r, hr, hpost⟩ := WP.spec_exists_ok
      (core.slice.iter.IteratorSliceIter.next.spec it)
    simp only [hlt, dite_true] at hpost
    refine ⟨{ it with i := it.i + 1 }, by rw [hr, hpost], ?_⟩
    exact ih { it with i := it.i + 1 } (by simp; omega)

/-- `next_back` on a slice iterator yields the elements from its index on, last first. -/
theorem core.slice.iter.IteratorSliceIter.next_back.yields {T : Type _} :
    ∀ (k : Nat) (it : core.slice.iter.Iter T), it.i + k = it.slice.val.length →
      ∃ it', core.iter.traits.iterator.Yields core.slice.iter.IteratorSliceIter.next_back it
          (it.slice.val.drop it.i).reverse it' ∧
        it'.i = it.i ∧ it'.slice.val = it.slice.val.take it.i := by
  intro k
  induction k with
  | zero =>
    intro it h
    have hge : ¬ it.i < it.slice.val.length := by omega
    refine ⟨it, ?_, rfl, ?_⟩
    · rw [List.drop_eq_nil_of_le (by omega)]
      simp [core.iter.traits.iterator.Yields.nil_iff, core.slice.iter.IteratorSliceIter.next_back,
        hge]
    · simp; omega
  | succ k ih =>
    intro it h
    have hlt : it.i < it.slice.val.length := by omega
    obtain ⟨r, hr, hpost⟩ := WP.spec_exists_ok
      (core.slice.iter.IteratorSliceIter.next_back.spec it hlt)
    obtain ⟨o, it1⟩ := r
    obtain ⟨ho, hs1, hi1⟩ := hpost
    simp only at ho hs1 hi1
    obtain ⟨it', hy', hi', hs'⟩ := ih it1 (by rw [hi1, hs1]; simp; omega)
    refine ⟨it', ?_, by rw [hi', hi1], ?_⟩
    · have hne : it.slice.val ≠ [] := by intro h0; rw [h0] at hlt; simp at hlt
      have hgl : o = some (it.slice.val.getLast hne) := by
        rw [ho, List.getLast?_eq_getLast_of_ne_nil hne]
      have hlist : (it.slice.val.drop it.i).reverse =
          it.slice.val.getLast hne :: (it1.slice.val.drop it1.i).reverse := by
        obtain ⟨L', hL⟩ : ∃ L', it.slice.val = L' ++ [it.slice.val.getLast hne] :=
          ⟨_, (List.dropLast_append_getLast hne).symm⟩
        have hlen : L'.length = it.slice.val.length - 1 := by
          have := congrArg List.length hL
          simp at this
          omega
        have htake : it.slice.val.take (it.slice.val.length - 1) = L' := by
          rw [← hlen]
          conv_lhs => rw [hL]
          simp
        rw [hs1, hi1, htake]
        conv_lhs => rw [hL]
        rw [List.drop_append_of_le_length (by omega)]
        simp
      rw [hlist, core.iter.traits.iterator.Yields.cons_iff]
      exact ⟨it1, by rw [hr, hgl], hy'⟩
    · rw [hs', hs1, hi1, List.take_take]
      congr 1
      omega

/-! ## `flatten` -/

/-- `core::iter::adapters::flatten::Flatten`. The type parameters are those the Rust type has
    after Aeneas adds the associated types of its clauses: the outer iterator, its item, the
    item of the inner iterators and their type. `front` and `back` are the inner iterators
    being drained from the front and the back; `back` is only filled by `next_back`, which is
    not modelled. The `Fuse` the standard library wraps around the outer iterator is left
    out. -/
@[rust_type "core::iter::adapters::flatten::Flatten"]
structure core.iter.adapters.flatten.Flatten (I : Type u) (Item0 : Type v) (Item1 : Type w)
    (U : Type x) where
  iter : I
  front : Option U
  back : Option U

def core.iter.traits.iterator.Iterator.flatten.default
  {Self Item0 Item1 U : Type _} :
  Self → Result (core.iter.adapters.flatten.Flatten Self Item0 Item1 U) :=
  fun self => ok ⟨self, none, none⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flatten"]
def core.iter.traits.iterator.Iterator.flatten.trait_default
  {Self Item0 Item1 U : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Item0)
  (_IntoIterInst : core.iter.traits.collect.IntoIterator Item0 Item1 U) :
  Self → Result (core.iter.adapters.flatten.Flatten Self Item0 Item1 U) :=
  core.iter.traits.iterator.Iterator.flatten.default

/-- One step of `Flatten::next` (`flatten.rs`, `FlattenCompat::next`): next item of the front
    inner iterator, else open the next inner iterator, else the back one. -/
def core.iter.adapters.flatten.Flatten.next.body
  {I U Item0 Item1 : Type _}
  (IterI : core.iter.traits.iterator.Iterator I Item0)
  (IntoIterInst : core.iter.traits.collect.IntoIterator Item0 Item1 U)
  (IterU : core.iter.traits.iterator.Iterator U Item1) :
  core.iter.adapters.flatten.Flatten I Item0 Item1 U →
    Result (ControlFlow (core.iter.adapters.flatten.Flatten I Item0 Item1 U)
      ((Option Item1) × core.iter.adapters.flatten.Flatten I Item0 Item1 U))
  | self => do
    match self.front with
    | some inner => do
      let (o, inner1) ← IterU.next inner
      match o with
      | some x => ok (.done (some x, { self with front := some inner1 }))
      | none => ok (.cont { self with front := none })
    | none => do
      let (o, it) ← IterI.next self.iter
      match o with
      | some u => do
        let j ← IntoIterInst.into_iter u
        ok (.cont { self with iter := it, front := some j })
      | none =>
        match self.back with
        | none => ok (.done (none, { self with iter := it }))
        | some b => do
          let (o2, b1) ← IterU.next b
          match o2 with
          | some x => ok (.done (some x, { self with iter := it, back := some b1 }))
          | none => ok (.done (none, { self with iter := it, back := none }))

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::next"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next
  {I U Item0 Item1 : Type _}
  (IterI : core.iter.traits.iterator.Iterator I Item0)
  (IntoIterInst : core.iter.traits.collect.IntoIterator Item0 Item1 U)
  (IterU : core.iter.traits.iterator.Iterator U Item1) :
  core.iter.adapters.flatten.Flatten I Item0 Item1 U →
    Result ((Option Item1) × core.iter.adapters.flatten.Flatten I Item0 Item1 U) :=
  fun self => Aeneas.Std.loop
    (core.iter.adapters.flatten.Flatten.next.body IterI IntoIterInst IterU) self

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>"]
impl_def core.iter.traits.iterator.IteratorFlatten {I U Item0 Item1 : Type _}
    (IterI : core.iter.traits.iterator.Iterator I Item0)
    (IntoIterInst : core.iter.traits.collect.IntoIterator Item0 Item1 U)
    (IterU : core.iter.traits.iterator.Iterator U Item1) :
    core.iter.traits.iterator.Iterator
      (core.iter.adapters.flatten.Flatten I Item0 Item1 U) Item1 := {
  next := core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next
    IterI IntoIterInst IterU
}

section FlattenSpecs

open core.iter.adapters.flatten core.iter.traits.iterator

variable {I U Item0 Item1 : Type _}
  (IterI : Iterator I Item0) (IntoIterInst : core.iter.traits.collect.IntoIterator Item0 Item1 U)
  (IterU : Iterator U Item1)

theorem Flatten.next.front_item (it : I) (j j1 : U) (x : Item1) (bk : Option U)
    (hn : IterU.next j = ok (some x, j1)) :
    Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU ⟨it, some j, bk⟩ =
      ok (some x, ⟨it, some j1, bk⟩) := by
  unfold Flatten.Insts.CoreIterTraitsIteratorIterator.next
  rw [Aeneas.Std.loop]
  simp [Flatten.next.body, hn, uncurry]

theorem Flatten.next.front_end (it : I) (j j1 : U) (bk : Option U)
    (hn : IterU.next j = ok (none, j1)) :
    Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU ⟨it, some j, bk⟩ =
      Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU ⟨it, none, bk⟩ := by
  unfold Flatten.Insts.CoreIterTraitsIteratorIterator.next
  rw [Aeneas.Std.loop]
  simp [Flatten.next.body, hn, uncurry]

theorem Flatten.next.outer_end (it it1 : I)
    (ho : IterI.next it = ok (none, it1)) :
    Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU
        ⟨it, none, none⟩ = ok (none, ⟨it1, none, none⟩) := by
  unfold Flatten.Insts.CoreIterTraitsIteratorIterator.next
  rw [Aeneas.Std.loop]
  simp [Flatten.next.body, ho, uncurry]

theorem Flatten.next.outer_item (it it1 : I) (u : Item0) (j : U) (bk : Option U)
    (ho : IterI.next it = ok (some u, it1)) (hj : IntoIterInst.into_iter u = ok j) :
    Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU
        ⟨it, none, bk⟩ =
      Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU
        ⟨it1, some j, bk⟩ := by
  unfold Flatten.Insts.CoreIterTraitsIteratorIterator.next
  rw [Aeneas.Std.loop]
  simp [Flatten.next.body, ho, hj, uncurry]

/-- The inner iterator in front of the outer one: its items, then those of the later rows. -/
theorem Flatten.next.yields_front (us : List Item0)
    (hA : ∀ (it it' : I) (ls : List (List Item1)),
      Yields IterI.next it us it' →
      List.Forall₂ (fun u l => ∃ j j', IntoIterInst.into_iter u = ok j ∧
        Yields IterU.next j l j') us ls →
      Yields (Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU)
        ⟨it, none, none⟩ ls.flatten ⟨it', none, none⟩) :
    ∀ (l : List Item1) (j j' : U) (it it' : I) (ls : List (List Item1)),
      Yields IterU.next j l j' → Yields IterI.next it us it' →
      List.Forall₂ (fun u l => ∃ j j', IntoIterInst.into_iter u = ok j ∧
        Yields IterU.next j l j') us ls →
      Yields (Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU)
        ⟨it, some j, none⟩ (l ++ ls.flatten) ⟨it', none, none⟩ := by
  intro l
  induction l with
  | nil =>
    intro j j' it it' ls hyj hyo hf
    rw [Yields.nil_iff] at hyj
    rw [List.nil_append]
    exact Yields.of_next_eq _ _ _ _ _
      (Flatten.next.front_end IterI IntoIterInst IterU it j j' none hyj) (hA it it' ls hyo hf)
  | cons x l ih =>
    intro j j' it it' ls hyj hyo hf
    obtain ⟨j1, hn, hy1⟩ := (Yields.cons_iff _ _ _ _ _).1 hyj
    rw [List.cons_append, Yields.cons_iff]
    exact ⟨⟨it, some j1, none⟩, Flatten.next.front_item IterI IntoIterInst IterU it j j1 x none hn,
      ih j1 j' it it' ls hy1 hyo hf⟩

/-- `flatten` yields the concatenation of the lists its inner iterators yield. -/
theorem Flatten.next.yields (us : List Item0) :
    ∀ (it it' : I) (ls : List (List Item1)),
      Yields IterI.next it us it' →
      List.Forall₂ (fun u l => ∃ j j', IntoIterInst.into_iter u = ok j ∧
        Yields IterU.next j l j') us ls →
      Yields (Flatten.Insts.CoreIterTraitsIteratorIterator.next IterI IntoIterInst IterU)
        ⟨it, none, none⟩ ls.flatten ⟨it', none, none⟩ := by
  induction us with
  | nil =>
    intro it it' ls hy hf
    rw [Yields.nil_iff] at hy
    cases hf
    rw [List.flatten_nil, Yields.nil_iff]
    exact Flatten.next.outer_end IterI IntoIterInst IterU it it' hy
  | cons u us ih =>
    intro it it' ls hy hf
    obtain ⟨it1, ho, hy1⟩ := (Yields.cons_iff _ _ _ _ _).1 hy
    cases hf with
    | cons hl hf' =>
      obtain ⟨j, j', hj, hyj⟩ := hl
      rw [List.flatten_cons]
      exact Yields.of_next_eq _ _ _ _ _
        (Flatten.next.outer_item IterI IntoIterInst IterU it it1 u j none ho hj)
        (Flatten.next.yields_front IterI IntoIterInst IterU us ih _ j j' it1 it' _ hyj hy1 hf')

end FlattenSpecs

/-! ## Slice-iterator overrides -/

/-- `slice::Iter::position`. The standard library overrides the default with an equivalent
    loop; the model is the default. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::position"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
  {T P : Type _} (FnMutInst : core.ops.function.FnMut P T Bool)
  (it : core.slice.iter.Iter T) (p : P) :
  Result ((Option Usize) × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.position.default.loop
    core.slice.iter.IteratorSliceIter.next FnMutInst it p

/-- `slice::Iter::find_map`. The standard library overrides the default with an equivalent
    loop; the model is the default. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::find_map"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find_map
  {T B F : Type _} (FnMutInst : core.ops.function.FnMut F T (Option B))
  (it : core.slice.iter.Iter T) (f : F) :
  Result ((Option B) × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.find_map.default.loop
    core.slice.iter.IteratorSliceIter.next FnMutInst it f

/-- `position` over an iterator that yields `l`, with a closure that is the pure predicate `g`:
    `List.findIdx?`, and the iterator after the match (or exhausted when there is none). -/
theorem core.iter.traits.iterator.Iterator.position.default.loop.spec_yields
    {Self Item P : Type _}
    (next : Self → Result ((Option Item) × Self))
    (FnMutInst : core.ops.function.FnMut P Item Bool) (g : Item → Bool)
    (l : List Item) (self : Self) (p : P) (self' : Self)
    (hy : core.iter.traits.iterator.Yields next self l self')
    (hg : ∀ p x, x ∈ l → FnMutInst.call_mut p x = ok (g x, p))
    (hlen : l.length ≤ Usize.max) :
    core.iter.traits.iterator.Iterator.position.default.loop next FnMutInst self p
      ⦃ r => r.1.map (·.val) = l.findIdx? g ∧
        match l.findIdx? g with
        | none => r.2 = self'
        | some k => core.iter.traits.iterator.Advances next self (l.take (k + 1)) r.2 ⦄ := by
  unfold core.iter.traits.iterator.Iterator.position.default.loop
  apply WP.spec_mono (core.iter.traits.iterator.Iterator.position.default.loop_from.spec
    next FnMutInst g l self 0#usize p self' hy hg (by simpa using hlen))
  rintro r ⟨h1, h2⟩
  exact ⟨by simpa using h1, h2⟩

theorem core.iter.traits.iterator.Iterator.find_map.default.loop.spec_yields
    {Self Item B F : Type _}
    (next : Self → Result ((Option Item) × Self))
    (FnMutInst : core.ops.function.FnMut F Item (Option B)) (g : Item → Option B)
    (l : List Item) (self : Self) (f : F) (self' : Self)
    (hy : core.iter.traits.iterator.Yields next self l self')
    (hg : ∀ f x, x ∈ l → FnMutInst.call_mut f x = ok (g x, f)) :
    core.iter.traits.iterator.Iterator.find_map.default.loop next FnMutInst self f
      ⦃ r => r.1 = l.findSome? g ∧
        match l.findIdx? (fun x => (g x).isSome) with
        | none => r.2 = self'
        | some k => core.iter.traits.iterator.Advances next self (l.take (k + 1)) r.2 ⦄ :=
  core.iter.traits.iterator.Iterator.find_map.default.loop.spec next FnMutInst g l self f self'
    hy hg

/-- `slice::Iter::fold` is a monadic left fold over the remaining elements. -/
theorem core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold.eq_foldlM
    {T Acc F : Type _} (FnMutInst : core.ops.function.FnMut F (Acc × T) Acc)
    (it : core.slice.iter.Iter T) (init : Acc) (f : F) (hi : it.i ≤ it.slice.val.length) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold FnMutInst it init f =
      (do
        let s ← (it.slice.val.drop it.i).foldlM
          (fun (s : Acc × F) x => FnMutInst.call_mut s.2 (s.1, x)) (init, f)
        ok s.1) :=
  core.iter.traits.iterator.Iterator.fold.default.loop.eq_foldlM_of_yields
    core.slice.iter.IteratorSliceIter.next FnMutInst _ it init f _
    (core.slice.iter.IteratorSliceIter.next.yields (it.slice.val.length - it.i) it (by omega))

