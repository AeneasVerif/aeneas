import Aeneas.SLPoC.Examples.VerusStd

/-!
# Doubly-linked list

A port of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`).
Every `&mut self` method becomes a function that consumes `self` and returns the
updated value, which is the shape a functional translation of the Rust code
takes.

The executable definitions come first; the ghost state, the specifications and
their proofs follow, in the same namespaces.  The sequence and permission-map
reasoning Verus inherits from `vstd` lives in `Aeneas.SLPoC.Examples.VerusStd`.  The
`*.spec` theorems state the Verus `requires`/`ensures` clauses over the explicit
ghost state.
-/

namespace Aeneas.SLPoC

open scoped SepLogic
open VerusStd

/-! # Executable definitions -/

/-- Single node in the list. -/
structure Node (V : Type) where
  prev : Option (Ptr (Node V))
  next : Option (Ptr (Node V))
  payload : V

/-- Doubly-linked list.  Contains a head pointer and a tail pointer; the ghost
state of the Verus version lives in the specifications instead. -/
structure DoublyLinkedList (V : Type) where
  head : Option (Ptr (Node V))
  tail : Option (Ptr (Node V))

namespace DoublyLinkedList

variable {V : Type}

/-- Construct a new, empty, doubly-linked list. -/
def new : St (DoublyLinkedList V) :=
  pure { head := none, tail := none }

/-- Insert one node, assuming the linked list is empty. -/
def pushEmptyCase (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  let ptr ← alloc { prev := none, next := none, payload := v }
  pure { s with tail := some ptr, head := some ptr }

/-- Insert a value at the end of the list. -/
def pushBack (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.tail with
  | none =>
    pushEmptyCase s v
  | some oldTailPtr =>
    let newTailPtr ← alloc { prev := some oldTailPtr, next := none, payload := v }
    let oldTailNode ← read oldTailPtr
    update oldTailPtr { oldTailNode with next := some newTailPtr }
    pure { s with tail := some newTailPtr }

/-- Take a value from the end of the list.  Requires the list to be non-empty. -/
def popBack (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  let lastPtr := s.tail.get!
  let lastNode ← read lastPtr
  free lastPtr
  let v := lastNode.payload
  match lastNode.prev with
  -- No `prev`: this was the only node, so the list becomes empty.
  | none =>
    pure ({ s with tail := none, head := none }, v)
  | some penultimatePtr =>
    let penultimateNode ← read penultimatePtr
    update penultimatePtr { penultimateNode with next := none }
    pure ({ s with tail := some penultimatePtr }, v)

/-- Insert a value at the front of the list. -/
def pushFront (s : DoublyLinkedList V) (v : V) : St (DoublyLinkedList V) := do
  match s.head with
  | none =>
    pushEmptyCase s v
  | some oldHeadPtr =>
    let newHeadPtr ← alloc { prev := none, next := some oldHeadPtr, payload := v }
    let oldHeadNode ← read oldHeadPtr
    update oldHeadPtr { oldHeadNode with prev := some newHeadPtr }
    pure { s with head := some newHeadPtr }

/-- Take a value from the front of the list.  Requires the list to be
non-empty. -/
def popFront (s : DoublyLinkedList V) : St (DoublyLinkedList V × V) := do
  let firstPtr := s.head.get!
  let firstNode ← read firstPtr
  free firstPtr
  let v := firstNode.payload
  match firstNode.next with
  -- No `next`: this was the only node, so the list becomes empty.
  | none =>
    pure ({ s with tail := none, head := none }, v)
  | some secondPtr =>
    let secondNode ← read secondPtr
    update secondPtr { secondNode with prev := none }
    pure ({ s with head := some secondPtr }, v)

/-- The `while j < i` loop of `get`, walking the list from index `j` to
index `i`. -/
def getLoop (i : Nat) (j : Nat) (ptr : Ptr (Node V)) : St (Ptr (Node V)) :=
  if j < i then do
    let node ← read ptr
    let nextPtr := node.next.get!
    getLoop i (j + 1) nextPtr
  else
    pure ptr
termination_by i - j
decreasing_by omega

/-- Get the `i`th value of the list. -/
def get (s : DoublyLinkedList V) (i : Nat) : St V := do
  let ptr ← getLoop i 0 s.head.get!
  let node ← read ptr
  pure node.payload

end DoublyLinkedList

/-- Iterator over a doubly-linked list.  `index` is ghost state in the Verus
version. -/
structure Iterator (V : Type) where
  l : DoublyLinkedList V
  cur : Option (Ptr (Node V))
  index : Nat

namespace Iterator

variable {V : Type}

/-- Create an iterator positioned at the front of `l`. -/
def new (l : DoublyLinkedList V) : St (Iterator V) :=
  pure { l := l, cur := l.head, index := 0 }

/-- The value the iterator currently points at. -/
def value (it : Iterator V) : St V := do
  let cur := it.cur.get!
  let node ← read cur
  pure node.payload

/-- Advance the iterator; returns whether it still points at a value. -/
def moveNext (it : Iterator V) : St (Iterator V × Bool) := do
  let cur := it.cur.get!
  let node ← read cur
  match node.next with
  | none => pure ({ it with cur := none, index := it.index + 1 }, false)
  | some nextPtr =>
    pure ({ it with cur := some nextPtr, index := it.index + 1 }, true)

end Iterator

/-! # Ghost state, specifications and proofs

Verus keeps the pointers and their `PointsTo` permissions in ghost state inside
the list; here the permissions live in the precondition and the sequence of
pointers is an ordinary parameter of the specifications.

| Verus | Here |
|---|---|
| `PPtr<Node<V>>` + `PointsTo<Node<V>>` | `Ptr (Node V)` and the assertion `r ↦ node` |
| `ghost_state@.ptrs` / `points_to_map` | `Cells V`, a list of pointer/payload pairs |
| `well_formed_node(i)` | `nodeAt l i v`, the contents `nodesFrom` requires at index `i` |
| `well_formed()` | `wellFormed s l` |
| `self@` (`view`) | `view l` |
| `Iterator::valid()` | `Iterator.valid it l` plus `wellFormed t l` in the precondition |
-/

namespace DoublyLinkedList

variable {V : Type}

/-- Verus' `ghost_state@.ptrs` zipped with `ghost_state@.points_to_map`. -/
abbrev Cells (V : Type) := List (Ptr (Node V) × V)

/-- Representation of the list as a sequence, i.e. Verus' `view`. -/
abbrev view (l : Cells V) : List V := payloads l

/-- Pointer to the node of index `i - 1`, or `none` if `i` is `0`. -/
def prevOf (l : Cells V) (i : Nat) : Option (Ptr (Node V)) :=
  if i = 0 then none else l[i - 1]?.map Prod.fst

/-- Pointer to the node of index `i + 1`, or `none` if `i` is the last index. -/
def nextOf (l : Cells V) (i : Nat) : Option (Ptr (Node V)) :=
  if i + 1 = l.length then none else l[i + 1]?.map Prod.fst

/-- Contents of the node of index `i`, i.e. Verus' `well_formed_node`. -/
def nodeAt (l : Cells V) (i : Nat) (v : V) : Node V :=
  { prev := prevOf l i, next := nextOf l i, payload := v }

-- Index arithmetic is all `grind` has to do here, so teach it the accessors once.
attribute [grind] prevOf nextOf nodeAt

/-- Owns the nodes `cs` of `l` starting at index `i`: `VerusStd`'s permission
map under the invariant `nodeAt l`. -/
abbrev nodesFrom (l : Cells V) : Nat → Cells V → SLProp := cellsFrom (nodeAt l)

/-- Ownership of every node, each well-formed: the first conjunct of Verus'
`well_formed`. -/
def nodes (l : Cells V) : SLProp := nodesFrom l 0 l

/-- Linked list is well-formed: every node is well-formed, and the `head`/`tail`
pointers agree with the ghost state. -/
def wellFormed (s : DoublyLinkedList V) (l : Cells V) : SLProp :=
  iprop(⌜s.head = firstPtr l ∧ s.tail = lastPtr l⌝ ∗ nodes l)

@[simp] theorem nodes_nil : nodes ([] : Cells V) = emp := rfl

@[simp] theorem prevOf_zero (l : Cells V) : prevOf l 0 = none := by
  simp [prevOf]

/-! ## Structural lemmas about `nodesFrom` -/

/-- Ownership of a concatenation splits into ownership of the two parts. -/
theorem nodesFrom_append (l : Cells V) (xs ys : Cells V) (i : Nat) :
    nodesFrom l i (xs ++ ys) =
      iprop(nodesFrom l i xs ∗ nodesFrom l (i + xs.length) ys) :=
  cellsFrom_append (nodeAt l) xs ys i

@[simp] theorem nodesFrom_singleton (l : Cells V) (i : Nat) (r : Ptr (Node V))
    (v : V) : nodesFrom l i [(r, v)] = iprop(r ↦ nodeAt l i v) :=
  cellsFrom_singleton (nodeAt l) i r v

/-- `nodesFrom` only depends on the `prev`/`next` pointers of the nodes it owns.
Replaces the pointwise `well_formed_node` triggers of the Verus proof. -/
theorem nodesFrom_congr {l₁ l₂ : Cells V} (cs : Cells V) (i₁ i₂ : Nat)
    (h : ∀ k, k < cs.length →
      prevOf l₁ (i₁ + k) = prevOf l₂ (i₂ + k) ∧
      nextOf l₁ (i₁ + k) = nextOf l₂ (i₂ + k)) :
    nodesFrom l₁ i₁ cs = nodesFrom l₂ i₂ cs :=
  cellsFrom_congr cs i₁ i₂ fun k hk => by funext v; grind

/-- Appending a node at the end does not change the nodes strictly before the
last one. -/
theorem nodesFrom_append_prefix (l₁ l₂ : Cells V) (xs : Cells V) (i : Nat)
    (h : i + xs.length < l₁.length) :
    nodesFrom (l₁ ++ l₂) i xs = nodesFrom l₁ i xs := by
  grind [nodesFrom_congr]

/-- Prepending a node shifts all the indices by one. -/
theorem nodesFrom_cons_shift (c : Ptr (Node V) × V) (l : Cells V) (xs : Cells V)
    (i : Nat) :
    nodesFrom (c :: l) (i + 2) xs = nodesFrom l (i + 1) xs :=
  nodesFrom_congr xs (i + 2) (i + 1) fun k _ => by grind

/-! ## Decomposition of `nodes` at the two ends of the list -/

theorem nodeAt_snoc_last (l : Cells V) (r : Ptr (Node V)) (v : V) :
    nodeAt (l ++ [(r, v)]) l.length v =
      { prev := lastPtr l, next := none, payload := v } := by grind

/-- Split the ownership of the last node out of `nodes`. -/
@[sl_simps] theorem nodes_snoc (l : Cells V) (r : Ptr (Node V)) (v : V) :
    nodes (l ++ [(r, v)]) =
      iprop(nodesFrom (l ++ [(r, v)]) 0 l ∗
        (r ↦ { prev := lastPtr l, next := none, payload := v })) := by
  unfold nodes
  rw [nodesFrom_append, Nat.zero_add, nodesFrom_singleton, nodeAt_snoc_last]

/-- Split the ownership of the last two nodes out of `nodes`.  This is the shape
of the heap both after `pushBack` and before `popBack`. -/
@[sl_simps high] theorem nodes_snoc_two (l : Cells V) (rt : Ptr (Node V)) (vt : V)
    (rn : Ptr (Node V)) (v : V) :
    nodes (l ++ [(rt, vt), (rn, v)]) =
      iprop(nodesFrom (l ++ [(rt, vt)]) 0 l ∗
        (rt ↦ { prev := lastPtr l, next := some rn, payload := vt }) ∗
        (rn ↦ { prev := some rt, next := none, payload := v })) := by
  have hassoc : l ++ [(rt, vt), (rn, v)] = (l ++ [(rt, vt)]) ++ [(rn, v)] := by simp
  have hprefix : nodesFrom (l ++ [(rt, vt), (rn, v)]) 0 l
      = nodesFrom (l ++ [(rt, vt)]) 0 l := by
    rw [hassoc]; exact nodesFrom_append_prefix _ _ _ _ (by simp)
  have hmid : nodeAt (l ++ [(rt, vt), (rn, v)]) l.length vt =
      { prev := lastPtr l, next := some rn, payload := vt } := by
    have hprev : prevOf (l ++ [(rt, vt), (rn, v)]) l.length = lastPtr l := by
      rw [hassoc]; grind
    grind
  rw [hassoc, nodes_snoc, ← hassoc, nodesFrom_append, Nat.zero_add,
    nodesFrom_singleton, hmid, hprefix, lastPtr_snoc, hstar_assoc_eq]

/-- Split the ownership of the first node out of `nodes`. -/
@[sl_simps] theorem nodes_cons (rh : Ptr (Node V)) (vh : V) (l : Cells V) :
    nodes ((rh, vh) :: l) =
      iprop((rh ↦ { prev := none, next := firstPtr l, payload := vh }) ∗
        nodesFrom ((rh, vh) :: l) 1 l) := by
  have : nodeAt ((rh, vh) :: l) 0 vh =
      { prev := none, next := firstPtr l, payload := vh } := by grind
  simp only [nodes, nodesFrom, cellsFrom_cons, Nat.zero_add, this]

/-- The second node of a list, as `nodesFrom` describes it. -/
@[sl_simps] theorem nodeAt_cons_one (a b : Ptr (Node V) × V) (l : Cells V) (v : V) :
    nodeAt (a :: b :: l) 1 v =
      { prev := some a.1, next := firstPtr l, payload := v } := by grind

/-- Peeling two nodes off leaves the rest indexed from `2`, which is the tail
indexed from `1`. -/
@[sl_simps] theorem nodesFrom_cons_two (a b : Ptr (Node V) × V) (l xs : Cells V) :
    nodesFrom (a :: b :: l) 2 xs = nodesFrom (b :: l) 1 xs :=
  nodesFrom_cons_shift a (b :: l) xs 0

/-! ## Specifications

Verus' `self.well_formed()` becomes `wellFormed s l`, and `self@` becomes
`view l`. -/

/-- `new` returns a well-formed list whose view is empty. -/
@[step]
theorem new.spec :
    ⦃ emp ⦄ (new : St (DoublyLinkedList V)) ⦃⇓ s => wellFormed s []⦄ := by
  unfold new
  sl_step*

/-- `pushEmptyCase` inserts one node into an empty list. -/
@[step]
theorem pushEmptyCase.spec (s : DoublyLinkedList V) (v : V) :
    ⦃ wellFormed s [] ⦄ pushEmptyCase s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' [(r, v)]⦄ := by
  unfold pushEmptyCase
  sl_step*

/-- `pushBack` appends `v` to the list. -/
@[step]
theorem pushBack.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushBack s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' (l ++ [(r, v)])⦄ := by
  unfold pushBack
  split
  next =>
    sl_pull -- needs the pure part of the precondition to prove `l = []`
    obtain rfl : l = [] := (lastPtr_eq_none_iff l).mp (by grind)
    sl_step*
  next oldTailPtr _ =>
    sl_pull -- needs the pure part of the precondition to prove `l ≠ []`
    have hne : l ≠ [] := mt (lastPtr_eq_none_iff l).mpr (by grind)
    obtain ⟨l', ⟨rt, vt⟩, rfl⟩ := (eq_nil_or_snoc l).resolve_left hne
    obtain rfl : oldTailPtr = rt := by grind [lastPtr_snoc]
    sl_step*

/-- `popBack` removes the last node and returns its payload. Indexing by the
whole list lets `step` recover the ghost list from a concrete precondition. -/
@[step]
theorem popBack.spec (s : DoublyLinkedList V) (l : Cells V) (hne : l ≠ []) :
    ⦃ wellFormed s l ⦄ popBack s
      ⦃⇓ (s', v) => ⌜l.getLast?.map Prod.snd = some v⌝ ∗ wellFormed s' l.dropLast⦄ := by
  obtain ⟨l', ⟨_, _⟩, rfl⟩ := (eq_nil_or_snoc l).resolve_left hne
  rcases eq_nil_or_snoc l' with rfl | ⟨_, ⟨_, _⟩, rfl⟩
  <;> unfold popBack
  <;> sl_pull ⟨_, htail⟩
  <;> simp only [lastPtr_snoc] at htail
  <;> sl_step*

/-- `pushFront` prepends `v` to the list. -/
@[step]
theorem pushFront.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushFront s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' ((r, v) :: l)⦄ := by
  unfold pushFront
  split
  next =>
    sl_pull
    obtain rfl : l = [] := (firstPtr_eq_none_iff l).mp (by grind)
    sl_step*
  next oldHeadPtr hsome =>
    rcases l with _ | ⟨⟨rh, _⟩, _⟩
    · sl_pull ⟨hhead, _⟩
      exfalso
      change s.head = none at hhead
      simp_all
    · sl_pull
      obtain rfl : rh = oldHeadPtr := by grind
      sl_step*

/-- `popFront` removes the first node and returns its payload. -/
@[step]
theorem popFront.spec (s : DoublyLinkedList V) (rh : Ptr (Node V)) (vh : V)
    (l : Cells V) :
    ⦃ wellFormed s ((rh, vh) :: l) ⦄ popFront s
      ⦃⇓ (s', v) => ⌜v = vh⌝ ∗ wellFormed s' l⦄ := by
  unfold popFront
  -- `nodes_cons_two`, which splits the two first nodes out, is stated over a pair.
  rcases l with _ | ⟨⟨_, _⟩, _⟩ <;> sl_step*

/- `step` infers the index and payload by matching `nodes_read`'s `Prop`
argument against a local assumption, which every caller below gets from
`exists_cell`.  The theorem is declared here because enabling it above would
leave the index unconstrained while proving the whole-node specifications. -/
@[step]
theorem nodes_read (l : Cells V) (i : Nat) (r : Ptr (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    ⦃ nodes l ⦄ read r ⦃⇓ node => ⌜node = nodeAt l i v⌝ ∗ nodes l⦄ :=
  cellsFrom_read (nodeAt l) l i r v h

/-! ## Specification of `get` -/

/-- The loop of `get` walks from index `j` to index `i`, keeping Verus' loop
invariant `ptr == ptrs[j]`.  The induction is the one `getLoop`'s own
`termination_by` generates, so no measure has to be threaded by hand. -/
@[step]
theorem getLoop.spec (l : Cells V) (i j : Nat) (r : Ptr (Node V))
    (hji : j ≤ i) (hi : i < l.length) (hr : l[j]?.map Prod.fst = some r) :
    ⦃ nodes l ⦄ getLoop i j r
      ⦃⇓ r' => ⌜l[i]?.map Prod.fst = some r'⌝ ∗ nodes l⦄ := by
  induction j, r using getLoop.induct (i := i) with
  | case1 j r hlt ih =>
    rw [getLoop, if_pos hlt]
    obtain ⟨rj, vj, hj⟩ := exists_cell l j (by omega)
    obtain ⟨r', v', hj'⟩ := exists_cell l (j + 1) (by omega)
    obtain rfl : r = rj := by grind
    sl_step*
  | case2 j r hge =>
    obtain rfl : j = i := by omega
    rw [getLoop, if_neg hge]
    sl_step*

/-- `get` returns the `i`th element of the view. -/
@[step]
theorem get.spec (s : DoublyLinkedList V) (l : Cells V) (i : Nat)
    (hi : i < l.length) :
    ⦃ wellFormed s l ⦄ get s i
      ⦃⇓ v => ⌜(view l)[i]? = some v⌝ ∗ wellFormed s l⦄ := by
  unfold get
  sl_step as ⟨ r, _ ⟩
  obtain ⟨ri, _, _⟩ := exists_cell l i hi
  obtain rfl : r = ri := by grind
  sl_step*

/- Keep the ghost list a literal between steps: otherwise the unifier has to
`whnf` through an unreduced `dropLast` at the next call, which is where
`run.spec` used to spend its whole heartbeat budget. -/
attribute [step_post_simps]
  List.nil_append List.cons_append List.append_assoc
  List.dropLast_cons₂ List.dropLast_nil
  List.getLast?_cons_cons List.getLast?_singleton Option.map_some

end DoublyLinkedList

/-! ## Iterator specifications -/

namespace Iterator

open DoublyLinkedList

variable {V : Type}

/-- Verus' `Iterator::valid`, minus the well-formedness of the underlying list:
that part lives in the separation-logic precondition. -/
def valid (it : Iterator V) (l : Cells V) : Prop :=
  it.index < l.length ∧ it.cur = l[it.index]?.map Prod.fst

/-- A fresh iterator is valid and positioned at index `0`. -/
@[step]
theorem new.spec (t : DoublyLinkedList V) (l : Cells V) (hne : 0 < l.length) :
    ⦃ wellFormed t l ⦄ Iterator.new t
      ⦃⇓ it => ⌜it.l = t ∧ it.index = 0 ∧ valid it l⌝ ∗ wellFormed t l⦄ := by
  unfold Iterator.new
  simp only [valid]
  sl_step*

/-- The iterator yields the element of the view at its index. -/
@[step]
theorem value.spec (it : Iterator V) (l : Cells V) (hvalid : valid it l) :
    ⦃ wellFormed it.l l ⦄ it.value
      ⦃⇓ v => ⌜(view l)[it.index]? = some v⌝ ∗ wellFormed it.l l⦄ := by
  unfold Iterator.value
  obtain ⟨hidx, hcur⟩ := hvalid
  obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx
  simp only [show it.cur = some r from by grind, get!_some]
  sl_step*

/-- Advancing the iterator: it reports whether there still is an element, and if
so it becomes valid again at the next index.  The unconditional `index` and the
`cur` of the exhausted case rule out an implementation that stalls at the last
node. -/
@[step]
theorem moveNext.spec (it : Iterator V) (l : Cells V) (hvalid : valid it l) :
    ⦃ wellFormed it.l l ⦄ it.moveNext
      ⦃⇓ (it', good) =>
        ⌜it'.l = it.l ∧
          it'.index = it.index + 1 ∧
          (good = true ↔ it.index + 1 < l.length) ∧
          (good = true → valid it' l) ∧
          (good = false → it'.cur = none)⌝ ∗
        wellFormed it.l l⦄ := by
  unfold Iterator.moveNext
  obtain ⟨hidx, hcur⟩ := hvalid
  obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx
  simp only [show it.cur = some r from by grind, get!_some]
  sl_step
  by_cases hlast : it.index + 1 = l.length
  · sl_step*
  · obtain ⟨r', v', hcell'⟩ := exists_cell l (it.index + 1) (by omega)
    simp only [nodeAt, nextOf, if_neg hlast, hcell', Option.map_some, valid]
    sl_step*

end Iterator

/-! ## The `main::run` example

The Verus example builds the list `1, 2, 3`, walks it with an iterator, and
empties it again, asserting the observed values along the way. -/

namespace Example

open DoublyLinkedList

def run : St (Nat × Nat × Nat × Bool × Nat × Nat × Nat) := do
  let t ← DoublyLinkedList.new (V := Nat)
  let t ← t.pushBack 2
  let t ← t.pushBack 3
  let t ← t.pushFront 1  -- 1, 2, 3
  let it ← Iterator.new t
  let v1 ← it.value
  let m1 ← it.moveNext
  let it := m1.1
  let v2 ← it.value
  let m2 ← it.moveNext
  let it := m2.1
  let v3 ← it.value
  let m3 ← it.moveNext
  let g := m3.2
  let p1 ← t.popBack  -- 3
  let t := p1.1
  let x := p1.2
  let p2 ← t.popFront  -- 1
  let t := p2.1
  let y := p2.2
  let p3 ← t.popFront  -- 2
  let z := p3.2
  pure (v1, v2, v3, g, x, y, z)

theorem run.spec :
    (run) ⦃⇓ (v1, v2, v3, g, x, y, z) =>
      v1 = 1 ∧ v2 = 2 ∧ v3 = 3 ∧ g = false ∧ x = 3 ∧ y = 1 ∧ z = 2⦄ := by
  unfold run
  sl_step*

end Example

end Aeneas.SLPoC
