import Aeneas.SLPoC.DoublyLinkedList
import Aeneas.SLPoC.Step

/-!
# Doubly-linked list: ghost state and its library layer

Ghost state of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`),
together with the sequence, index and permission-map reasoning the proofs in
`Aeneas.SLPoC.DoublyLinkedListSpec` are built on.

Verus tracks the pointers and their `PointsTo` permissions in ghost state stored
inside the list.  Here the permissions live in the separation-logic
precondition, and the ghost sequence of pointers is an ordinary parameter of the
specifications: `Cells V` plays the role of Verus' `ghost_state@.ptrs` zipped
with the payloads of `ghost_state@.points_to_map`.

Correspondence with the Verus development:

| Verus | Here |
|---|---|
| `PPtr<Node<V>>` + `PointsTo<Node<V>>` | `Ptr (Node V)` and the assertion `r ↦ node` |
| `ghost_state@.ptrs` / `points_to_map` | `Cells V`, a list of pointer/payload pairs |
| `well_formed_node(i)` | `nodeAt l i v`, the contents `nodesFrom` requires at index `i` |
| `well_formed()` | `wellFormed s l` |
| `self@` (`view`) | `view l` |
| `well_formed()` with the ghost state hidden | `isList s vs` |
| `Iterator::valid()` | `Iterator.valid it l` plus `wellFormed t l` in the precondition |

Every lemma below is labelled with the `vstd` primitive (or the specification
Verus derives from it) that makes the corresponding step free on the Verus side.
Verus imports `vstd`, so none of these lemmas appear in its version of the
example; they are the price of building the model from scratch, and they are
kept in this module so that the line counts of the example proper stay
comparable.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## Ghost state and the representation predicate -/

namespace DoublyLinkedList

variable {V : Type}

/-- Ghost state of a list: the sequence of node pointers, each paired with the
payload the node holds.  This plays the role of Verus'
`ghost_state@.ptrs` zipped with `ghost_state@.points_to_map`. -/
abbrev Cells (V : Type) := List (Ptr (Node V) × V)

/-- Representation of the list as a sequence, i.e. Verus' `view`. -/
def view (l : Cells V) : List V := l.map Prod.snd

/-- Pointer to the first node, if any.  Stated with `getElem?` rather than
`head?` so that it is the `i = 0` case of the same index arithmetic as
`prevOf`/`nextOf`, which is what lets `grind` relate them. -/
def headPtr (l : Cells V) : Option (Ptr (Node V)) := l[0]?.map Prod.fst

/-- Pointer to the last node, if any. -/
def lastPtr (l : Cells V) : Option (Ptr (Node V)) := l.getLast?.map Prod.fst

/-- Pointer to the node of index `i - 1`, or `none` if `i` is `0`. -/
def prevOf (l : Cells V) (i : Nat) : Option (Ptr (Node V)) :=
  if i = 0 then none else l[i - 1]?.map Prod.fst

/-- Pointer to the node of index `i + 1`, or `none` if `i` is the last index. -/
def nextOf (l : Cells V) (i : Nat) : Option (Ptr (Node V)) :=
  if i + 1 = l.length then none else l[i + 1]?.map Prod.fst

/-- Contents of the node of index `i`, whose payload is `v`.  Verus'
`well_formed_node` states that the node stored at `ptrs[i]` is exactly this. -/
def nodeAt (l : Cells V) (i : Nat) (v : V) : Node V :=
  { prev := prevOf l i, next := nextOf l i, payload := v }

/- The accessors are the only arithmetic `grind` has to do on indices, so it is
worth teaching it their equations once instead of citing them at every use. -/
attribute [grind] headPtr lastPtr prevOf nextOf nodeAt

/-- `nodesFrom l i cs` owns the nodes `cs`, which are the nodes of `l` starting
at index `i`. -/
def nodesFrom (l : Cells V) : Nat → Cells V → SLProp
  | _, [] => emp
  | i, (r, v) :: rest => iprop((r ↦ nodeAt l i v) ∗ nodesFrom l (i + 1) rest)

/-- Ownership of every node of the list, each of them well-formed.  This is the
separation-logic counterpart of the first conjunct of Verus'
`well_formed`. -/
def nodes (l : Cells V) : SLProp := nodesFrom l 0 l

/-- Linked list is well-formed: every node is well-formed, and the `head`/`tail`
pointers agree with the ghost state. -/
def wellFormed (s : DoublyLinkedList V) (l : Cells V) : SLProp :=
  iprop(⌜s.head = headPtr l ∧ s.tail = lastPtr l⌝ ∗ nodes l)

/-- Abstract representation predicate: `s` is a well-formed list whose view is
`vs`.  The ghost state is hidden, as it is in Verus. -/
def isList (s : DoublyLinkedList V) (vs : List V) : SLProp :=
  iprop(∃ l : Cells V, ⌜view l = vs⌝ ∗ wellFormed s l)

/-! ## Basic simplification lemmas -/

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::empty()` and its `len`/`index` axioms. -/
@[simp] theorem view_nil : view ([] : Cells V) = [] := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::push`/`subrange` axioms (Verus writes `seq![v].add(s)`). -/
@[simp] theorem view_cons (c : Ptr (Node V) × V) (l : Cells V) :
    view (c :: l) = c.2 :: view l := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::add` and `lemma_seq_add_len`. -/
@[simp] theorem view_append (l₁ l₂ : Cells V) :
    view (l₁ ++ l₂) = view l₁ ++ view l₂ := List.map_append ..

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::len` axiom for `Seq::new`. -/
@[simp] theorem view_length (l : Cells V) : (view l).length = l.length := by
  simp [view]

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::index` axiom for `Seq::new`. -/
@[grind =] theorem view_getElem? (l : Cells V) (i : Nat) :
    (view l)[i]? = l[i]?.map Prod.snd := by
  simp [view]

/-- *Verus/`vstd` counterpart:* the `vstd::map::Map::empty()` case of a `PointsTo` map. -/
@[simp] theorem nodesFrom_nil (l : Cells V) (i : Nat) :
    nodesFrom l i [] = emp := rfl

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::insert` together with `tracked_remove`. -/
@[simp] theorem nodesFrom_cons (l : Cells V) (i : Nat) (r : Ptr (Node V))
    (v : V) (rest : Cells V) :
    nodesFrom l i ((r, v) :: rest) =
      iprop((r ↦ nodeAt l i v) ∗ nodesFrom l (i + 1) rest) := rfl

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::empty()`. -/
@[simp] theorem nodes_nil : nodes ([] : Cells V) = emp := rfl

/-- *Verus/`vstd` counterpart:* arithmetic Verus discharges with its SMT backend. -/
@[simp] theorem prevOf_zero (l : Cells V) : prevOf l 0 = none := by
  simp [prevOf]

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::empty()` index axiom. -/
@[simp] theorem headPtr_nil : headPtr ([] : Cells V) = none := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::empty()` index axiom. -/
@[simp] theorem lastPtr_nil : lastPtr ([] : Cells V) = none := rfl

/-! ## Structural lemmas about `nodesFrom` -/

/-- `nodesFrom` only depends on the `prev`/`next` pointers of the nodes it
owns.  This lemma replaces the pointwise `well_formed_node` triggers of the
Verus proof.

*Verus/`vstd` counterpart:* `vstd::map::Map::ext_equal` (extensional equality of `PointsTo` maps). -/
theorem nodesFrom_congr {l₁ l₂ : Cells V} :
    ∀ (cs : Cells V) (i₁ i₂ : Nat),
      (∀ k, k < cs.length →
        prevOf l₁ (i₁ + k) = prevOf l₂ (i₂ + k) ∧
        nextOf l₁ (i₁ + k) = nextOf l₂ (i₂ + k)) →
      nodesFrom l₁ i₁ cs = nodesFrom l₂ i₂ cs := by
  intro cs
  induction cs with
  | nil => intros; rfl
  | cons c cs ih =>
    intro i₁ i₂ h
    obtain ⟨r, v⟩ := c
    have h0 := h 0 (by simp)
    have hrest : nodesFrom l₁ (i₁ + 1) cs = nodesFrom l₂ (i₂ + 1) cs := by
      refine ih (i₁ + 1) (i₂ + 1) fun k hk => ?_
      have h' := h (k + 1) (by simpa using hk)
      grind
    simp only [nodesFrom_cons, nodeAt, Nat.add_zero] at h0 ⊢
    grind

/-- Ownership of a concatenation splits into ownership of the two parts.

*Verus/`vstd` counterpart:* `vstd::map::Map::union_prefer_right` plus `lemma_disjoint_union`. -/
theorem nodesFrom_append (l : Cells V) :
    ∀ (xs ys : Cells V) (i : Nat),
      nodesFrom l i (xs ++ ys) =
        iprop(nodesFrom l i xs ∗ nodesFrom l (i + xs.length) ys) := by
  intro xs
  induction xs with
  | nil => intro ys i; simp [hstar_hempty_l_eq]
  | cons c xs ih =>
    intro ys i
    obtain ⟨r, v⟩ := c
    have e : i + 1 + xs.length = i + (xs.length + 1) := by omega
    simp only [List.cons_append, nodesFrom_cons, ih, List.length_cons, e,
      hstar_assoc_eq]

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::singleton`. -/
@[simp] theorem nodesFrom_singleton (l : Cells V) (i : Nat) (r : Ptr (Node V))
    (v : V) :
    nodesFrom l i [(r, v)] = iprop(r ↦ nodeAt l i v) := by
  simp [hstar_hempty_r_eq]

/-! ## How `prevOf`/`nextOf` react to `++` and `::` -/

/-- Appending a node at the end does not change the nodes strictly before the
last one.

*Verus/`vstd` counterpart:* `vstd::map::Map::restrict` on a prefix of the index domain. -/
theorem nodesFrom_append_prefix (l₁ l₂ : Cells V) (xs : Cells V) (i : Nat)
    (h : i + xs.length < l₁.length) :
    nodesFrom (l₁ ++ l₂) i xs = nodesFrom l₁ i xs := by
  grind [nodesFrom_congr]

/-- Prepending a node shifts all the indices by one.

*Verus/`vstd` counterpart:* `vstd::seq::Seq::subrange` re-indexing lemmas. -/
theorem nodesFrom_cons_shift (c : Ptr (Node V) × V) (l : Cells V) (xs : Cells V)
    (i : Nat) :
    nodesFrom (c :: l) (i + 2) xs = nodesFrom l (i + 1) xs := by
  refine nodesFrom_congr xs (i + 2) (i + 1) fun k _ => ?_
  grind [prevOf, nextOf]

/-! ## Decomposition of `nodes` at the two ends of the list -/

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::index` axiom at `0`. -/
@[simp] theorem headPtr_cons (c : Ptr (Node V) × V) (l : Cells V) :
    headPtr (c :: l) = some c.1 := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::push` / `last` axioms. -/
@[simp] theorem lastPtr_snoc (l : Cells V) (c : Ptr (Node V) × V) :
    lastPtr (l ++ [c]) = some c.1 := by
  simp [lastPtr]

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::last` on a one-element sequence. -/
@[simp] theorem lastPtr_singleton (c : Ptr (Node V) × V) :
    lastPtr [c] = some c.1 := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::last` axiom. -/
@[sl_simps] theorem lastPtr_cons_cons (a b : Ptr (Node V) × V) (l : Cells V) :
    lastPtr (a :: b :: l) = lastPtr (b :: l) := by
  simp [lastPtr]

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::push` index axioms. -/
theorem nodeAt_snoc_last (l : Cells V) (r : Ptr (Node V)) (v : V) :
    nodeAt (l ++ [(r, v)]) l.length v =
      { prev := lastPtr l, next := none, payload := v } := by grind

/-- Split the ownership of the last node out of `nodes`.

*Verus/`vstd` counterpart:* `vstd::map::Map::remove` at the last index. -/
@[sl_simps] theorem nodes_snoc (l : Cells V) (r : Ptr (Node V)) (v : V) :
    nodes (l ++ [(r, v)]) =
      iprop(nodesFrom (l ++ [(r, v)]) 0 l ∗
        (r ↦ { prev := lastPtr l, next := none, payload := v })) := by
  unfold nodes
  rw [nodesFrom_append, Nat.zero_add, nodesFrom_singleton, nodeAt_snoc_last]

/-- Split the ownership of the last two nodes out of `nodes`.  This is the shape
of the heap both after `pushBack` and before `popBack`.

*Verus/`vstd` counterpart:* two applications of `vstd::map::Map::remove`. -/
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

/-- Split the ownership of the first node out of `nodes`.

*Verus/`vstd` counterpart:* `vstd::map::Map::remove` at index `0`. -/
@[sl_simps] theorem nodes_cons (rh : Ptr (Node V)) (vh : V) (l : Cells V) :
    nodes ((rh, vh) :: l) =
      iprop((rh ↦ { prev := none, next := headPtr l, payload := vh }) ∗
        nodesFrom ((rh, vh) :: l) 1 l) := by
  have : nodeAt ((rh, vh) :: l) 0 vh =
      { prev := none, next := headPtr l, payload := vh } := by grind
  simp only [nodes, nodesFrom_cons, Nat.zero_add, this]

/-- The second node of a list, as `nodesFrom` describes it.

*Verus/`vstd` counterpart:* `vstd::seq::Seq::index` axiom at `1`. -/
@[sl_simps] theorem nodeAt_cons_one (a b : Ptr (Node V) × V) (l : Cells V) (v : V) :
    nodeAt (a :: b :: l) 1 v =
      { prev := some a.1, next := headPtr l, payload := v } := by grind

/-- Peeling the first node off `nodes` leaves the rest indexed from `1`; peeling
the second one leaves it indexed from `2`, which is the same as the rest of the
tail indexed from `1`.

*Verus/`vstd` counterpart:* `vstd::seq::Seq::subrange` re-indexing lemmas. -/
@[sl_simps] theorem nodesFrom_cons_two (a b : Ptr (Node V) × V) (l xs : Cells V) :
    nodesFrom (a :: b :: l) 2 xs = nodesFrom (b :: l) 1 xs :=
  nodesFrom_cons_shift a (b :: l) xs 0

/-! ## Auxiliary facts used by the specifications -/

/-- *Verus/`vstd` counterpart:* `vstd::option` / Verus' built-in `Option::get_Some_0`. -/
@[simp] theorem get!_some {α : Type} [Inhabited α] (a : α) :
    (some a).get! = a := rfl

/-- Every list is either empty or ends with a node.

*Verus/`vstd` counterpart:* `vstd::seq_lib::lemma_seq_properties` (a sequence is empty or a `push`). -/
theorem eq_nil_or_snoc (l : Cells V) : l = [] ∨ ∃ l' c, l = l' ++ [c] := by
  rcases l.eq_nil_or_concat with h | ⟨l', c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', c, by simpa [List.concat_eq_append] using h⟩

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` tail can only
come from an empty list.

*Verus/`vstd` counterpart:* `assert_by_contradiction!` over the `vstd::seq::Seq::len` axiom. -/
theorem lastPtr_eq_none_iff (l : Cells V) : lastPtr l = none ↔ l = [] := by
  constructor
  · intro h
    rcases l.eq_nil_or_concat with h' | ⟨l', c, h'⟩
    · exact h'
    · rw [h', List.concat_eq_append] at h
      simp at h
  · rintro rfl; rfl

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` head can only
come from an empty list.

*Verus/`vstd` counterpart:* `assert_by_contradiction!` over the `vstd::seq::Seq::len` axiom. -/
theorem headPtr_eq_none_iff (l : Cells V) : headPtr l = none ↔ l = [] := by
  cases l <;> simp [headPtr]

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::index` axiom for `push`. -/
@[sl_simps] theorem headPtr_append_two (l : Cells V) (a b : Ptr (Node V) × V) :
    headPtr (l ++ [a, b]) = headPtr (l ++ [a]) := by
  cases l <;> rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::last` axiom for `push`. -/
@[sl_simps] theorem lastPtr_append_two (l : Cells V) (a b : Ptr (Node V) × V) :
    lastPtr (l ++ [a, b]) = some b.1 := by
  rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp, lastPtr_snoc]

/-! ## Reading an arbitrary node -/

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::ext_equal`. -/
theorem nodes_eq_nodesFrom (l cs : Cells V) (h : cs = l) :
    nodes l = nodesFrom l 0 cs := by
  subst h; rfl

/-- Split the ownership of the node of index `i` out of `nodes`.  This is the
counterpart of Verus' `tracked_borrow` at index `i`.

*Verus/`vstd` counterpart:* `vstd::map::Map::tracked_borrow` at an index. -/
theorem nodes_split (l : Cells V) (i : Nat) (r : Ptr (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    nodes l =
      iprop(nodesFrom l 0 (l.take i) ∗
        ((r ↦ nodeAt l i v) ∗ nodesFrom l (i + 1) (l.drop (i + 1)))) := by
  have hdrop : l.drop i = (r, v) :: l.drop (i + 1) := by
    grind [List.drop_eq_getElem_cons]
  rw [nodes_eq_nodesFrom l (l.take i ++ ((r, v) :: l.drop (i + 1)))
      (by rw [← hdrop, List.take_append_drop]),
    nodesFrom_append, Nat.zero_add, nodesFrom_cons]
  grind

/-- Reading the node of index `i` yields exactly the node the well-formedness
invariant predicts, and leaves the list untouched.

*Verus/`vstd` counterpart:* `vstd::ptr::PPtr::borrow` under a `tracked` borrow of the map. -/
theorem nodes_read (l : Cells V) (i : Nat) (r : Ptr (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    ⦃ nodes l ⦄ read r ⦃⇓ node => ⌜node = nodeAt l i v⌝ ∗ nodes l⦄ := by
  rw [nodes_split l i r v h]
  sl_step*

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::dom` membership from the `len` invariant. -/
theorem exists_cell (l : Cells V) (i : Nat) (hi : i < l.length) :
    ∃ r v, l[i]? = some (r, v) :=
  ⟨(l[i]'hi).1, (l[i]'hi).2, by rw [List.getElem?_eq_getElem hi]⟩

/-! ## Recovering the ghost state from a view -/

/-- *Verus/`vstd` counterpart:* `vstd::seq_lib::lemma_seq_properties` + `Seq::drop_last`. -/
theorem view_eq_snoc (l : Cells V) (vs : List V) (v : V) (h : view l = vs ++ [v]) :
    ∃ l' r, l = l' ++ [(r, v)] ∧ view l' = vs := by
  rcases eq_nil_or_snoc l with rfl | ⟨l', ⟨r, w⟩, rfl⟩
  · simp [view] at h
  · rw [view_append] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj' h (by simp)
    exact ⟨l', r, by simp only [view, List.map_cons] at h₂; grind, h₁⟩

/-- *Verus/`vstd` counterpart:* `vstd::seq_lib::lemma_seq_properties` + `Seq::subrange`. -/
theorem view_eq_cons (l : Cells V) (v : V) (vs : List V) (h : view l = v :: vs) :
    ∃ r l', l = (r, v) :: l' ∧ view l' = vs := by
  cases l <;> grind [view]

end DoublyLinkedList

end Aeneas.SLPoC
