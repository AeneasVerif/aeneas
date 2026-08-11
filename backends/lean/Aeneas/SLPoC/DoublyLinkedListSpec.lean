import Aeneas.SLPoC.DoublyLinkedList
import Aeneas.SLPoC.VerusStd

/-!
# Doubly-linked list: specifications and proofs

Specifications and proofs for the executable definitions of
`Aeneas.SLPoC.DoublyLinkedList`, a port of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`).

The sequence and permission-map reasoning that Verus inherits from `vstd` lives
in `Aeneas.SLPoC.VerusStd`; what remains here is the ghost state of this
particular data structure and the specifications themselves.

The `*.spec` theorems state the Verus `requires`/`ensures` clauses over the
explicit ghost state; the `*.isList_spec` theorems restate them over the
abstract predicate, matching the Verus signatures literally.
-/

namespace Aeneas.SLPoC

open scoped SepLogic
open VerusStd

/-! ## Ghost state and the representation predicate

Verus tracks the pointers and their `PointsTo` permissions in ghost state stored
inside the list.  Here the permissions live in the separation-logic
precondition, and the ghost sequence of pointers is an ordinary parameter of the
specifications.

| Verus | Here |
|---|---|
| `PPtr<Node<V>>` + `PointsTo<Node<V>>` | `Ptr (Node V)` and the assertion `r ↦ node` |
| `ghost_state@.ptrs` / `points_to_map` | `Cells V`, a list of pointer/payload pairs |
| `well_formed_node(i)` | `nodeAt l i v`, the contents `nodesFrom` requires at index `i` |
| `well_formed()` | `wellFormed s l` |
| `self@` (`view`) | `view l` |
| `well_formed()` with the ghost state hidden | `isList s vs` |
| `Iterator::valid()` | `Iterator.valid it l` plus `wellFormed t l` in the precondition |
-/

namespace DoublyLinkedList

variable {V : Type}

/-- Ghost state of a list: the sequence of node pointers, each paired with the
payload the node holds.  This plays the role of Verus'
`ghost_state@.ptrs` zipped with `ghost_state@.points_to_map`. -/
abbrev Cells (V : Type) := List (Ptr (Node V) × V)

/-- Representation of the list as a sequence, i.e. Verus' `view`. -/
abbrev view (l : Cells V) : List V := payloads l

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
attribute [grind] prevOf nextOf nodeAt

/-- `nodesFrom l i cs` owns the nodes `cs`, which are the nodes of `l` starting
at index `i`: the permission map of `Aeneas.SLPoC.VerusStd` under the invariant
`nodeAt l`. -/
abbrev nodesFrom (l : Cells V) : Nat → Cells V → SLProp := cellsFrom (nodeAt l)

/-- Ownership of every node of the list, each of them well-formed.  This is the
separation-logic counterpart of the first conjunct of Verus'
`well_formed`. -/
def nodes (l : Cells V) : SLProp := nodesFrom l 0 l

/-- Linked list is well-formed: every node is well-formed, and the `head`/`tail`
pointers agree with the ghost state. -/
def wellFormed (s : DoublyLinkedList V) (l : Cells V) : SLProp :=
  iprop(⌜s.head = firstPtr l ∧ s.tail = lastPtr l⌝ ∗ nodes l)

/-- Abstract representation predicate: `s` is a well-formed list whose view is
`vs`.  The ghost state is hidden, as it is in Verus. -/
def isList (s : DoublyLinkedList V) (vs : List V) : SLProp :=
  iprop(∃ l : Cells V, ⌜view l = vs⌝ ∗ wellFormed s l)

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
This lemma replaces the pointwise `well_formed_node` triggers of the Verus
proof. -/
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

/-- Peeling the first node off `nodes` leaves the rest indexed from `1`; peeling
the second one leaves it indexed from `2`, which is the same as the rest of the
tail indexed from `1`. -/
@[sl_simps] theorem nodesFrom_cons_two (a b : Ptr (Node V) × V) (l xs : Cells V) :
    nodesFrom (a :: b :: l) 2 xs = nodesFrom (b :: l) 1 xs :=
  nodesFrom_cons_shift a (b :: l) xs 0

/-- Reading the node of index `i` yields exactly the node the well-formedness
invariant predicts, and leaves the list untouched. -/
theorem nodes_read (l : Cells V) (i : Nat) (r : Ptr (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    ⦃ nodes l ⦄ read r ⦃⇓ node => ⌜node = nodeAt l i v⌝ ∗ nodes l⦄ :=
  cellsFrom_read (nodeAt l) l i r v h

/-! ## Specifications

Each specification mirrors the `requires`/`ensures` clauses of the corresponding
Verus method.  Verus' `self.well_formed()` becomes the separation-logic
assertion `wellFormed s l`, and `self@` becomes `view l`. -/

/-- `new` returns a well-formed list whose view is empty. -/
theorem new.spec :
    ⦃ emp ⦄ (new : St (DoublyLinkedList V)) ⦃⇓ s => wellFormed s []⦄ := by
  unfold new
  sl_step*

/-- `pushEmptyCase` inserts one node into an empty list. -/
theorem pushEmptyCase.spec (s : DoublyLinkedList V) (v : V) :
    ⦃ wellFormed s [] ⦄ pushEmptyCase s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' [(r, v)]⦄ := by
  unfold pushEmptyCase
  sl_step*

/-- `pushBack` appends `v` to the list. -/
theorem pushBack.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushBack s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' (l ++ [(r, v)])⦄ := by
  unfold pushBack
  sl_pull ⟨hhead, htail⟩
  split
  · -- Special case: the list is empty
    rename_i hnone
    obtain rfl : l = [] := (lastPtr_eq_none_iff l).mp (by grind)
    apply triple_conseq (pushEmptyCase.spec s v)
      (by simp only [wellFormed]; sl_frame)
      (fun s' => by simp only [wellFormed, List.nil_append]; exact himpl_refl _)
  · rename_i oldTailPtr hsome
    -- The list is non-empty, hence of the shape `l' ++ [(oldTailPtr, vt)]`
    obtain ⟨l', ⟨rt, vt⟩, rfl⟩ : ∃ l' c, l = l' ++ [c] := by
      rcases eq_nil_or_snoc l with rfl | h
      · grind
      · exact h
    have hrt : oldTailPtr = rt := by grind [lastPtr_snoc]
    subst hrt
    simp only [show ∀ r : Ptr (Node V), l' ++ [(oldTailPtr, vt)] ++ [(r, v)] =
      l' ++ [(oldTailPtr, vt), (r, v)] from by simp]
    sl_step*

/-- `popBack` removes the last node and returns its payload. -/
theorem popBack.spec (s : DoublyLinkedList V) (l : Cells V) (rt : Ptr (Node V))
    (vt : V) :
    ⦃ wellFormed s (l ++ [(rt, vt)]) ⦄ popBack s
      ⦃⇓ (s', v) => ⌜v = vt⌝ ∗ wellFormed s' l⦄ := by
  unfold popBack
  sl_pull ⟨hhead, htail⟩
  simp only [lastPtr_snoc] at htail
  simp only [htail, get!_some]
  rcases eq_nil_or_snoc l with rfl | ⟨l'', ⟨rp, vp⟩, rfl⟩
  · -- The list had exactly one node: `head` and `tail` both become `none`
    simp only [List.nil_append] at hhead ⊢
    sl_step*
  · -- The list had at least two nodes: the penultimate one becomes the tail
    simp only [show l'' ++ [(rp, vp)] ++ [(rt, vt)] = l'' ++ [(rp, vp), (rt, vt)]
      from by simp] at hhead ⊢
    sl_step*

/-- `popBack` in the shape `step` can apply on its own.

`popBack.spec` mentions its ghost list under `++`, so `sl_frame` cannot recover
it from a precondition `wellFormed s [c₀, c₁, c₂]`: that is a higher-order match
the unifier will not solve.  Indexing the triple by the whole list instead makes
the precondition first-order, at the cost of a `l ≠ []` side condition and of a
postcondition phrased with `dropLast`/`getLast?` — both of which compute on a
concrete list, so `sl_side?` and the postcondition simp set discharge them. -/
theorem popBack.spec' (s : DoublyLinkedList V) (l : Cells V) (hne : l ≠ []) :
    ⦃ wellFormed s l ⦄ popBack s
      ⦃⇓ (s', v) => ⌜l.getLast?.map Prod.snd = some v⌝ ∗ wellFormed s' l.dropLast⦄ := by
  rcases eq_nil_or_snoc l with rfl | ⟨l', ⟨rt, vt⟩, rfl⟩
  · simp at hne
  · apply triple_conseq (popBack.spec s l' rt vt) (himpl_refl _)
    rintro ⟨s', v⟩
    simp only [List.getLast?_concat, List.dropLast_concat, Option.map_some]
    sl_frame

/-- `pushFront` prepends `v` to the list. -/
theorem pushFront.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushFront s v
      ⦃⇓ s' => ∃ r : Ptr (Node V), wellFormed s' ((r, v) :: l)⦄ := by
  unfold pushFront
  sl_pull ⟨hhead, htail⟩
  split
  · -- Special case: the list is empty
    rename_i hnone
    obtain rfl : l = [] := (firstPtr_eq_none_iff l).mp (by grind)
    apply triple_conseq (pushEmptyCase.spec s v)
      (by simp only [wellFormed]; sl_frame)
      (fun s' => by simp only [wellFormed]; exact himpl_refl _)
  · rename_i oldHeadPtr hsome
    cases l with
    | nil => grind
    | cons c l' =>
      obtain ⟨rh, vh⟩ := c
      obtain rfl : rh = oldHeadPtr := by grind
      sl_step*

/-- `popFront` removes the first node and returns its payload. -/
theorem popFront.spec (s : DoublyLinkedList V) (rh : Ptr (Node V)) (vh : V)
    (l : Cells V) :
    ⦃ wellFormed s ((rh, vh) :: l) ⦄ popFront s
      ⦃⇓ (s', v) => ⌜v = vh⌝ ∗ wellFormed s' l⦄ := by
  unfold popFront
  /- The cell has to be destructured: `nodes_cons_two`, which frame inference
     needs to split the two first nodes out, is stated over a pair. -/
  rcases l with _ | ⟨⟨r2, v2⟩, l'⟩ <;> sl_step*

/- `nodes_read` is registrable even though its `Prop` argument carries the index
and the payload, which neither the program term nor `sl_frame` determines: `step`
infers them by matching the argument against a local assumption, and every caller
below obtains one from `exists_cell`.  It is only enabled here, after the
specifications above: they own whole nodes rather than reading through the ghost
index, so letting `step` try it earlier leaves the index unconstrained. -/
attribute [step] nodes_read

/-! ## Specification of `get` -/

/-- The loop of `get` walks from index `j` to index `i`, keeping Verus' loop
invariant `ptr == ptrs[j]`. -/
theorem getLoop.spec (l : Cells V) (i j : Nat) (r : Ptr (Node V))
    (hji : j ≤ i) (hi : i < l.length) (hr : l[j]?.map Prod.fst = some r) :
    ⦃ nodes l ⦄ getLoop i j r
      ⦃⇓ r' => ⌜l[i]?.map Prod.fst = some r'⌝ ∗ nodes l⦄ := by
  have key : ∀ n j r, i - j = n → j ≤ i → l[j]?.map Prod.fst = some r →
      ⦃ nodes l ⦄ getLoop i j r
        ⦃⇓ r' => ⌜l[i]?.map Prod.fst = some r'⌝ ∗ nodes l⦄ := by
    intro n
    induction n with
    | zero =>
      intro j r hn hji hr
      obtain rfl : j = i := by omega
      rw [getLoop, if_neg (by omega)]
      sl_step*
    | succ n ih =>
      intro j r hn hji hr
      rw [getLoop, if_pos (by omega)]
      obtain ⟨rj, vj, hj⟩ := exists_cell l j (by omega)
      obtain rfl : r = rj := by grind
      obtain ⟨r', v', hj'⟩ := exists_cell l (j + 1) (by omega)
      sl_step
      have hnext : (nodeAt l j vj).next = some r' := by grind
      simp only [hnext, get!_some]
      exact ih (j + 1) r' (by omega) (by omega) (by rw [hj']; rfl)
  exact key (i - j) j r rfl hji hr

attribute [step] getLoop.spec

/-- `get` returns the `i`th element of the view. -/
theorem get.spec (s : DoublyLinkedList V) (l : Cells V) (i : Nat)
    (hi : i < l.length) :
    ⦃ wellFormed s l ⦄ get s i
      ⦃⇓ v => ⌜(view l)[i]? = some v⌝ ∗ wellFormed s l⦄ := by
  unfold get
  sl_pull ⟨hhead, htail⟩
  obtain ⟨r0, v0, h0⟩ := exists_cell l 0 (by omega)
  have hhead' : s.head = some r0 := by grind
  simp only [hhead', get!_some]
  sl_step as ⟨ r, hr ⟩
  obtain ⟨ri, vi, hi'⟩ := exists_cell l i hi
  obtain rfl : r = ri := by grind
  sl_step*

/- Specifications `step` can apply on its own: the program term fixes the
receiver, `sl_frame` fixes the ghost list by matching `nodes ?l`, and `sl_side?`
discharges the remaining `Prop` arguments.  A specification is *not* registrable
when its ghost list only occurs under `++` (`popBack.spec`, hence the restated
`popBack.spec'`), which the unifier will not solve. -/
attribute [step]
  new.spec pushBack.spec pushFront.spec popFront.spec get.spec popBack.spec'

/- `pushBack`/`pushFront` grow the ghost list with `++` and `::`, and
`popBack.spec'` shrinks it with `dropLast`.  Normalising all three keeps the
list a literal between steps; otherwise the unifier has to `whnf` through an
unreduced `dropLast` at the next call, which is where `run.spec` used to spend
its whole heartbeat budget. -/
attribute [step_post_simps]
  List.nil_append List.cons_append List.append_assoc
  List.dropLast_cons₂ List.dropLast_nil
  List.getLast?_cons_cons List.getLast?_singleton Option.map_some

/-! ## Ghost-free specifications

Verus' `well_formed` and `view` are `closed` specification functions: clients
only see the sequence of payloads.  `isList s vs` is the corresponding abstract
predicate, and the specifications below are literal transcriptions of the Verus
`requires`/`ensures` clauses. -/

/-- Verus: `ensures s.well_formed(), s@.len() == 0`. -/
theorem new.isList_spec :
    ⦃ emp ⦄ (new : St (DoublyLinkedList V)) ⦃⇓ s => isList s []⦄ := by
  sl_conseq new.spec

/-- Verus: `ensures final(self).well_formed(), final(self)@ == old(self)@.push(v)`. -/
theorem pushBack.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s vs ⦄ pushBack s v ⦃⇓ s' => isList s' (vs ++ [v])⦄ := by
  sl_pull l rfl
  sl_conseq (pushBack.spec s l v)

/-- Verus: `ensures final(self).well_formed(), final(self)@ == seq![v].add(old(self)@)`. -/
theorem pushFront.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s vs ⦄ pushFront s v ⦃⇓ s' => isList s' (v :: vs)⦄ := by
  sl_pull l rfl
  sl_conseq (pushFront.spec s l v)

/-- Verus: `requires old(self)@.len() > 0`,
`ensures final(self)@ == old(self)@.drop_last(), v == old(self)@[len - 1]`. -/
theorem popBack.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s (vs ++ [v]) ⦄ popBack s
      ⦃⇓ (s', w) => ⌜w = v⌝ ∗ isList s' vs⦄ := by
  sl_pull l hview
  obtain ⟨l', r, rfl, hl'⟩ := payloads_eq_snoc l vs v hview
  sl_conseq (popBack.spec s l' r v)

/-- Verus: `requires old(self)@.len() > 0`,
`ensures final(self)@ == old(self)@.subrange(1, len), v == old(self)@[0]`. -/
theorem popFront.isList_spec (s : DoublyLinkedList V) (v : V) (vs : List V) :
    ⦃ isList s (v :: vs) ⦄ popFront s
      ⦃⇓ (s', w) => ⌜w = v⌝ ∗ isList s' vs⦄ := by
  sl_pull l hview
  obtain ⟨r, l', rfl, hl'⟩ := payloads_eq_cons l v vs hview
  sl_conseq (popFront.spec s r v l')

/-- Verus: `requires 0 <= i < self@.len()`, `ensures *v == self@[i as int]`. -/
theorem get.isList_spec (s : DoublyLinkedList V) (vs : List V) (i : Nat)
    (hi : i < vs.length) :
    ⦃ isList s vs ⦄ get s i ⦃⇓ w => ⌜vs[i]? = some w⌝ ∗ isList s vs⦄ := by
  sl_pull l rfl
  sl_conseq (get.spec s l i (by simpa using hi))

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
theorem new.spec (t : DoublyLinkedList V) (l : Cells V) (hne : 0 < l.length) :
    ⦃ wellFormed t l ⦄ Iterator.new t
      ⦃⇓ it => ⌜it.l = t ∧ it.index = 0 ∧ valid it l⌝ ∗ wellFormed t l⦄ := by
  unfold Iterator.new
  sl_pull ⟨hhead, htail⟩
  have hv : valid ({ l := t, cur := t.head, index := 0 } : Iterator V) l :=
    ⟨hne, hhead⟩
  sl_step*

/-- The iterator yields the element of the view at its index. -/
theorem value.spec (it : Iterator V) (l : Cells V) (hvalid : valid it l) :
    ⦃ wellFormed it.l l ⦄ it.value
      ⦃⇓ v => ⌜(view l)[it.index]? = some v⌝ ∗ wellFormed it.l l⦄ := by
  unfold Iterator.value
  obtain ⟨hidx, hcur⟩ := hvalid
  obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx
  have hcur' : it.cur = some r := by grind
  simp only [hcur', get!_some]
  sl_step*

/-- Advancing the iterator: it reports whether there still is an element, and
if so it becomes valid again at the next index.  The unconditional `index` and
the `cur` of the exhausted case are what rule out an implementation that leaves
the iterator untouched at the last node. -/
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
  have hcur' : it.cur = some r := by grind
  simp only [hcur', get!_some]
  sl_step
  by_cases hlast : it.index + 1 = l.length
  · -- The iterator was on the last node
    simp only [nodeAt, nextOf, if_pos hlast]
    sl_step*
  · -- There is a next node
    obtain ⟨r', v', hcell'⟩ := exists_cell l (it.index + 1) (by omega)
    simp only [nodeAt, nextOf, if_neg hlast, hcell', Option.map_some]
    have hv :
        valid ({ it with cur := some r', index := it.index + 1 } : Iterator V) l :=
      ⟨show it.index + 1 < l.length by omega, by grind⟩
    sl_step*

attribute [step] new.spec value.spec moveNext.spec

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

/-! ## Frame inference through the abstract predicate

`isList` is an existential, so a caller that owns it as a single opaque
assertion exercises the frame inference of `sl_frame` on an `hexists` atom. -/


end Aeneas.SLPoC
