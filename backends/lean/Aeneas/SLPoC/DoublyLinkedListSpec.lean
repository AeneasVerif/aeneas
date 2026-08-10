import Aeneas.SLPoC.DoublyLinkedList
import Aeneas.SLPoC.Step

/-!
# Doubly-linked list: ghost state, specifications and proofs

Specifications and proofs for the executable definitions of
`Aeneas.SLPoC.DoublyLinkedList`, a port of the Verus doubly-linked-list example
(`https://github.com/verus-lang/verus/blob/main/examples/doubly_linked.rs`).

Verus tracks the pointers and their `PointsTo` permissions in ghost state stored
inside the list.  Here the permissions live in the separation-logic
precondition, and the ghost sequence of pointers is an ordinary parameter of the
specifications: `Cells V` plays the role of Verus' `ghost_state@.ptrs` zipped
with the payloads of `ghost_state@.points_to_map`.

Correspondence with the Verus development:

| Verus | Here |
|---|---|
| `PPtr<Node<V>>` + `PointsTo<Node<V>>` | `Ref (Node V)` and the assertion `r ↦ node` |
| `ghost_state@.ptrs` / `points_to_map` | `Cells V`, a list of pointer/payload pairs |
| `well_formed_node(i)` | `nodeAt l i v`, the contents `nodesFrom` requires at index `i` |
| `well_formed()` | `wellFormed s l` |
| `self@` (`view`) | `view l` |
| `well_formed()` with the ghost state hidden | `isList s vs` |
| `Iterator::valid()` | `Iterator.valid it l` plus `wellFormed t l` in the precondition |

The `*.spec` theorems state the Verus `requires`/`ensures` clauses over the
explicit ghost state; the `*.isList_spec` theorems restate them over the
abstract predicate, matching the Verus signatures literally.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## Ghost state and the representation predicate -/

namespace DoublyLinkedList

variable {V : Type}

/-- Ghost state of a list: the sequence of node pointers, each paired with the
payload the node holds.  This plays the role of Verus'
`ghost_state@.ptrs` zipped with `ghost_state@.points_to_map`. -/
abbrev Cells (V : Type) := List (Ref (Node V) × V)

/-- Representation of the list as a sequence, i.e. Verus' `view`. -/
def view (l : Cells V) : List V := l.map Prod.snd

/-- Pointer to the first node, if any. -/
def headPtr (l : Cells V) : Option (Ref (Node V)) := l.head?.map Prod.fst

/-- Pointer to the last node, if any. -/
def lastPtr (l : Cells V) : Option (Ref (Node V)) := l.getLast?.map Prod.fst

/-- Pointer to the node of index `i - 1`, or `none` if `i` is `0`. -/
def prevOf (l : Cells V) (i : Nat) : Option (Ref (Node V)) :=
  if i = 0 then none else l[i - 1]?.map Prod.fst

/-- Pointer to the node of index `i + 1`, or `none` if `i` is the last index. -/
def nextOf (l : Cells V) (i : Nat) : Option (Ref (Node V)) :=
  if i + 1 = l.length then none else l[i + 1]?.map Prod.fst

/-- Contents of the node of index `i`, whose payload is `v`.  Verus'
`well_formed_node` states that the node stored at `ptrs[i]` is exactly this. -/
def nodeAt (l : Cells V) (i : Nat) (v : V) : Node V :=
  { prev := prevOf l i, next := nextOf l i, payload := v }

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

@[simp] theorem view_nil : view ([] : Cells V) = [] := rfl

@[simp] theorem view_cons (c : Ref (Node V) × V) (l : Cells V) :
    view (c :: l) = c.2 :: view l := rfl

@[simp] theorem view_append (l₁ l₂ : Cells V) :
    view (l₁ ++ l₂) = view l₁ ++ view l₂ := List.map_append ..

@[simp] theorem view_length (l : Cells V) : (view l).length = l.length := by
  simp [view]

theorem view_getElem? (l : Cells V) (i : Nat) :
    (view l)[i]? = l[i]?.map Prod.snd := by
  simp [view]

@[simp] theorem nodesFrom_nil (l : Cells V) (i : Nat) :
    nodesFrom l i [] = emp := rfl

@[simp] theorem nodesFrom_cons (l : Cells V) (i : Nat) (r : Ref (Node V))
    (v : V) (rest : Cells V) :
    nodesFrom l i ((r, v) :: rest) =
      iprop((r ↦ nodeAt l i v) ∗ nodesFrom l (i + 1) rest) := rfl

@[simp] theorem nodes_nil : nodes ([] : Cells V) = emp := rfl

@[simp] theorem prevOf_zero (l : Cells V) : prevOf l 0 = none := by
  simp [prevOf]

@[simp] theorem headPtr_nil : headPtr ([] : Cells V) = none := rfl

@[simp] theorem lastPtr_nil : lastPtr ([] : Cells V) = none := rfl

/-! ## Structural lemmas about `nodesFrom` -/

/-- `nodesFrom` only depends on the `prev`/`next` pointers of the nodes it
owns.  This lemma replaces the pointwise `well_formed_node` triggers of the
Verus proof. -/
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
    simp only [Nat.add_zero] at h0
    have hrest : nodesFrom l₁ (i₁ + 1) cs = nodesFrom l₂ (i₂ + 1) cs := by
      refine ih (i₁ + 1) (i₂ + 1) fun k hk => ?_
      have h' := h (k + 1) (by simpa using hk)
      have e₁ : i₁ + 1 + k = i₁ + (k + 1) := by omega
      have e₂ : i₂ + 1 + k = i₂ + (k + 1) := by omega
      rw [e₁, e₂]
      exact h'
    simp only [nodesFrom_cons, nodeAt, h0.1, h0.2, hrest]

/-- Ownership of a concatenation splits into ownership of the two parts. -/
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

@[simp] theorem nodesFrom_singleton (l : Cells V) (i : Nat) (r : Ref (Node V))
    (v : V) :
    nodesFrom l i [(r, v)] = iprop(r ↦ nodeAt l i v) := by
  simp [hstar_hempty_r_eq]

/-! ## How `prevOf`/`nextOf` react to `++` and `::` -/

theorem prevOf_append_left (l₁ l₂ : Cells V) (i : Nat) (h : i < l₁.length) :
    prevOf (l₁ ++ l₂) i = prevOf l₁ i := by
  unfold prevOf
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, if_false]
    rw [List.getElem?_append_left (by omega)]

theorem nextOf_append_left (l₁ l₂ : Cells V) (i : Nat) (h : i + 1 < l₁.length) :
    nextOf (l₁ ++ l₂) i = nextOf l₁ i := by
  unfold nextOf
  have h₁ : ¬ (i + 1 = (l₁ ++ l₂).length) := by
    simp only [List.length_append]; omega
  have h₂ : ¬ (i + 1 = l₁.length) := by omega
  simp only [h₁, h₂, if_false]
  rw [List.getElem?_append_left h]

theorem prevOf_cons_succ (c : Ref (Node V) × V) (l : Cells V) (i : Nat) :
    prevOf (c :: l) (i + 2) = prevOf l (i + 1) := by
  simp [prevOf]

theorem nextOf_cons_succ (c : Ref (Node V) × V) (l : Cells V) (i : Nat) :
    nextOf (c :: l) (i + 1) = nextOf l i := by
  simp only [nextOf, List.length_cons, List.getElem?_cons_succ]
  split <;> split <;> first | rfl | omega

/-- Appending a node at the end does not change the nodes strictly before the
last one. -/
theorem nodesFrom_append_prefix (l₁ l₂ : Cells V) (xs : Cells V) (i : Nat)
    (h : i + xs.length < l₁.length) :
    nodesFrom (l₁ ++ l₂) i xs = nodesFrom l₁ i xs := by
  refine nodesFrom_congr xs i i fun k hk => ?_
  exact ⟨prevOf_append_left l₁ l₂ (i + k) (by omega),
    nextOf_append_left l₁ l₂ (i + k) (by omega)⟩

/-- Prepending a node shifts all the indices by one. -/
theorem nodesFrom_cons_shift (c : Ref (Node V) × V) (l : Cells V) (xs : Cells V)
    (i : Nat) :
    nodesFrom (c :: l) (i + 2) xs = nodesFrom l (i + 1) xs := by
  refine nodesFrom_congr xs (i + 2) (i + 1) fun k _ => ?_
  have e : i + 2 + k = (i + k) + 2 := by omega
  have e' : i + 1 + k = (i + k) + 1 := by omega
  rw [e, e', prevOf_cons_succ, nextOf_cons_succ]
  exact ⟨rfl, rfl⟩

/-! ## Decomposition of `nodes` at the two ends of the list -/

@[simp] theorem headPtr_cons (c : Ref (Node V) × V) (l : Cells V) :
    headPtr (c :: l) = some c.1 := rfl

@[simp] theorem lastPtr_snoc (l : Cells V) (c : Ref (Node V) × V) :
    lastPtr (l ++ [c]) = some c.1 := by
  simp [lastPtr]

@[simp] theorem lastPtr_singleton (c : Ref (Node V) × V) :
    lastPtr [c] = some c.1 := rfl

@[sl_simps] theorem lastPtr_cons_cons (a b : Ref (Node V) × V) (l : Cells V) :
    lastPtr (a :: b :: l) = lastPtr (b :: l) := by
  simp [lastPtr]

theorem prevOf_cons_one (c : Ref (Node V) × V) (l : Cells V) :
    prevOf (c :: l) 1 = some c.1 := by
  simp [prevOf]

theorem nextOf_cons_zero (c : Ref (Node V) × V) (l : Cells V) :
    nextOf (c :: l) 0 = headPtr l := by
  cases l with
  | nil => simp [nextOf]
  | cons a l => simp [nextOf, headPtr]

theorem prevOf_snoc_last (l : Cells V) (c : Ref (Node V) × V) :
    prevOf (l ++ [c]) l.length = lastPtr l := by
  unfold prevOf lastPtr
  by_cases h : l.length = 0
  · rw [h]
    simp [List.eq_nil_of_length_eq_zero h]
  · rw [if_neg h, List.getElem?_append_left (by omega),
      List.getLast?_eq_getElem?]

theorem nextOf_snoc_last (l : Cells V) (c : Ref (Node V) × V) :
    nextOf (l ++ [c]) l.length = none := by
  simp [nextOf]

theorem nodeAt_snoc_last (l : Cells V) (r : Ref (Node V)) (v : V) :
    nodeAt (l ++ [(r, v)]) l.length v =
      { prev := lastPtr l, next := none, payload := v } := by
  unfold nodeAt
  rw [prevOf_snoc_last, nextOf_snoc_last]

/-- Split the ownership of the last node out of `nodes`. -/
@[sl_simps] theorem nodes_snoc (l : Cells V) (r : Ref (Node V)) (v : V) :
    nodes (l ++ [(r, v)]) =
      iprop(nodesFrom (l ++ [(r, v)]) 0 l ∗
        (r ↦ { prev := lastPtr l, next := none, payload := v })) := by
  unfold nodes
  rw [nodesFrom_append, Nat.zero_add, nodesFrom_singleton, nodeAt_snoc_last]

theorem getElem?_append_two_left (l : Cells V) (a b : Ref (Node V) × V) :
    (l ++ [a, b])[l.length]? = some a := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem getElem?_append_two_right (l : Cells V) (a b : Ref (Node V) × V) :
    (l ++ [a, b])[l.length + 1]? = some b := by
  rw [List.getElem?_append_right (by omega)]
  have e : l.length + 1 - l.length = 1 := by omega
  rw [e]
  simp

/-- Split the ownership of the last two nodes out of `nodes`.  This is the shape
of the heap both after `pushBack` and before `popBack`. -/
@[sl_simps high] theorem nodes_snoc_two (l : Cells V) (rt : Ref (Node V)) (vt : V)
    (rn : Ref (Node V)) (v : V) :
    nodes (l ++ [(rt, vt), (rn, v)]) =
      iprop(nodesFrom (l ++ [(rt, vt)]) 0 l ∗
        (rt ↦ { prev := lastPtr l, next := some rn, payload := vt }) ∗
        (rn ↦ { prev := some rt, next := none, payload := v })) := by
  have hassoc : l ++ [(rt, vt), (rn, v)] = (l ++ [(rt, vt)]) ++ [(rn, v)] := by
    simp
  have hlen : (l ++ [(rt, vt), (rn, v)]).length = l.length + 2 := by simp
  have hprefix :
      nodesFrom (l ++ [(rt, vt), (rn, v)]) 0 l = nodesFrom (l ++ [(rt, vt)]) 0 l := by
    rw [hassoc]
    exact nodesFrom_append_prefix _ _ _ _ (by simp)
  have hmid : nodeAt (l ++ [(rt, vt), (rn, v)]) l.length vt =
      { prev := lastPtr l, next := some rn, payload := vt } := by
    unfold nodeAt
    have hprev : prevOf (l ++ [(rt, vt), (rn, v)]) l.length = lastPtr l := by
      rw [hassoc, prevOf_append_left _ _ _ (by simp), prevOf_snoc_last]
    have hnext : nextOf (l ++ [(rt, vt), (rn, v)]) l.length = some rn := by
      unfold nextOf
      rw [hlen, if_neg (by omega), getElem?_append_two_right]
      rfl
    rw [hprev, hnext]
  have hlast : nodeAt (l ++ [(rt, vt), (rn, v)]) (l.length + 1) v =
      { prev := some rt, next := none, payload := v } := by
    unfold nodeAt
    have hprev : prevOf (l ++ [(rt, vt), (rn, v)]) (l.length + 1) = some rt := by
      unfold prevOf
      rw [if_neg (by omega)]
      have e : l.length + 1 - 1 = l.length := by omega
      rw [e, getElem?_append_two_left]
      rfl
    have hnext : nextOf (l ++ [(rt, vt), (rn, v)]) (l.length + 1) = none := by
      unfold nextOf
      rw [hlen, if_pos (by omega)]
    rw [hprev, hnext]
  unfold nodes
  rw [nodesFrom_append, Nat.zero_add, hprefix]
  simp only [nodesFrom_cons, nodesFrom_nil, hstar_hempty_r_eq, hmid, hlast]

/-- Split the ownership of the first node out of `nodes`. -/
@[sl_simps] theorem nodes_cons (rh : Ref (Node V)) (vh : V) (l : Cells V) :
    nodes ((rh, vh) :: l) =
      iprop((rh ↦ { prev := none, next := headPtr l, payload := vh }) ∗
        nodesFrom ((rh, vh) :: l) 1 l) := by
  unfold nodes
  rw [nodesFrom_cons, Nat.zero_add]
  unfold nodeAt
  rw [prevOf_zero, nextOf_cons_zero]

/-- Split the ownership of the first two nodes out of `nodes`.  This is the
shape of the heap both after `pushFront` and before `popFront`. -/
@[sl_simps high] theorem nodes_cons_two (rn : Ref (Node V)) (v : V) (rh : Ref (Node V)) (vh : V)
    (l : Cells V) :
    nodes ((rn, v) :: (rh, vh) :: l) =
      iprop((rn ↦ { prev := none, next := some rh, payload := v }) ∗
        (rh ↦ { prev := some rn, next := headPtr l, payload := vh }) ∗
        nodesFrom ((rh, vh) :: l) 1 l) := by
  unfold nodes
  have hfirst : nodeAt ((rn, v) :: (rh, vh) :: l) 0 v =
      { prev := none, next := some rh, payload := v } := by
    unfold nodeAt
    rw [prevOf_zero, nextOf_cons_zero]
    rfl
  have hsecond : nodeAt ((rn, v) :: (rh, vh) :: l) 1 vh =
      { prev := some rn, next := headPtr l, payload := vh } := by
    unfold nodeAt
    rw [prevOf_cons_one]
    have : nextOf ((rn, v) :: (rh, vh) :: l) 1 = headPtr l := by
      rw [show (1 : Nat) = 0 + 1 from rfl, nextOf_cons_succ, nextOf_cons_zero]
    rw [this]
  have hrest : nodesFrom ((rn, v) :: (rh, vh) :: l) 2 l =
      nodesFrom ((rh, vh) :: l) 1 l :=
    nodesFrom_cons_shift (rn, v) ((rh, vh) :: l) l 0
  simp only [nodesFrom_cons, Nat.zero_add, hfirst, hsecond]
  rw [show (1 + 1 : Nat) = 2 from rfl, hrest]

/-! ## Auxiliary facts used by the specifications -/

@[simp] theorem get!_some {α : Type} [Inhabited α] (a : α) :
    (some a).get! = a := rfl

/-- Every list is either empty or ends with a node. -/
theorem eq_nil_or_snoc (l : Cells V) : l = [] ∨ ∃ l' c, l = l' ++ [c] := by
  rcases l.eq_nil_or_concat with h | ⟨l', c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', c, by simpa [List.concat_eq_append] using h⟩

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` tail can only
come from an empty list. -/
theorem lastPtr_eq_none_iff (l : Cells V) : lastPtr l = none ↔ l = [] := by
  constructor
  · intro h
    rcases l.eq_nil_or_concat with h' | ⟨l', c, h'⟩
    · exact h'
    · rw [h', List.concat_eq_append] at h
      simp at h
  · rintro rfl; rfl

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` head can only
come from an empty list. -/
theorem headPtr_eq_none_iff (l : Cells V) : headPtr l = none ↔ l = [] := by
  cases l <;> simp [headPtr]

@[sl_simps] theorem headPtr_append_two (l : Cells V) (a b : Ref (Node V) × V) :
    headPtr (l ++ [a, b]) = headPtr (l ++ [a]) := by
  cases l <;> rfl

@[sl_simps] theorem lastPtr_append_two (l : Cells V) (a b : Ref (Node V) × V) :
    lastPtr (l ++ [a, b]) = some b.1 := by
  rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp, lastPtr_snoc]

/-! ## Specifications

Each specification mirrors the `requires`/`ensures` clauses of the corresponding
Verus method.  Verus' `self.well_formed()` becomes the separation-logic
assertion `wellFormed s l`, and `self@` becomes `view l`. -/

/-- `new` returns a well-formed list whose view is empty. -/
theorem new.spec :
    ⦃ emp ⦄ (new : St (DoublyLinkedList V)) ⦃⇓ s => wellFormed s []⦄ := by
  unfold new
  step* by sl_frame

/-- `pushEmptyCase` inserts one node into an empty list. -/
theorem pushEmptyCase.spec (s : DoublyLinkedList V) (v : V) :
    ⦃ wellFormed s [] ⦄ pushEmptyCase s v
      ⦃⇓ s' => ∃ r : Ref (Node V), wellFormed s' [(r, v)]⦄ := by
  unfold pushEmptyCase
  sl_pull _
  step* by sl_frame

/-- `pushBack` appends `v` to the list. -/
theorem pushBack.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushBack s v
      ⦃⇓ s' => ∃ r : Ref (Node V), wellFormed s' (l ++ [(r, v)])⦄ := by
  unfold pushBack
  sl_pull ⟨hhead, htail⟩
  split
  · -- Special case: the list is empty
    rename_i hnone
    have hl : l = [] := (lastPtr_eq_none_iff l).mp (by rw [← htail, hnone])
    subst hl
    simp only [headPtr_nil, lastPtr_nil] at hhead htail
    apply triple_conseq (pushEmptyCase.spec s v)
    · simp only [wellFormed, nodes_nil, headPtr_nil, lastPtr_nil]
      sl_frame
    · intro s'
      simp only [wellFormed, List.nil_append]
      exact himpl_refl _
  · rename_i oldTailPtr hsome
    -- The list is non-empty, hence of the shape `l' ++ [(oldTailPtr, vt)]`
    obtain ⟨l', c, rfl⟩ : ∃ l' c, l = l' ++ [c] := by
      rcases l.eq_nil_or_concat with rfl | ⟨l', c, h⟩
      · rw [hsome] at htail; simp [lastPtr] at htail
      · exact ⟨l', c, by simpa [List.concat_eq_append] using h⟩
    obtain ⟨rt, vt⟩ := c
    have hrt : oldTailPtr = rt := by
      rw [hsome, lastPtr_snoc] at htail
      exact Option.some.inj htail
    subst hrt
    simp only [show ∀ r : Ref (Node V), l' ++ [(oldTailPtr, vt)] ++ [(r, v)] =
      l' ++ [(oldTailPtr, vt), (r, v)] from by simp]
    step* by sl_frame

/-- `popBack` removes the last node and returns its payload. -/
theorem popBack.spec (s : DoublyLinkedList V) (l : Cells V) (rt : Ref (Node V))
    (vt : V) :
    ⦃ wellFormed s (l ++ [(rt, vt)]) ⦄ popBack s
      ⦃⇓ (s', v) => ⌜v = vt⌝ ∗ wellFormed s' l⦄ := by
  unfold popBack
  sl_pull ⟨hhead, htail⟩
  simp only [lastPtr_snoc] at htail
  simp only [htail, get!_some]
  rcases eq_nil_or_snoc l with rfl | ⟨l'', c, rfl⟩
  · -- The list had exactly one node: `head` and `tail` both become `none`
    simp only [List.nil_append] at hhead ⊢
    step* by sl_frame
  · -- The list had at least two nodes: the penultimate one becomes the tail
    obtain ⟨rp, vp⟩ := c
    simp only [show l'' ++ [(rp, vp)] ++ [(rt, vt)] = l'' ++ [(rp, vp), (rt, vt)]
      from by simp] at hhead ⊢
    step as ⟨ lastNode, hLastNode ⟩ by sl_frame
    subst hLastNode
    step* by sl_frame

/-- `pushFront` prepends `v` to the list. -/
theorem pushFront.spec (s : DoublyLinkedList V) (l : Cells V) (v : V) :
    ⦃ wellFormed s l ⦄ pushFront s v
      ⦃⇓ s' => ∃ r : Ref (Node V), wellFormed s' ((r, v) :: l)⦄ := by
  unfold pushFront
  sl_pull ⟨hhead, htail⟩
  split
  · -- Special case: the list is empty
    rename_i hnone
    have hl : l = [] := (headPtr_eq_none_iff l).mp (by rw [← hhead, hnone])
    subst hl
    simp only [headPtr_nil, lastPtr_nil] at hhead htail
    apply triple_conseq (pushEmptyCase.spec s v)
    · simp only [wellFormed, nodes_nil, headPtr_nil, lastPtr_nil]
      sl_frame
    · intro s'
      simp only [wellFormed]
      exact himpl_refl _
  · rename_i oldHeadPtr hsome
    cases l with
    | nil => rw [hsome] at hhead; simp [headPtr] at hhead
    | cons c l' =>
      obtain ⟨rh, vh⟩ := c
      obtain rfl : rh = oldHeadPtr := by
        rw [hsome, headPtr_cons] at hhead
        exact (Option.some.inj hhead).symm
      step* by sl_frame

/-- `popFront` removes the first node and returns its payload. -/
theorem popFront.spec (s : DoublyLinkedList V) (rh : Ref (Node V)) (vh : V)
    (l : Cells V) :
    ⦃ wellFormed s ((rh, vh) :: l) ⦄ popFront s
      ⦃⇓ (s', v) => ⌜v = vh⌝ ∗ wellFormed s' l⦄ := by
  unfold popFront
  sl_pull ⟨hhead, htail⟩
  simp only [headPtr_cons] at hhead
  simp only [hhead, get!_some]
  cases l with
  | nil =>
    -- The list had exactly one node: `head` and `tail` both become `none`
    step* by sl_frame
  | cons c l' =>
    -- The list had at least two nodes: the second one becomes the head
    obtain ⟨r2, v2⟩ := c
    step as ⟨ firstNode, hFirstNode ⟩ by sl_frame
    subst hFirstNode
    step* by sl_frame

/-! ## Reading an arbitrary node -/

theorem nodes_eq_nodesFrom (l cs : Cells V) (h : cs = l) :
    nodes l = nodesFrom l 0 cs := by
  subst h; rfl

/-- Split the ownership of the node of index `i` out of `nodes`.  This is the
counterpart of Verus' `tracked_borrow` at index `i`. -/
theorem nodes_split (l : Cells V) (i : Nat) (r : Ref (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    nodes l =
      iprop(nodesFrom l 0 (l.take i) ∗
        ((r ↦ nodeAt l i v) ∗ nodesFrom l (i + 1) (l.drop (i + 1)))) := by
  have hi : i < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    simp at h
  have hget : l[i] = (r, v) :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h)
  have hdrop : l.drop i = (r, v) :: l.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hlen : (l.take i).length = i := by
    rw [List.length_take]; omega
  rw [nodes_eq_nodesFrom l (l.take i ++ ((r, v) :: l.drop (i + 1)))
      (by rw [← hdrop, List.take_append_drop]),
    nodesFrom_append, hlen, Nat.zero_add, nodesFrom_cons]

/-- Reading the node of index `i` yields exactly the node the well-formedness
invariant predicts, and leaves the list untouched. -/
theorem nodes_read (l : Cells V) (i : Nat) (r : Ref (Node V)) (v : V)
    (h : l[i]? = some (r, v)) :
    ⦃ nodes l ⦄ read r ⦃⇓ node => ⌜node = nodeAt l i v⌝ ∗ nodes l⦄ := by
  rw [nodes_split l i r v h]
  step* by sl_frame

theorem exists_cell (l : Cells V) (i : Nat) (hi : i < l.length) :
    ∃ r v, l[i]? = some (r, v) :=
  ⟨(l[i]'hi).1, (l[i]'hi).2, by rw [List.getElem?_eq_getElem hi]⟩

theorem headPtr_eq_getElem? (l : Cells V) : headPtr l = l[0]?.map Prod.fst := by
  cases l <;> rfl

/-! ## Specification of `get` -/

/-- The loop of `get` walks from index `j` to index `i`, keeping Verus' loop
invariant `ptr == ptrs[j]`. -/
theorem getLoop.spec (l : Cells V) (i j : Nat) (r : Ref (Node V))
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
      step* by sl_frame
    | succ n ih =>
      intro j r hn hji hr
      rw [getLoop, if_pos (by omega)]
      obtain ⟨rj, vj, hj⟩ := exists_cell l j (by omega)
      have he : some rj = some r := by rw [hj] at hr; exact hr
      obtain rfl : r = rj := (Option.some.inj he).symm
      obtain ⟨r', v', hj'⟩ := exists_cell l (j + 1) (by omega)
      step with nodes_read l j r vj hj as ⟨ node, hnode ⟩ by sl_frame
      subst hnode
      have hnext : (nodeAt l j vj).next = some r' := by
        simp only [nodeAt, nextOf, if_neg (show j + 1 ≠ l.length by omega), hj']
        rfl
      simp only [hnext, get!_some, hstar_hempty_r_eq]
      exact ih (j + 1) r' (by omega) (by omega) (by rw [hj']; rfl)
  exact key (i - j) j r rfl hji hr

/-- `get` returns the `i`th element of the view. -/
theorem get.spec (s : DoublyLinkedList V) (l : Cells V) (i : Nat)
    (hi : i < l.length) :
    ⦃ wellFormed s l ⦄ get s i
      ⦃⇓ v => ⌜(view l)[i]? = some v⌝ ∗ wellFormed s l⦄ := by
  unfold get
  sl_pull ⟨hhead, htail⟩
  obtain ⟨r0, v0, h0⟩ := exists_cell l 0 (by omega)
  have hhead' : s.head = some r0 := by
    rw [hhead, headPtr_eq_getElem?, h0]; rfl
  rw [hhead']
  simp only [get!_some]
  step with getLoop.spec l i 0 r0 (by omega) hi (by rw [h0]; rfl)
    as ⟨ r, hr ⟩ by sl_frame
  obtain ⟨ri, vi, hi'⟩ := exists_cell l i hi
  obtain rfl : r = ri := (Option.some.inj (by rw [hi'] at hr; exact hr)).symm
  have hview : (view l)[i]? = some vi := by rw [view_getElem?, hi']; rfl
  have hpay : (nodeAt l i vi).payload = vi := rfl
  step with nodes_read l i r vi hi' as ⟨ node, hnode ⟩ by sl_frame
  subst hnode
  step* by sl_frame

/-! ## Ghost-free specifications

Verus' `well_formed` and `view` are `closed` specification functions: clients
only see the sequence of payloads.  `isList s vs` is the corresponding abstract
predicate, and the specifications below are literal transcriptions of the Verus
`requires`/`ensures` clauses. -/

theorem view_eq_snoc (l : Cells V) (vs : List V) (v : V) (h : view l = vs ++ [v]) :
    ∃ l' r, l = l' ++ [(r, v)] ∧ view l' = vs := by
  rcases eq_nil_or_snoc l with rfl | ⟨l', c, rfl⟩
  · simp [view] at h
  · obtain ⟨r, w⟩ := c
    rw [view_append] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj' h (by simp)
    have hw : w = v := by simpa [view] using h₂
    exact ⟨l', r, by rw [hw], h₁⟩

theorem view_eq_cons (l : Cells V) (v : V) (vs : List V) (h : view l = v :: vs) :
    ∃ r l', l = (r, v) :: l' ∧ view l' = vs := by
  cases l with
  | nil => simp [view] at h
  | cons c l' =>
    obtain ⟨r, w⟩ := c
    rw [view_cons] at h
    have hw : w = v := (List.cons.inj h).1
    exact ⟨r, l', by rw [hw], (List.cons.inj h).2⟩

/-- Verus: `ensures s.well_formed(), s@.len() == 0`. -/
theorem new.isList_spec :
    ⦃ emp ⦄ (new : St (DoublyLinkedList V)) ⦃⇓ s => isList s []⦄ := by
  apply triple_conseq new.spec (himpl_refl _)
  intro s
  sl_frame

/-- Verus: `ensures final(self).well_formed(), final(self)@ == old(self)@.push(v)`. -/
theorem pushBack.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s vs ⦄ pushBack s v ⦃⇓ s' => isList s' (vs ++ [v])⦄ := by
  sl_pull l rfl
  apply triple_conseq (pushBack.spec s l v) (himpl_refl _)
  intro s'
  sl_frame

/-- Verus: `ensures final(self).well_formed(), final(self)@ == seq![v].add(old(self)@)`. -/
theorem pushFront.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s vs ⦄ pushFront s v ⦃⇓ s' => isList s' (v :: vs)⦄ := by
  sl_pull l rfl
  apply triple_conseq (pushFront.spec s l v) (himpl_refl _)
  intro s'
  sl_frame

/-- Verus: `requires old(self)@.len() > 0`,
`ensures final(self)@ == old(self)@.drop_last(), v == old(self)@[len - 1]`. -/
theorem popBack.isList_spec (s : DoublyLinkedList V) (vs : List V) (v : V) :
    ⦃ isList s (vs ++ [v]) ⦄ popBack s
      ⦃⇓ (s', w) => ⌜w = v⌝ ∗ isList s' vs⦄ := by
  sl_pull l hview
  obtain ⟨l', r, rfl, hl'⟩ := view_eq_snoc l vs v hview
  apply triple_conseq (popBack.spec s l' r v) (himpl_refl _)
  rintro ⟨s', w⟩
  sl_frame

/-- Verus: `requires old(self)@.len() > 0`,
`ensures final(self)@ == old(self)@.subrange(1, len), v == old(self)@[0]`. -/
theorem popFront.isList_spec (s : DoublyLinkedList V) (v : V) (vs : List V) :
    ⦃ isList s (v :: vs) ⦄ popFront s
      ⦃⇓ (s', w) => ⌜w = v⌝ ∗ isList s' vs⦄ := by
  sl_pull l hview
  obtain ⟨r, l', rfl, hl'⟩ := view_eq_cons l v vs hview
  apply triple_conseq (popFront.spec s r v l') (himpl_refl _)
  rintro ⟨s', w⟩
  sl_frame

/-- Verus: `requires 0 <= i < self@.len()`, `ensures *v == self@[i as int]`. -/
theorem get.isList_spec (s : DoublyLinkedList V) (vs : List V) (i : Nat)
    (hi : i < vs.length) :
    ⦃ isList s vs ⦄ get s i ⦃⇓ w => ⌜vs[i]? = some w⌝ ∗ isList s vs⦄ := by
  sl_pull l rfl
  apply triple_conseq (get.spec s l i (by simpa using hi)) (himpl_refl _)
  intro w
  sl_frame

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
    ⟨hne, by rw [hhead, headPtr_eq_getElem?]⟩
  step* by sl_frame

/-- The iterator yields the element of the view at its index. -/
theorem value.spec (it : Iterator V) (t : DoublyLinkedList V) (l : Cells V)
    (hl : it.l = t) (hvalid : valid it l) :
    ⦃ wellFormed t l ⦄ it.value
      ⦃⇓ v => ⌜(view l)[it.index]? = some v⌝ ∗ wellFormed t l⦄ := by
  subst hl
  unfold Iterator.value
  sl_pull ⟨hhead, htail⟩
  obtain ⟨hidx, hcur⟩ := hvalid
  obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx
  have hcur' : it.cur = some r := by rw [hcur, hcell]; rfl
  rw [hcur']
  simp only [get!_some]
  have hview : (view l)[it.index]? = some v := by rw [view_getElem?, hcell]; rfl
  have hpay : (nodeAt l it.index v).payload = v := rfl
  step with nodes_read l it.index r v hcell as ⟨ node, hnode ⟩ by sl_frame
  subst hnode
  step* by sl_frame

/-- Advancing the iterator: it reports whether there still is an element, and
if so it becomes valid again at the next index. -/
theorem moveNext.spec (it : Iterator V) (t : DoublyLinkedList V) (l : Cells V)
    (hl : it.l = t) (hvalid : valid it l) :
    ⦃ wellFormed t l ⦄ it.moveNext
      ⦃⇓ (it', good) =>
        ⌜it'.l = it.l ∧
          (good = true ↔ it.index + 1 < l.length) ∧
          (good = true → valid it' l ∧ it'.index = it.index + 1)⌝ ∗
        wellFormed t l⦄ := by
  subst hl
  unfold Iterator.moveNext
  sl_pull ⟨hhead, htail⟩
  obtain ⟨hidx, hcur⟩ := hvalid
  obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx
  have hcur' : it.cur = some r := by rw [hcur, hcell]; rfl
  rw [hcur']
  simp only [get!_some]
  step with nodes_read l it.index r v hcell as ⟨ node, hnode ⟩ by sl_frame
  subst hnode
  by_cases hlast : it.index + 1 = l.length
  · -- The iterator was on the last node
    simp only [nodeAt, nextOf, if_pos hlast]
    step* by sl_frame
  · -- There is a next node
    obtain ⟨r', v', hcell'⟩ := exists_cell l (it.index + 1) (by omega)
    simp only [nodeAt, nextOf, if_neg hlast, hcell', Option.map_some]
    have hidx' : it.index + 1 < l.length := by omega
    have hv :
        valid ({ it with cur := some r', index := it.index + 1 } : Iterator V) l :=
      ⟨hidx', by rw [hcell']; rfl⟩
    have hi' :
        ({ it with cur := some r', index := it.index + 1 } : Iterator V).index =
          it.index + 1 := rfl
    have hl' :
        ({ it with cur := some r', index := it.index + 1 } : Iterator V).l = it.l := rfl
    step* by sl_frame

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
  -- Build the list `1, 2, 3`
  step with DoublyLinkedList.new.spec as ⟨ t0 ⟩ by sl_frame
  step with DoublyLinkedList.pushBack.spec t0 [] 2 as ⟨ t1 ⟩ by sl_frame
  sl_pull r1
  step with DoublyLinkedList.pushBack.spec t1 [(r1, 2)] 3 as ⟨ t2 ⟩ by sl_frame
  sl_pull r2
  step with DoublyLinkedList.pushFront.spec t2 [(r1, 2), (r2, 3)] 1
    as ⟨ t3 ⟩ by sl_frame
  sl_pull r3
  -- Walk the list with an iterator
  step with Iterator.new.spec t3 [(r3, 1), (r1, 2), (r2, 3)] (by simp)
    as ⟨ it, hitl, hitidx, hitvalid ⟩ by sl_frame
  step with Iterator.value.spec it t3 _ hitl hitvalid as ⟨ v1, hv1 ⟩ by sl_frame
  step with Iterator.moveNext.spec it t3 _ hitl hitvalid
    as ⟨ m1, hm1l, hm1good, hm1next ⟩ by sl_frame
  obtain ⟨hvalid1, hidx1⟩ := hm1next (hm1good.mpr (by simp [hitidx]))
  step with Iterator.value.spec m1.1 t3 _ (hm1l.trans hitl) hvalid1
    as ⟨ v2, hv2 ⟩ by sl_frame
  step with Iterator.moveNext.spec m1.1 t3 _ (hm1l.trans hitl) hvalid1
    as ⟨ m2, hm2l, hm2good, hm2next ⟩ by sl_frame
  obtain ⟨hvalid2, hidx2⟩ := hm2next (hm2good.mpr (by rw [hidx1, hitidx]; simp))
  step with Iterator.value.spec m2.1 t3 _ (hm2l.trans (hm1l.trans hitl)) hvalid2
    as ⟨ v3, hv3 ⟩ by sl_frame
  step with Iterator.moveNext.spec m2.1 t3 _ (hm2l.trans (hm1l.trans hitl)) hvalid2
    as ⟨ m3, hm3l, hm3good, hm3next ⟩ by sl_frame
  -- Empty the list again
  step with DoublyLinkedList.popBack.spec t3 [(r3, 1), (r1, 2)] r2 3
    as ⟨ p1, ex ⟩ by sl_frame
  step with DoublyLinkedList.popFront.spec p1.1 r3 1 [(r1, 2)]
    as ⟨ p2, ey ⟩ by sl_frame
  step with DoublyLinkedList.popFront.spec p2.1 r1 2 [] as ⟨ p3, ez ⟩ by sl_frame
  -- Read off the observed values
  have e1 : v1 = 1 := by rw [hitidx] at hv1; simp [view] at hv1; omega
  have e2 : v2 = 2 := by rw [hidx1, hitidx] at hv2; simp [view] at hv2; omega
  have e3 : v3 = 3 := by rw [hidx2, hidx1, hitidx] at hv3; simp [view] at hv3; omega
  have eg : m3.2 = false := by
    have hnot : ¬ (m3.2 = true) := by rw [hm3good, hidx2, hidx1, hitidx]; simp
    simpa using hnot
  step* by sl_frame

end Example

/-! ## Frame inference through the abstract predicate

`isList` is an existential, so a caller that owns it as a single opaque
assertion exercises the frame inference of `sl_frame` on an `hexists` atom. -/

namespace FrameInferenceTest

open DoublyLinkedList

/-- Frame inference works when the callee's precondition is an abstract
representation predicate defined as an existential. -/
def twoPushes (s : DoublyLinkedList Nat) : St (DoublyLinkedList Nat) := do
  let s ← pushBack s 1
  pushBack s 2

example (s : DoublyLinkedList Nat) (vs : List Nat) :
    ⦃ isList s vs ⦄ twoPushes s ⦃⇓ s' => isList s' (vs ++ [1] ++ [2])⦄ := by
  unfold twoPushes
  apply triple_step_bind (pushBack s 1) _ (pushBack.isList_spec s vs 1)
  case hPre => sl_frame
  case hNext =>
    intro s1 _
    -- The terminal call goes through the ramified frame rule: a single goal,
    -- with no frame metavariable to guess.
    exact triple_step_mono (pushBack s1 2) _ (pushBack.isList_spec s1 (vs ++ [1]) 2)
      (by sl_frame)


end FrameInferenceTest


end Aeneas.SLPoC
