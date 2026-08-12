import Aeneas.SLPoC.Step

/-!
# The `vstd` layer

Verus programs import `vstd`, which supplies sequences, maps, and the
manipulation of `PointsTo` permissions.  None of that appears in a Verus
example, so a line-count comparison with a Lean development is only fair if the
Lean side keeps the same material separate.  This module is that layer: it is
generic in the pointee type `α` and the payload type `β`, and it knows nothing
about any particular data structure.

The pattern it supports is Verus' "ghost sequence of pointers plus a `PointsTo`
map keyed by them": a `List (Ptr α × β)` records the pointers in order together
with the payload each of them carries, and `cellsFrom` owns the corresponding
permissions.

Every declaration names the `vstd` primitive (or the specification Verus derives
from it) that makes the corresponding step free on the Verus side.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace VerusStd

variable {α β : Type}

/-! ## Sequences of pointer/payload pairs

Verus keeps `ptrs : Seq<PPtr<T>>` and `points_to_map : Map<nat, PointsTo<T>>`
side by side.  A single `List (Ptr α × β)` records both, so the sequence
operations below play the role of the `vstd::seq` axioms. -/

/-- The payloads of the sequence, i.e. Verus' `points_to_map[i]@.value`
collected in index order.

*Verus/`vstd` counterpart:* `vstd::seq::Seq::new` together with its `len` and
`index` axioms. -/
def payloads (l : List (Ptr α × β)) : List β := l.map Prod.snd

/-- The first pointer of the sequence, i.e. Verus' `ptrs[0]`.

*Verus/`vstd` counterpart:* the `vstd::seq::Seq::index` axiom at `0`. -/
def firstPtr (l : List (Ptr α × β)) : Option (Ptr α) := l[0]?.map Prod.fst

/-- The last pointer of the sequence, i.e. Verus' `ptrs.last()`.

*Verus/`vstd` counterpart:* `vstd::seq::Seq::last`. -/
def lastPtr (l : List (Ptr α × β)) : Option (Ptr α) := l.getLast?.map Prod.fst

/- These are the only index arithmetic `grind` has to do, so it is worth
teaching it their equations once instead of citing them at every use. -/
attribute [grind] firstPtr lastPtr

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::empty()` and its `len` axiom. -/
@[simp] theorem payloads_nil : payloads ([] : List (Ptr α × β)) = [] := rfl

/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::index` axiom for
`seq![v].add(s)`. -/
@[simp] theorem payloads_cons (c : Ptr α × β) (l : List (Ptr α × β)) :
    payloads (c :: l) = c.2 :: payloads l := rfl

/-- *Verus/`vstd` counterpart:* `vstd::seq::Seq::add` and
`vstd::seq_lib::lemma_seq_add_len`. -/
@[simp] theorem payloads_append (l₁ l₂ : List (Ptr α × β)) :
    payloads (l₁ ++ l₂) = payloads l₁ ++ payloads l₂ := List.map_append ..

/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::len` axiom for `Seq::new`. -/
@[simp] theorem payloads_length (l : List (Ptr α × β)) :
    (payloads l).length = l.length := by
  simp [payloads]

/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::index` axiom for
`Seq::new`. -/
@[grind =] theorem payloads_getElem? (l : List (Ptr α × β)) (i : Nat) :
    (payloads l)[i]? = l[i]?.map Prod.snd := by
  simp [payloads]

/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::empty()` index axiom. -/
@[simp] theorem firstPtr_nil : firstPtr ([] : List (Ptr α × β)) = none := rfl

/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::index` axiom at `0`. -/
@[simp] theorem firstPtr_cons (c : Ptr α × β) (l : List (Ptr α × β)) :
    firstPtr (c :: l) = some c.1 := rfl


/-- *Verus/`vstd` counterpart:* the `vstd::seq::Seq::last` axiom for
`Seq::push`. -/
@[simp] theorem lastPtr_snoc (l : List (Ptr α × β)) (c : Ptr α × β) :
    lastPtr (l ++ [c]) = some c.1 := by
  simp [lastPtr]





/-- Every sequence is either empty or a `push`.

*Verus/`vstd` counterpart:* `vstd::seq_lib::lemma_seq_properties`. -/
theorem eq_nil_or_snoc (l : List γ) : l = [] ∨ ∃ l' c, l = l' ++ [c] := by
  rcases l.eq_nil_or_concat with h | ⟨l', c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', c, by simpa [List.concat_eq_append] using h⟩

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` last pointer
can only come from an empty sequence.

*Verus/`vstd` counterpart:* `assert_by_contradiction!` over the
`vstd::seq::Seq::len` axiom. -/
theorem lastPtr_eq_none_iff (l : List (Ptr α × β)) : lastPtr l = none ↔ l = [] := by
  constructor
  · intro h
    rcases l.eq_nil_or_concat with h' | ⟨l', c, h'⟩
    · exact h'
    · rw [h', List.concat_eq_append] at h
      simp at h
  · rintro rfl; rfl

/-- The counterpart of Verus' `assert_by_contradiction!`: a `none` first pointer
can only come from an empty sequence.

*Verus/`vstd` counterpart:* `assert_by_contradiction!` over the
`vstd::seq::Seq::len` axiom. -/
theorem firstPtr_eq_none_iff (l : List (Ptr α × β)) : firstPtr l = none ↔ l = [] := by
  cases l <;> simp [firstPtr]

/-- An in-range index really denotes a cell.

*Verus/`vstd` counterpart:* membership in `vstd::map::Map::dom`, which the
`well_formed` invariant relates to `ptrs.len()`. -/
theorem exists_cell (l : List (Ptr α × β)) (i : Nat) (hi : i < l.length) :
    ∃ r v, l[i]? = some (r, v) :=
  ⟨(l[i]'hi).1, (l[i]'hi).2, by rw [List.getElem?_eq_getElem hi]⟩

/-- *Verus/`vstd` counterpart:* Verus' built-in `Option::get_Some_0`. -/
@[simp] theorem get!_some {γ : Type} [Inhabited γ] (a : γ) : (some a).get! = a := rfl

/-! ## Permission maps

`cellsFrom f i cs` owns one permission per cell of `cs`, the cell at position
`i + k` holding `f (i + k)` applied to its payload.  This is Verus'
`points_to_map` restricted to a range of indices, and `f` is the pointwise
invariant its `well_formed` clause imposes on each entry. -/

/-- Ownership of the cells `cs`, whose indices start at `i`, each holding the
contents its index prescribes.

*Verus/`vstd` counterpart:* a `tracked` `vstd::map::Map<nat, PointsTo<T>>`
together with the pointwise invariant relating it to `ptrs`. -/
def cellsFrom (f : Nat → β → α) : Nat → List (Ptr α × β) → SLProp
  | _, [] => emp
  | i, (r, v) :: rest => iprop((r ↦ f i v) ∗ cellsFrom f (i + 1) rest)

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::empty()`. -/
@[simp] theorem cellsFrom_nil (f : Nat → β → α) (i : Nat) : cellsFrom f i [] = emp := rfl

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::insert` together with
`tracked_remove`. -/
@[simp] theorem cellsFrom_cons (f : Nat → β → α) (i : Nat) (r : Ptr α) (v : β)
    (rest : List (Ptr α × β)) :
    cellsFrom f i ((r, v) :: rest) =
      iprop((r ↦ f i v) ∗ cellsFrom f (i + 1) rest) := rfl

/-- *Verus/`vstd` counterpart:* `vstd::map::Map::singleton`. -/
@[simp] theorem cellsFrom_singleton (f : Nat → β → α) (i : Nat) (r : Ptr α) (v : β) :
    cellsFrom f i [(r, v)] = iprop(r ↦ f i v) := by
  simp [hstar_hempty_r_eq]

/-- `cellsFrom` only depends on the contents its index function prescribes, so
two invariants that agree on the relevant range own the same permissions.  This
lemma replaces the pointwise `well_formed_node` triggers of a Verus proof.

*Verus/`vstd` counterpart:* `vstd::map::Map::ext_equal`. -/
theorem cellsFrom_congr {f₁ f₂ : Nat → β → α} :
    ∀ (cs : List (Ptr α × β)) (i₁ i₂ : Nat),
      (∀ k, k < cs.length → f₁ (i₁ + k) = f₂ (i₂ + k)) →
      cellsFrom f₁ i₁ cs = cellsFrom f₂ i₂ cs := by
  intro cs
  induction cs with
  | nil => intros; rfl
  | cons c cs ih =>
    intro i₁ i₂ h
    obtain ⟨r, v⟩ := c
    have h0 := h 0 (by simp)
    have hrest : cellsFrom f₁ (i₁ + 1) cs = cellsFrom f₂ (i₂ + 1) cs := by
      refine ih (i₁ + 1) (i₂ + 1) fun k hk => ?_
      have h' := h (k + 1) (by simpa using hk)
      grind
    simp only [cellsFrom_cons, Nat.add_zero] at h0 ⊢
    grind

/-- Ownership of a concatenation splits into ownership of the two parts.

*Verus/`vstd` counterpart:* `vstd::map::Map::union_prefer_right` together with
`vstd::map_lib::lemma_disjoint_union`. -/
theorem cellsFrom_append (f : Nat → β → α) :
    ∀ (xs ys : List (Ptr α × β)) (i : Nat),
      cellsFrom f i (xs ++ ys) =
        iprop(cellsFrom f i xs ∗ cellsFrom f (i + xs.length) ys) := by
  intro xs
  induction xs with
  | nil => intro ys i; simp [hstar_hempty_l_eq]
  | cons c xs ih =>
    intro ys i
    obtain ⟨r, v⟩ := c
    have e : i + 1 + xs.length = i + (xs.length + 1) := by omega
    simp only [List.cons_append, cellsFrom_cons, ih, List.length_cons, e,
      hstar_assoc_eq]

/-- Split the permission of the cell of index `i` out of a full permission map.

*Verus/`vstd` counterpart:* `vstd::map::Map::tracked_borrow` at index `i`. -/
theorem cellsFrom_split (f : Nat → β → α) (l : List (Ptr α × β)) (i : Nat)
    (r : Ptr α) (v : β) (h : l[i]? = some (r, v)) :
    cellsFrom f 0 l =
      iprop(cellsFrom f 0 (l.take i) ∗
        ((r ↦ f i v) ∗ cellsFrom f (i + 1) (l.drop (i + 1)))) := by
  have hdrop : l.drop i = (r, v) :: l.drop (i + 1) := by
    grind [List.drop_eq_getElem_cons]
  have hl : l = l.take i ++ ((r, v) :: l.drop (i + 1)) := by
    rw [← hdrop, List.take_append_drop]
  rw [show cellsFrom f 0 l = cellsFrom f 0 (l.take i ++ ((r, v) :: l.drop (i + 1)))
      from by rw [← hl],
    cellsFrom_append, Nat.zero_add, cellsFrom_cons]
  grind

/-- Reading through a pointer of the map yields exactly the contents the
invariant prescribes, and returns the permission untouched.

*Verus/`vstd` counterpart:* `vstd::ptr::PPtr::borrow` under a `tracked` borrow
of the permission map. -/
theorem cellsFrom_read (f : Nat → β → α) (l : List (Ptr α × β)) (i : Nat)
    (r : Ptr α) (v : β) (h : l[i]? = some (r, v)) :
    ⦃ cellsFrom f 0 l ⦄ read r ⦃⇓ node => ⌜node = f i v⌝ ∗ cellsFrom f 0 l⦄ := by
  rw [cellsFrom_split f l i r v h]
  sl_step*

end VerusStd

end Aeneas.SLPoC
