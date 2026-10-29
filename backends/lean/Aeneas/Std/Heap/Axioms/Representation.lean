module

public import Aeneas.Std.Heap.Types

@[expose] public section

namespace Aeneas.Std

universe u

theorem Repr.size_aligned (repr : Repr ty) : repr.align.val ∣ repr.size :=
  Nat.dvd_of_mod_eq_zero repr.aligned

/-- Same-type logical indices are disjoint only when their strides agree. -/
def CellsDisjoint {T U : Type u}
    (reprT : Repr T) (i : Nat) (reprU : Repr U) (j : Nat) : Prop :=
  (T = U ∧ reprT.size = reprU.size ∧ i ≠ j) ∨
  (T ≠ U ∧ (reprT.size = 0 ∨ reprU.size = 0)) ∨
  (0 < reprT.size ∧ 0 < reprU.size ∧
    ((i + 1) * reprT.size ≤ j * reprU.size ∨
      (j + 1) * reprU.size ≤ i * reprT.size))

namespace Block

abbrev bytes (block : Block) : List (Cell U8) := block.repr

/- The remaining declarations are the old operational interface, not a concrete
implementation of typed validity or zero-sized cells. In particular, existence
of a creation or update is not assumed. -/
axiom extent {ty : Type u} (repr : Repr ty) : Block → Nat
axiom view {ty : Type u} (repr : Repr ty) : Block → Nat → Cell ty → Prop
axiom setCell {ty : Type u} (repr : Repr ty) :
  Nat → Option (Cell ty) → Block → Block → Prop
axiom create {ty : Type u} (repr : Repr ty) : List (Cell ty) → Block → Prop

axiom extent_bytes : ∀ {ty} (repr : Repr ty) r, 0 < repr.size →
  extent repr r = r.repr.length / repr.size
axiom view_unique : ∀ {ty} (repr : Repr ty) r i a b,
  view repr r i a → view repr r i b → a = b
axiom view_bound : ∀ {ty} (repr : Repr ty) r i c,
  view repr r i c → i < extent repr r
axiom view_bytes : ∀ {ty} (repr : Repr ty) r i c, view repr r i c →
  ∀ b, i * repr.size ≤ b → b < (i + 1) * repr.size →
    ∃ byte, r.repr[b]? = some byte ∧ byte.depth = c.depth ∧
      (c.read ≠ none → byte.read ≠ none)
axiom create_extent : ∀ {ty} (repr : Repr ty) cs r,
  create repr cs r → extent repr r = cs.length
axiom create_bytes : ∀ {ty} (repr : Repr ty) cs r,
  create repr cs r → r.repr.length = cs.length * repr.size
axiom create_view : ∀ {ty} (repr : Repr ty) cs r, create repr cs r →
  ∀ i (hi : i < cs.length), view repr r i cs[i]
axiom set_none : ∀ {ty} (repr : Repr ty) i r r',
  setCell repr i none r r' ↔ r' = r
axiom set_view : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i (some c) r r' → view repr r' i c
axiom set_extent : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i c r r' →
  ∀ {U} (reprU : Repr U), extent reprU r' = extent reprU r
axiom set_bytes_length : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i c r r' → r'.repr.length = r.repr.length
axiom set_outside : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i c r r' →
  ∀ b, b < i * repr.size ∨ (i + 1) * repr.size ≤ b →
    r'.repr[b]? = r.repr[b]?
axiom set_frame : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i c r r' →
  ∀ {U} (reprU : Repr U) j, CellsDisjoint repr i reprU j →
    ∀ value, view reprU r' j value ↔ view reprU r j value
axiom set_borrow_type : ∀ {ty} (repr : Repr ty) i r r',
  setCell repr i (some .borrowed) r r' →
  ∀ {U} (reprU : Repr U) j, ty ≠ U → ¬ CellsDisjoint repr i reprU j →
    ∀ value, ¬ view reprU r' j value
axiom set_pointer : ∀ {ty} (repr : Repr ty) i c r r',
  setCell repr i (some c) r r' →
  ∀ {U} (reprU : Repr (RawPtr U)) j,
    ty ≠ RawPtr U → ¬ CellsDisjoint repr i reprU j →
    ∀ value, ¬ view reprU r' j value

theorem set_bound {ty : Type u} (repr : Repr ty) (i : Nat) (c : Cell ty)
    (r r' : Block) (h : setCell repr i (some c) r r') :
    i < extent repr r := by
  have hb := view_bound repr r' i c (set_view repr i c r r' h)
  rw [set_extent repr i (some c) r r' h repr] at hb
  exact hb

end Block

end Aeneas.Std
