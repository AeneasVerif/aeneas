module
public import Aeneas.Std.Heap
public import Aeneas.Std.Primitives
public meta import Aeneas.Extract.Extract
@[expose] public section

/-!
# `MaybeUninit`

A value of type `MaybeUninit T` is either uninitialized or a value of type `T`.
In memory, an uninitialized value is a run of uninitialized cells, and an
initialized one the bytes encoding it (see [`Heap`](Heap.lean)).
-/

namespace Aeneas.Std

open Result

@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
inductive MaybeUninit (T : Type) where
  | uninit
  | init (value : T)
  deriving Inhabited

namespace MaybeUninit

variable {T : Type}

/-- The cells of a value of type `MaybeUninit T` in memory. -/
def cells [ByteRepr T] : MaybeUninit T → List Cell
  | uninit => List.replicate (ByteRepr.size T) none
  | init value => (ByteRepr.encode value).map some

@[simp] theorem length_cells [ByteRepr T] (m : MaybeUninit T) :
    m.cells.length = ByteRepr.size T := by
  cases m <;> simp [cells, ByteRepr.length_encode]

@[simp] theorem cells_uninit [ByteRepr T] :
    (uninit : MaybeUninit T).cells = List.replicate (ByteRepr.size T) none := rfl

@[simp] theorem cells_init [ByteRepr T] (value : T) :
    (init value).cells = (ByteRepr.encode value).map some := rfl

/-- Read a value of type `MaybeUninit T` back from its cells: it is initialized
if all the cells are, and if they encode a value of type `T`.  In particular,
a value which is only partially initialized is read back as uninitialized,
which is consistent with the fact that it can't be used as a value of type
`T` anyway. -/
def ofCells [ByteRepr T] (cs : List Cell) : MaybeUninit T :=
  match cs.mapM id with
  | some bs =>
    match ByteRepr.decode bs with
    | some value => init value
    | none => uninit
  | none => uninit

private theorem mapM_id_map_some (bs : List Byte) :
    (bs.map some).mapM id = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [List.mapM_cons, ih]

private theorem mapM_id_replicate_none (n : Nat) (hn : 0 < n) :
    (List.replicate n (none : Option Byte)).mapM id = none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [List.replicate_succ, List.mapM_cons]

@[simp] theorem ofCells_cells [ByteRepr T] (m : MaybeUninit T)
    (hSize : 0 < ByteRepr.size T) : ofCells m.cells = m := by
  cases m with
  | uninit => simp [ofCells, cells, mapM_id_replicate_none _ hSize]
  | init value =>
    have h := mapM_id_map_some (ByteRepr.encode value)
    simp only [ofCells, cells, h, ByteRepr.decode_encode]

/-- Read back consecutive values of type `MaybeUninit T` from their cells. -/
def ofCellsRange [ByteRepr T] (cs : List Cell) : Nat → List (MaybeUninit T)
  | 0 => []
  | n + 1 => ofCells (cs.take (ByteRepr.size T)) :: ofCellsRange (cs.drop (ByteRepr.size T)) n

@[simp] theorem ofCellsRange_flatMap_cells [ByteRepr T] (ms : List (MaybeUninit T))
    (hSize : 0 < ByteRepr.size T) :
    ofCellsRange (ms.flatMap cells) ms.length = ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    have hLen := length_cells m
    simp only [List.flatMap_cons, List.length_cons, ofCellsRange]
    rw [List.take_left' hLen, List.drop_left' hLen, ofCells_cells m hSize, ih]

theorem length_flatMap_cells [ByteRepr T] (ms : List (MaybeUninit T)) :
    (ms.flatMap cells).length = ms.length * ByteRepr.size T := by
  induction ms with
  | nil => simp
  | cons m rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

@[simp] theorem flatMap_cells_map_init [ByteRepr T] (values : List T) :
    (values.map init).flatMap cells = (values.flatMap ByteRepr.encode).map some := by
  induction values with
  | nil => rfl
  | cons v rest ih => simp [ih]

end MaybeUninit

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::uninit"]
def core.mem.maybe_uninit.MaybeUninit.uninit (T : Type) : Result (MaybeUninit T) :=
  ok .uninit

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::new"]
def core.mem.maybe_uninit.MaybeUninit.new {T : Type} (value : T) : Result (MaybeUninit T) :=
  ok (.init value)

/-- Using an uninitialized value is undefined behavior. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::assume_init"]
def core.mem.maybe_uninit.MaybeUninit.assume_init {T : Type} : MaybeUninit T → Result T
  | .init value => ok value
  | .uninit => fail .undef

end Aeneas.Std
