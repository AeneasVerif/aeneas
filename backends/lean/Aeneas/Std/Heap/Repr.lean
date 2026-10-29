module

public import Aeneas.Std.Heap.Types

/-! Byte-level operations take a representation explicitly. They do not track
pointer validity or the authority to restore a borrow. Empty footprints carry
no byte permissions; observing a zero-sized cell therefore returns `none`. -/

@[expose] public section

namespace Aeneas.Std.Repr

universe u

variable {ty : Type u} {r : Nat}

/- returns the cells representing the ith typed entry -/
def select
  (repr : Repr ty)
  (bytes : Vector (Cell U8) r)
  (i : Nat) (hi : (i + 1) * repr.size ≤ r) : Vector (Cell U8) repr.size :=
  (bytes.extract (i * repr.size) ((i + 1) * repr.size)).cast
    (by rw [Nat.min_eq_left hi]; simp [Nat.add_mul])

/-- Overwrite the selected cells, preserving all surrounding cells. -/
def update
  (repr : Repr ty)
  (bytes : Vector (Cell U8) r)
  (i : Nat) (hi : (i + 1) * repr.size ≤ r)
  (replacement : Vector (Cell U8) repr.size) : Vector (Cell U8) r :=
  ((bytes.extract 0 (i * repr.size)) ++ replacement ++
    bytes.extract ((i + 1) * repr.size)).cast (by
      have hstart : i * repr.size ≤ r := by grind [Nat.add_mul]
      simp only [Nat.min_eq_left hstart, Nat.sub_zero, Nat.min_self]
      grind [Nat.add_mul])

/-- Collect initialized, readable bytes, preserving their length. -/
def readBytes (n : Nat) (bytes : Vector (Cell U8) n) : Option (Vector U8 n) :=
  bytes.mapM Cell.read

def writeBytes (n : Nat) (bytes : Vector (Cell U8) n) (data : Vector U8 n) :
    Option (Vector (Cell U8) n) :=
  (bytes.zip data).mapM fun (cell, byte) => Cell.write cell byte

def read (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat) : Option ty :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    (readBytes repr.size (repr.select bytes i h.2)).bind repr.decode
  else none

inductive create (repr : Repr ty) : List (Cell ty) → List (Cell U8) → Prop where
  | nil : create repr [] []
  | uninit (depth : Nat) {cs bytes} (rest : create repr cs bytes) :
      create repr (.shared depth none :: cs)
        (List.replicate repr.size (.shared depth none) ++ bytes)
  | initialized (depth : Nat) (value : ty) (data : Vector U8 repr.size)
      (decoded : repr.decode data = some value) {cs bytes} (rest : create repr cs bytes) :
      create repr (.shared depth (some value) :: cs)
        (data.toList.map (Cell.shared depth ∘ some) ++ bytes)
  | borrowed {cs bytes} (rest : create repr cs bytes) :
      create repr (.borrowed :: cs) (List.replicate repr.size .borrowed ++ bytes)

/-- Write a value using the supplied byte representation. -/
def write (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat)
    (value : ty) (data : Vector U8 repr.size)
    (_decoded : repr.decode data = some value) : Option (Vector (Cell U8) r) :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    match writeBytes repr.size (repr.select bytes i h.2) data with
    | some cells => some (repr.update bytes i h.2 cells)
    | none => none
  else none

def borrow (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat) :
    Option (Vector (Cell U8) r) :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    match (repr.select bytes i h.2).mapM Cell.borrow with
    | some cells => some (repr.update bytes i h.2 cells)
    | none => none
  else none

/-- The caller must possess the matching borrow authority. -/
def endBorrow (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat)
    (value : ty) (data : Vector U8 repr.size)
    (_decoded : repr.decode data = some value) : Option (Vector (Cell U8) r) :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    match ((repr.select bytes i h.2).zip data).mapM (fun (cell, byte) =>
        Cell.endBorrow cell byte) with
    | some cells => some (repr.update bytes i h.2 cells)
    | none => none
  else none

def share (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat) :
    Option (Vector (Cell U8) r) :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    match (repr.select bytes i h.2).mapM Cell.share with
    | some cells => some (repr.update bytes i h.2 cells)
    | none => none
  else none

def endShare (repr : Repr ty) (bytes : Vector (Cell U8) r) (i : Nat) :
    Option (Vector (Cell U8) r) :=
  if h : 0 < repr.size ∧ (i + 1) * repr.size ≤ r then
    match (repr.select bytes i h.2).mapM Cell.endShare with
    | some cells => some (repr.update bytes i h.2 cells)
    | none => none
  else none

end Aeneas.Std.Repr
