module

public import Lean
public import Aeneas.Std.Scalar.Types

/-! Byte-level operations take a representation explicitly (as we expect
Charon/Aeneas to pass that information from Rust). They do not track
pointer validity or the authority to restore a borrow. Empty footprints carry
no byte permissions; observing a zero-sized cell returns `none` (aka UB). -/

@[expose] public section

namespace Aeneas.Std

universe u

abbrev Alignment := { n : Nat // ∃ k : Nat, n = 2 ^ k }

/-- A fixed-size byte representation of a type. -/
structure Repr (ty : Type u) where
  size : Nat
  align : Alignment
  decode : Vector U8 size -> Option ty
  aligned : align.val ∣ size
  complete : ∀ v : ty, ∃ bytes : Vector U8 size, decode bytes = v

inductive Cell (ty : Type u) where
  | shared (depth : Nat) (value : Option ty)
  | borrowed

@[simp] def Cell.depth : Cell ty → Option Nat
  | .shared depth _ => some depth
  | .borrowed => none

def Cell.writable (c : Cell ty) : Prop := c.depth = some 0

def Cell.read : Cell ty → Option ty
  | .shared _ value => value
  | _ => none

def Cell.write (cell : Cell ty) (value : ty) : Option (Cell ty) :=
  match cell with
  | .shared 0 _ => some (.shared 0 (some value))
  | _ => none

def Cell.borrow : Cell ty → Option (Cell ty)
  | .shared 0 _ => some .borrowed
  | _ => none

def Cell.endBorrow (cell : Cell ty) (value : ty) : Option (Cell ty) :=
  match cell with
  | .borrowed => some (.shared 0 (some value))
  | _ => none

def Cell.share : Cell ty → Option (Cell ty)
  | .shared depth value => some (.shared (depth + 1) value)
  | .borrowed => none

def Cell.endShare : Cell ty → Option (Cell ty)
  | .shared (depth + 1) value => some (.shared depth value)
  | _ => none

def Cell.full (values : List ty) : List (Cell ty) :=
  values.map (Cell.shared 0 ∘ some)

namespace Repr

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

/-- Expand encoded cells into bytes, preserving their permissions. -/
def create (repr : Repr ty) {n : Nat}
    (cells : Vector (Cell (Vector U8 repr.size)) n) :
    Vector (Cell U8) (n * repr.size) :=
  cells.flatMap fun
    | .shared depth (some data) => data.map (Cell.shared depth ∘ some)
    | .shared depth none => Vector.replicate repr.size (.shared depth none)
    | .borrowed => Vector.replicate repr.size .borrowed

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

end Repr
end Aeneas.Std
