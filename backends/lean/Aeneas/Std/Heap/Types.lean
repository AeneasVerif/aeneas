module

public import Lean
public import Aeneas.Std.Scalar.Types

@[expose] public section

namespace Aeneas.Std

universe u v

def update {α : Type u} {β : Type v} [DecidableEq α]
    (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k


abbrev Alignment := { n : Nat // ∃ k : Nat, n = 2 ^ k }

/-- A fixed-size byte representation of a type. -/
structure Repr (ty : Type u) where
  size : Nat
  align : Alignment
  decode : Vector U8 size -> Option ty
  aligned: align.val ∣ size
  complete: ∀ v : ty, ∃ bytes : Vector U8 size, decode bytes = v

abbrev BasePtr := Usize

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

structure RawPtr (ty : Type u) : Type u where
  base : BasePtr
  index : Usize

instance : Inhabited (RawPtr ty) := ⟨⟨⟨0⟩, ⟨0⟩⟩⟩

/-- Pointer constness is erased; cell permissions authorize access. -/
abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

structure Block where
  repr : List (Cell U8)
  alignment : Alignment
  owned : Bool

structure Heap where
  allocations : BasePtr → Option Block
  next : BasePtr

end Aeneas.Std
