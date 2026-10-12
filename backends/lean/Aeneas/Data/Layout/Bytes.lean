module
public import Aeneas.Data.Byte
@[expose] public section

namespace Aeneas

/-! ## Abstract Bytes and Definedness Relation (`le_defined`)
    Following MiniRust's `spec/lang/representation.md`. -/

inductive AbstractByte where
  | uninit
  | init (data : Byte)
deriving DecidableEq

namespace AbstractByte

@[simp]
def data : AbstractByte → Option Byte
  | .uninit => none
  | .init b => some b

/-- Returns whether `self` is less or as defined as `other` (`b1 <= b2`). -/
def le_defined (self other : AbstractByte) : Prop :=
  match self, other with
  -- `Uninit <= _`: initializing something makes it "more defined".
  | .uninit, _ => True
  -- Among initialized bytes (without provenance), data must be equal.
  | .init data1, .init data2 => data1 = data2
  -- Nothing else is related.
  | _, _ => False

end AbstractByte

abbrev Bytes (n : Nat) := Vector AbstractByte n

namespace Bytes

def uninit (n : Nat) : Bytes n := Vector.replicate n .uninit

/-- The order on `Bytes` is bytewise `le_defined`. -/
def le_defined {n : Nat} (self other : Bytes n) : Prop :=
  ∀ i : Fin n, (self[i]).le_defined (other[i])

def subslice_with_length {n : Nat} (bytes : Bytes n) (offset length : Nat) (h : offset + length ≤ n) : Bytes length :=
  Vector.ofFn λ (i : Fin length) ↦ bytes[offset + i.val]'(by omega)

def write_subslice_at_index {n m : Nat} (bytes : Bytes n) (offset : Nat) (subslice : Bytes m) : Bytes n :=
  Vector.ofFn λ (j : Fin n) ↦
    if h : offset ≤ j.val ∧ j.val < offset + m then subslice[j.val - offset]'(by omega) else bytes[j]

def toData {n : Nat} (bytes : Bytes n) : Option (Vector Byte n) :=
  if h : ∀ i : Fin n, (bytes[i]).data.isSome
  then some (Vector.ofFn λ i ↦ (bytes[i]).data.get (h i))
  else none

end Bytes

/-- On `Option`, `none <= _`, and `some v1 <= some v2` iff `v1 = v2`. -/
def Option.le_defined {α : Type u} (self other : Option α) : Prop :=
  match self, other with
  | none, _ => True
  | some l, some r => l = r
  | _, _ => False

end Aeneas
