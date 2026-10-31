module

public import Aeneas.Std.Core.Ptr

/-! Byte movement and restricted same-allocation distance. Allocation identifiers
are provenance tokens, never integer addresses. These opt-in models have no
builtin registration and do not provide general pointer comparison. -/

@[expose] public section

namespace Aeneas.Std

/-- Metadata-only stride for byte movement, not a pointee layout. -/
def Repr.byteStride : Repr Unit where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode := fun _ => some ()
  aligned := Nat.one_dvd _
  complete := fun value => by cases value; exact ⟨Vector.replicate _ ⟨0⟩, rfl⟩

def Heap.byteOffset (p : RawPtr T) (count : Int) (s : Heap) : Option (RawPtr T) :=
  (Heap.offset Repr.byteStride (RawPtr.cast Unit p) count s).map (RawPtr.cast T)

/-- Deliberately restricted to a live common allocation, including one-past.
Both byte distance and element distance must fit `isize`; ZSTs are rejected. -/
def Heap.offsetFrom (repr : Repr T) (p origin : RawPtr T) (s : Heap) : Option Isize :=
  if 0 < repr.size ∧ p.base = origin.base then
    match s.allocations p.base with
    | some block =>
      let bytes : Int := (p.byteOffset.val : Int) - origin.byteOffset.val
      let elements := bytes / repr.size
      if p.byteOffset.val ≤ block.repr.length ∧ origin.byteOffset.val ≤ block.repr.length ∧
          bytes % repr.size = 0 ∧ IScalar.cMin .Isize ≤ bytes ∧ bytes ≤ IScalar.cMax .Isize then
        if h : IScalar.cMin .Isize ≤ elements ∧ elements ≤ IScalar.cMax .Isize then
          some (IScalar.ofInt elements h)
        else none
      else none
    | none => none
  else none

def RawPtr.byte_offset (p : RawPtr T) (count : Isize) : Result (RawPtr T) :=
  Result.checkedModify (fun s result s' => Heap.byteOffset p count.val s = some result ∧ s' = s)

def RawPtr.byte_add (p : RawPtr T) (count : Usize) : Result (RawPtr T) :=
  if (count.val : Int) ≤ IScalar.cMax .Isize then
    Result.checkedModify (fun s result s' => Heap.byteOffset p count.val s = some result ∧ s' = s)
  else .fail .undef

def RawPtr.offset_from (repr : Repr T) (p origin : RawPtr T) : Result Isize :=
  Result.checkedModify (fun s result s' => Heap.offsetFrom repr p origin s = some result ∧ s' = s)

end Aeneas.Std
