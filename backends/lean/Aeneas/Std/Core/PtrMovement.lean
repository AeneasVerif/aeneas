module

public import Aeneas.Std.Core.Ptr

/-! Byte movement and root-aware allocation distance. These opt-in models have
no builtin registration. The core distinguishes numerical addresses from view IDs. -/

@[expose] public section

namespace Aeneas.Std

/-- Metadata-only stride for byte movement, not a pointee layout. -/
def Repr.byteStride : Repr Unit where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode := fun _ => some ()
  encode := fun _ bytes => bytes = #v[Byte.data ⟨0⟩]
  aligned := Nat.one_dvd _
  encode_complete := fun _ => ⟨#v[Byte.data ⟨0⟩], rfl⟩
  encode_decode := by intros; rfl
  decode_mono := by intros; assumption
  encode_valid := by
    intro value bytes i h
    subst bytes
    simp

def Heap.byteOffset (p : RawPtr T) (count : Int) (s : Heap) : Option (RawPtr T) :=
  (Heap.offset Repr.byteStride (RawPtr.cast Unit p) count s).map (RawPtr.cast T)

/-- Restricted to live views of a common root, including one-past.
Both byte distance and element distance must fit `isize`; ZSTs are rejected. -/
def Heap.offsetFrom (repr : Repr T) (p origin : RawPtr T) (s : Heap) : Option Isize := do
  let elements ← Heap.distance repr p origin s
  let a := p.address
  let b := origin.address
  let bytes := (a.val : Int) - b.val
  if IScalar.cMin .Isize ≤ bytes && bytes ≤ IScalar.cMax .Isize then
    if h : IScalar.cMin .Isize ≤ elements ∧ elements ≤ IScalar.cMax .Isize then
      some (IScalar.ofInt elements h)
    else none
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
