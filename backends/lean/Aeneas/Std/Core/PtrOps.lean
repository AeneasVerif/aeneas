module

public import Aeneas.Std.Core.Ptr

/-! Opt-in pointer operations for the isolated byte model. No compiler mappings
are registered here; descriptors remain explicit until extraction supports them. -/

@[expose] public section

namespace Aeneas.Std

/-- The decoder and byte size are unchanged; only the access alignment is relaxed. -/
def Repr.unaligned (repr : Repr T) : Repr T :=
  { repr with align := ⟨1, 0, rfl⟩, aligned := Nat.one_dvd _ }

def RawPtr.replace (repr : Repr T) (p : RawPtr T) (value : T) : Result T := do
  let _ : Pointee T := ⟨repr⟩
  let old ← p.read
  MutRawPtr.write p value
  pure old

/-- Only disjoint or identical footprints are modeled. Rust's partially
overlapping case is deliberately rejected rather than approximated. -/
def RawPtr.swap (repr : Repr T) (p q : RawPtr T) : Result Unit :=
  Result.checkedModify fun s (_ : Unit) s' => Heap.swapBytes repr p q s = some s'

def RawPtr.read_unaligned (repr : Repr T) (p : RawPtr T) : Result T :=
  @RawPtr.read _ ⟨repr.unaligned⟩ p

def RawPtr.write_unaligned (repr : Repr T) (p : RawPtr T) (value : T) : Result Unit :=
  @MutRawPtr.write _ ⟨repr.unaligned⟩ p value

end Aeneas.Std
