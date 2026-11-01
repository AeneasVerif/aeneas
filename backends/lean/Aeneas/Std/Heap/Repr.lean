module

public import Lean
public import Aeneas.Std.Scalar.Types

/-! Symbolic bytes distinguish numerical observation from provenance-preserving storage.
Descriptors specify admissible writes separately from readable representations. -/

@[expose] public section

namespace Aeneas.Std

universe u

abbrev Alignment := { n : Nat // ∃ k : Nat, n = 2 ^ k }
abbrev BasePtr := Usize
abbrev AddressMap := Nat → Option BasePtr

structure RawPtr (ty : Type u) : Type u where
  base : Nat
  byteOffset : Usize
deriving BEq, DecidableEq

instance : Inhabited (RawPtr ty) := ⟨⟨0, ⟨0⟩⟩⟩

abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

def RawPtr.cast (T' : Type) (p : RawPtr T) : RawPtr T' :=
  ⟨p.base, p.byteOffset⟩

inductive Byte where
  | uninit
  | data (value : U8)
  | pointer (value : RawPtr Unit) (lane : Nat)
deriving Inhabited, BEq, DecidableEq

/- The prototype uses eight little-endian lanes for thin pointers. -/
abbrev pointerWidth : Nat := 8

def RawPtr.address (addresses : AddressMap) (p : RawPtr T) : Option Usize := do
  let bptr ← addresses p.base
  let address := bptr.val + p.byteOffset.val
  if address < 2 ^ UScalarTy.numBits .Usize then
    some ⟨BitVec.ofNat _ address⟩
  else none

def Byte.numeric (addresses : AddressMap) : Byte → Option U8
  | .uninit => none
  | .data value => some value
  | .pointer p lane => do
      if lane < pointerWidth then
        let address ← p.address addresses
        some ⟨BitVec.ofNat _ (address.val / 2 ^ (8 * lane))⟩
      else none

inductive Cell where
  | shared (depth : Nat) (value : Byte)
  | borrowed
deriving Inhabited, BEq, DecidableEq

@[simp] def Cell.depth : Cell → Option Nat
  | .shared depth _ => some depth
  | .borrowed => none

def Cell.writable (cell : Cell) : Prop := cell.depth = some 0

def Cell.read : Cell → Option Byte
  | .shared _ .uninit => none
  | .shared _ value => some value
  | .borrowed => none

def Cell.write : Cell → Byte → Option Cell
  | .shared 0 _, value => some (.shared 0 value)
  | _, _ => none

def Cell.borrow : Cell → Option Cell
  | .shared 0 _ => some .borrowed
  | _ => none

def Cell.endBorrow : Cell → Byte → Option Cell
  | .borrowed, value => some (.shared 0 value)
  | _, _ => none

def Cell.share : Cell → Option Cell
  | .shared depth value => some (.shared (depth + 1) value)
  | .borrowed => none

def Cell.endShare : Cell → Option Cell
  | .shared (depth + 1) value => some (.shared depth value)
  | _ => none

def Cell.full (values : List Byte) : List Cell :=
  values.map (Cell.shared 0)

/-- Borrowed cells contribute no raw permission, but may carry implicit safe loans.
Uninitialized bytes are exact payloads, not compatibility wildcards. -/
def Cell.compatible : Cell → Cell → Bool
  | .borrowed, _ | _, .borrowed => true
  | .shared n x, .shared m y => n > 0 && m > 0 && decide (x = y)

/-- `decode` may observe pointer lanes numerically; `encodes` must not invent their
provenance. Both fields are calibrated to the represented Rust type. -/
structure Repr (ty : Type u) where
  size : Nat
  align : Alignment
  decode : AddressMap → Vector Byte size → Option ty
  encodes : ty → Vector Byte size → Prop
  pointers : ty → List (RawPtr Unit)
  aligned : align.val ∣ size
  complete : ∀ value, ∃ bytes, encodes value bytes
  encode_decode : ∀ addresses value bytes,
    encodes value bytes → decode addresses bytes = some value
  encodes_support : ∀ value bytes (i : Fin size), encodes value bytes →
    match bytes[i.val] with
    | .pointer p _ => p ∈ pointers value
    | _ => True

namespace Repr

variable {ty : Type u} {r : Nat}

def encodesList (repr : Repr ty) : List ty → List (Vector Byte repr.size) → Prop
  | [], [] => True
  | value :: values, bytes :: data => repr.encodes value bytes ∧ repr.encodesList values data
  | _, _ => False

def select (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) : Vector Cell repr.size :=
  (bytes.extract i (i + repr.size)).cast
    (by rw [Nat.min_eq_left hi]; simp)

def update (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r)
    (replacement : Vector Cell repr.size) : Vector Cell r :=
  ((bytes.extract 0 i) ++ replacement ++ bytes.extract (i + repr.size)).cast (by
    have hstart : i ≤ r := by grind
    simp only [Nat.min_eq_left hstart, Nat.sub_zero, Nat.min_self]
    grind)

def readBytes (n : Nat) (bytes : Vector Cell n) : Option (Vector Byte n) :=
  bytes.mapM Cell.read

def writeBytes (n : Nat) (bytes : Vector Cell n) (data : Vector Byte n) :
    Option (Vector Cell n) :=
  (bytes.zip data).mapM fun (cell, byte) => Cell.write cell byte

def read (repr : Repr ty) (addresses : AddressMap)
    (bytes : Vector Cell r) (i : Nat) : Option ty :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    (readBytes repr.size (repr.select bytes i h.2)).bind (repr.decode addresses)
  else none

def create (repr : Repr ty) (data : List (Vector Byte repr.size)) (depth : Nat) :
    List Cell :=
  data.flatMap fun bytes => bytes.toList.map (Cell.shared depth)

def write (repr : Repr ty) (bytes : Vector Cell r) (i : Nat)
    (_value : ty) (data : Vector Byte repr.size)
    (_encoded : repr.encodes _value data) : Option (Vector Cell r) :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    (writeBytes repr.size (repr.select bytes i h.2) data).map (repr.update bytes i h.2)
  else none

def borrow (repr : Repr ty) (bytes : Vector Cell r) (i : Nat) :
    Option (Vector Cell r) :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    ((repr.select bytes i h.2).mapM Cell.borrow).map (repr.update bytes i h.2)
  else none

/-- Authorized only by the matching safe backward continuation. -/
def endBorrow (repr : Repr ty) (bytes : Vector Cell r) (i : Nat)
    (data : Vector Byte repr.size) : Option (Vector Cell r) :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    (((repr.select bytes i h.2).zip data).mapM fun (cell, byte) =>
      Cell.endBorrow cell byte).map (repr.update bytes i h.2)
  else none

def share (repr : Repr ty) (bytes : Vector Cell r) (i : Nat) :
    Option (Vector Cell r) :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    ((repr.select bytes i h.2).mapM Cell.share).map (repr.update bytes i h.2)
  else none

def endShare (repr : Repr ty) (bytes : Vector Cell r) (i : Nat) :
    Option (Vector Cell r) :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    ((repr.select bytes i h.2).mapM Cell.endShare).map (repr.update bytes i h.2)
  else none

/-- Scalar writes use data bytes even when scalar reads observed a pointer lane. -/
def u8 : Repr U8 where
  size := 1
  align := ⟨1, ⟨0, rfl⟩⟩
  decode := fun addresses bytes => bytes[0].numeric addresses
  encodes := fun value bytes => bytes = #v[Byte.data value]
  pointers := fun _ => []
  aligned := by decide
  complete := fun value => ⟨#v[Byte.data value], rfl⟩
  encode_decode := by
    intro addresses value bytes h
    subst bytes
    rfl
  encodes_support := by
    intro value bytes i h
    subst bytes
    simp

def pointerEncoding (p : RawPtr T) : Vector Byte pointerWidth :=
  Vector.ofFn fun i => .pointer (p.cast Unit) i.val

def decodePointer (bytes : Vector Byte pointerWidth) : Option (RawPtr T) :=
  match bytes[0] with
  | .pointer p 0 =>
      if bytes = pointerEncoding p then some (p.cast T) else none
  | _ => none

/-- Thin-pointer metadata is recovered from coherent lanes, never from integer bytes. -/
def pointer (T : Type) : Repr (RawPtr T) where
  size := pointerWidth
  align := ⟨8, ⟨3, rfl⟩⟩
  decode := fun _ bytes => decodePointer bytes
  encodes := fun value bytes => bytes = pointerEncoding value
  pointers := fun value => [value.cast Unit]
  aligned := by decide
  complete := fun value => ⟨pointerEncoding value, rfl⟩
  encode_decode := by
    intro addresses value bytes h
    subst bytes
    simp [decodePointer, pointerEncoding, RawPtr.cast]
  encodes_support := by
    intro value bytes i h
    subst bytes
    simp [pointerEncoding]

end Repr
end Aeneas.Std
