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
structure RawPtr (ty : Type u) : Type u where
  provenance : Nat
  address : Usize
deriving BEq, DecidableEq

instance : Inhabited (RawPtr ty) := ⟨⟨0, ⟨0⟩⟩⟩

abbrev MutRawPtr (ty : Type u) := RawPtr ty
abbrev ConstRawPtr (ty : Type u) := RawPtr ty

def RawPtr.cast (T' : Type) (p : RawPtr T) : RawPtr T' :=
  ⟨p.provenance, p.address⟩

def RawPtr.offsetFrom (p : RawPtr T) (bptr : BasePtr) : Nat :=
  p.address.val - bptr.val

inductive Byte where
  | uninit
  | data (value : U8)
  | pointer (value : RawPtr Unit) (lane : Nat)
deriving Inhabited, BEq, DecidableEq

/- The prototype uses eight little-endian lanes for thin pointers. -/
abbrev pointerWidth : Nat := 8

def Byte.numeric : Byte → Option U8
  | .uninit => none
  | .data value => some value
  | .pointer p lane => do
      if lane < pointerWidth then
        some ⟨BitVec.ofNat _ (p.address.val / 2 ^ (8 * lane))⟩
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

/-- `decode` decides which bytes must be initialized, and may ignore padding or
observe pointer lanes numerically. `encode` must not invent provenance.
Both fields are calibrated to the represented Rust type. -/
structure Repr (ty : Type u) where
  size : Nat
  align : Alignment
  decode : Vector Byte size → Option ty
  encode : ty → Vector Byte size → Prop
  aligned : align.val ∣ size
  /- Every value can be encoded in size bytes. -/
  encode_complete : ∀ value, ∃ bytes, encode value bytes
  /- Every encoding of a value decodes correctly -/
  encode_decode : ∀ value bytes,
    encode value bytes → decode bytes = some value
  /- Decoding does not depend on uninitialized bytes. -/
  decode_mono : ∀ bytes bytes' value, decode bytes = some value →
    (∀ i : Fin size, bytes[i.val] ≠ .uninit → bytes'[i.val] = bytes[i.val]) →
    decode bytes' = some value
  /- Generic encodings must contain valid lanes, including in ignored padding.
     The explicit pointer descriptor alone cannot constrain aggregate descriptors. -/
  encode_valid : ∀ value bytes (i : Fin size), encode value bytes →
    match bytes[i.val] with
    | .pointer _ lane => lane < pointerWidth
    | _ => True

namespace Repr

variable {ty : Type u} {r : Nat}

/-- Pointer payloads are derived from admissible representations, not stored
as a second description of the value. This does not grant pointee access. -/
def Carries (repr : Repr ty) (value : ty) (p : RawPtr Unit) : Prop :=
  ∃ bytes : Vector Byte repr.size, repr.encode value bytes ∧
    ∃ i : Fin repr.size, ∃ lane, bytes[i.val] = .pointer p lane

theorem decode_set_uninit (repr : Repr ty) (bytes : Vector Byte repr.size)
    (value : ty) (i : Fin repr.size) (replacement : Byte)
    (decoded : repr.decode bytes = some value) (uninit : bytes[i.val] = .uninit) :
    repr.decode (bytes.set i.val replacement i.isLt) = some value := by
  apply repr.decode_mono bytes _ value decoded
  intro j initialized
  have different : i.val ≠ j.val := by
    intro he
    have same : i = j := Fin.ext he
    subst j
    exact initialized uninit
  exact Vector.getElem_set_ne i.isLt j.isLt different

def encodeList (repr : Repr ty) : List ty → List (Vector Byte repr.size) → Prop
  | [], [] => True
  | value :: values, bytes :: data => repr.encode value bytes ∧ repr.encodeList values data
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

def read (repr : Repr ty) (bytes : Vector Cell r) (i : Nat) : Option ty :=
  if h : 0 < repr.size ∧ i + repr.size ≤ r then
    (readBytes repr.size (repr.select bytes i h.2)).bind repr.decode
  else none

def create (repr : Repr ty) (data : List (Vector Byte repr.size)) (depth : Nat) :
    List Cell :=
  data.flatMap fun bytes => bytes.toList.map (Cell.shared depth)

def write (repr : Repr ty) (bytes : Vector Cell r) (i : Nat)
    (_value : ty) (data : Vector Byte repr.size)
    (_encoded : repr.encode _value data) : Option (Vector Cell r) :=
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
  decode := fun bytes => bytes[0].numeric
  encode := fun value bytes => bytes = #v[Byte.data value]
  aligned := by decide
  encode_complete := fun value => ⟨#v[Byte.data value], rfl⟩
  encode_decode := by
    intro value bytes h
    subst bytes
    rfl
  decode_mono := by
    intro bytes bytes' value decoded agree
    have initialized : bytes[0] ≠ .uninit := by
      intro he
      simp [he, Byte.numeric] at decoded
    change bytes'[0].numeric = some value
    rw [agree ⟨0, by decide⟩ initialized]
    exact decoded
  encode_valid := by
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
  decode := decodePointer
  encode := fun value bytes => bytes = pointerEncoding value
  aligned := by decide
  encode_complete := fun value => ⟨pointerEncoding value, rfl⟩
  encode_decode := by
    intro value bytes h
    subst bytes
    simp [decodePointer, pointerEncoding, RawPtr.cast]
  decode_mono := by
    intro bytes bytes' value decoded agree
    have original := decoded
    unfold decodePointer at decoded
    split at decoded
    · split at decoded
      · rename_i he
        have same : bytes' = bytes := by
          apply Vector.ext
          intro i hi
          apply agree ⟨i, hi⟩
          simp [he, pointerEncoding]
        simpa only [same] using original
      · contradiction
    · contradiction
  encode_valid := by
    intro value bytes i h
    subst bytes
    simp [pointerEncoding, i.isLt]

/-- Pointer decoding succeeds exactly on its complete provenance-carrying
encoding: every lane is checked, including the leading lane zero. -/
theorem pointer_decode_iff (bytes : Vector Byte pointerWidth) (value : RawPtr T) :
    (pointer T).decode bytes = some value ↔ (pointer T).encode value bytes := by
  constructor
  · intro decoded
    change bytes = pointerEncoding value
    change decodePointer bytes = some value at decoded
    unfold decodePointer at decoded
    split at decoded
    · split at decoded
      · rename_i encoded
        have he := Option.some.inj decoded
        subst value
        simpa only [pointerEncoding, RawPtr.cast] using encoded
      · contradiction
    · contradiction
  · exact (pointer T).encode_decode value bytes

@[simp] theorem u8_noPointers (value : U8) (p : RawPtr Unit) :
    ¬ u8.Carries value p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = #v[Byte.data value] at encoded
  subst bytes
  have hi : i.val < 1 := i.isLt
  have hz : i.val = 0 := by grind
  simp only [hz] at hp
  change Byte.data value = Byte.pointer p lane at hp
  cases hp

@[simp] theorem pointer_carries (value : RawPtr T) (p : RawPtr Unit) :
    (pointer T).Carries value p ↔ p = value.cast Unit := by
  constructor
  · rintro ⟨bytes, encoded, i, lane, hp⟩
    change bytes = pointerEncoding value at encoded
    subst bytes
    have laneEq := Vector.getElem_ofFn
      (f := fun j : Fin pointerWidth => Byte.pointer (value.cast Unit) j.val)
      (show i.val < pointerWidth from i.isLt)
    exact (Byte.pointer.inj (laneEq.symm.trans hp)).1.symm
  · intro he
    subst p
    exact ⟨pointerEncoding value, rfl, (⟨0, by decide⟩ : Fin pointerWidth), 0, rfl⟩

end Repr
end Aeneas.Std
