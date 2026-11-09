/- The byte representations of the values stored behind raw pointers. -/
module
public import Aeneas.Std.Heap
public import Aeneas.Std.Scalar.Core
public import Aeneas.Data.BitVec
@[expose] public section

namespace Aeneas.Std

/-- The byte representation (see `Repr`) of the values of type `T`, used by the models of the
raw-pointer functions to read and write values of type `T` in the heap.

The extracted code doesn't pass it explicitly: it is found by instance resolution. The stateful
functions receive the instances of their type parameters, and Aeneas generates the instances of the
structures (see `Repr.prod` and `Repr.iso`). -/
class Pointee (T : Type) where
  repr : Repr T

namespace Repr

/-! ### Representations by bytes

Integers and booleans are stored as data bytes: reading them observes the numerical value of the
bytes (also of pointer bytes). -/

theorem mapM_numeric_map_data (xs : List U8) : (xs.map Byte.data).mapM Byte.numeric = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih, Byte.numeric]

theorem ne_uninit_of_mapM_numeric {bytes : List Byte} {xs : List U8}
    (h : bytes.mapM Byte.numeric = some xs) : ∀ b ∈ bytes, b ≠ .uninit := by
  induction bytes generalizing xs with
  | nil => simp
  | cons b bytes ih =>
    simp only [List.mapM_cons] at h
    intro b' hb' he
    cases hb : b.numeric <;> simp [hb] at h
    rcases List.mem_cons.mp hb' with rfl | hb'
    · simp [he, Byte.numeric] at hb
    · cases hr : bytes.mapM Byte.numeric <;> simp [hr] at h
      exact ih hr b' hb' he

/-- The representation of a type by `size` data bytes: `encode` gives the bytes of a value, and
`decode` the value whose bytes are given (if any). -/
def ofBytes (T : Type) (size : Nat) (align : Alignment) (aligned : align.val ∣ size)
    (encode : T → List U8) (decode : List U8 → Option T)
    (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value) : Repr T where
  size := size
  align := align
  decode bytes := bytes.toList.mapM Byte.numeric >>= decode
  encode value bytes := bytes.toList = (encode value).map Byte.data
  aligned := aligned
  encode_complete value :=
    ⟨⟨((encode value).map Byte.data).toArray, by simp [length_encode]⟩, by simp⟩
  encode_decode := by
    intro value bytes h
    show bytes.toList.mapM Byte.numeric >>= decode = some value
    rw [h, mapM_numeric_map_data]
    exact decode_encode value
  decode_mono := by
    intro bytes bytes' value decoded agree
    cases hm : bytes.toList.mapM Byte.numeric with
    | none => simp [hm] at decoded
    | some xs =>
      have hne := ne_uninit_of_mapM_numeric hm
      have same : bytes' = bytes := by
        apply Vector.ext
        intro i hi
        apply agree ⟨i, hi⟩
        apply hne
        simp
      rw [same]
      exact decoded
  encode_valid := by
    intro value bytes i h
    have hi : bytes[i.val] = ((encode value).map Byte.data)[i.val]'(by simp [length_encode]) := by
      simp only [← h, Vector.getElem_toList]
    rw [hi]
    simp

/-- Little-endian bytes of `numBits` bits. -/
def decodeLE (numBits : Nat) (bytes : List U8) : Option (BitVec numBits) :=
  if h : 8 * bytes.length = numBits then
    some ((BitVec.fromLEBytes (bytes.map U8.bv)).cast (by simpa using h))
  else none

theorem decodeLE_toLEBytes {n : Nat} (hn : n % 8 = 0) (b : BitVec n) :
    decodeLE n (b.toLEBytes.map UScalar.mk) = some b := by
  have hLen : 8 * (b.toLEBytes.map (UScalar.mk (ty := .U8))).length = n := by
    rw [List.length_map, BitVec.toLEBytes_length]; omega
  unfold decodeLE
  rw [dite_eq_left hLen]
  have hMap : (b.toLEBytes.map (UScalar.mk (ty := .U8))).map U8.bv = b.toLEBytes := by
    rw [List.map_map]; exact List.map_id _
  have key : ∀ l, l = b.toLEBytes → (BitVec.fromLEBytes l).toNat = b.toNat := by
    rintro l rfl
    rw [BitVec.fromLEBytes_toLEBytes hn, BitVec.toNat_cast]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast]
  exact key _ hMap

theorem _root_.Aeneas.Std.UScalarTy.numBits_mod_eight (ty : UScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [UScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_mod_eight (ty : IScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [IScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem usize_bytes_pow : ∃ k, System.Platform.numBits / 8 = 2 ^ k := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The integers are aligned on their size, which is a power of two. -/
def scalarAlign (numBits : Nat) (h : ∃ k, numBits / 8 = 2 ^ k) : Alignment := ⟨numBits / 8, h⟩

theorem _root_.Aeneas.Std.UScalarTy.bytes_pow (ty : UScalarTy) : ∃ k, ty.numBits / 8 = 2 ^ k := by
  cases ty
  · exact usize_bytes_pow
  all_goals simp only [UScalarTy.numBits]
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem _root_.Aeneas.Std.IScalarTy.bytes_pow (ty : IScalarTy) : ∃ k, ty.numBits / 8 = 2 ^ k := by
  cases ty
  · exact usize_bytes_pow
  all_goals simp only [IScalarTy.numBits]
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

/-- Little-endian representation of an unsigned integer. -/
def uscalar (ty : UScalarTy) : Repr (UScalar ty) :=
  ofBytes (UScalar ty) (ty.numBits / 8) (scalarAlign ty.numBits ty.bytes_pow) (Nat.dvd_refl _)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (decodeLE ty.numBits bytes).map UScalar.mk)
    (fun x => by
      rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])

/-- Little-endian (two's complement) representation of a signed integer. -/
def iscalar (ty : IScalarTy) : Repr (IScalar ty) :=
  ofBytes (IScalar ty) (ty.numBits / 8) (scalarAlign ty.numBits ty.bytes_pow) (Nat.dvd_refl _)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (decodeLE ty.numBits bytes).map IScalar.mk)
    (fun x => by
      rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])

/-- A boolean is the byte `0` or `1`. -/
def bool : Repr Bool :=
  ofBytes Bool 1 ⟨1, ⟨0, rfl⟩⟩ (Nat.dvd_refl 1)
    (fun b => [if b then (⟨1#8⟩ : U8) else (⟨0#8⟩ : U8)])
    (fun bytes => match bytes with
      | [x] => if x = (⟨0#8⟩ : U8) then some false else if x = (⟨1#8⟩ : U8) then some true else none
      | _ => none)
    (fun _ => rfl) (fun b => by cases b <;> decide)

/-! ### Representations of the structures

A value of a structure is stored as the values of its fields, one after the other, with padding to
align them (as nested pairs: see `prod`). Rust doesn't specify the layout of the structures (unless
they are `#[repr(C)]`), so any layout is a correct model of the code which doesn't depend on it. -/

/-- The zero-sized representation of the types with a single value. -/
def unit (T : Type) (value : T) (unique : ∀ x : T, x = value) : Repr T where
  size := 0
  align := ⟨1, ⟨0, rfl⟩⟩
  decode _ := some value
  encode _ _ := True
  aligned := Nat.dvd_refl _ |>.trans (by simp)
  encode_complete _ := ⟨#v[], trivial⟩
  encode_decode := by
    intro x bytes _
    rw [unique x]
  decode_mono := by
    intro _ _ x h _
    exact h
  encode_valid := by
    intro _ _ i
    exact absurd i.isLt (Nat.not_lt_zero _)

/-- The representation of a type which is in bijection with the represented type. -/
def iso {A B : Type} (r : Repr A) (f : B → A) (g : A → B) (gf : ∀ b, g (f b) = b) : Repr B where
  size := r.size
  align := r.align
  decode bytes := (r.decode bytes).map g
  encode b bytes := r.encode (f b) bytes
  aligned := r.aligned
  encode_complete b := r.encode_complete (f b)
  encode_decode := by
    intro b bytes h
    simp [r.encode_decode _ _ h, gf]
  decode_mono := by
    intro bytes bytes' b decoded agree
    cases hd : r.decode bytes with
    | none => simp [hd] at decoded
    | some a => simp [r.decode_mono bytes bytes' a hd agree, ← decoded, hd]
  encode_valid := by
    intro b bytes i h
    exact r.encode_valid _ _ i h

/-- `n` rounded up to a multiple of `a`. -/
def roundUp (n a : Nat) : Nat := n + (a - n % a) % a

theorem le_roundUp (n a : Nat) : n ≤ roundUp n a := Nat.le_add_right _ _

theorem dvd_roundUp (n a : Nat) (ha : 0 < a) : a ∣ roundUp n a := by
  unfold roundUp
  have hmod := Nat.mod_lt n ha
  by_cases h : n % a = 0
  · simp [h, Nat.dvd_of_mod_eq_zero h]
  · rw [Nat.mod_eq_of_lt (by omega : a - n % a < a)]
    have := Nat.div_add_mod n a
    exact ⟨n / a + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩

theorem Alignment.pos (a : Alignment) : 0 < a.val := by
  obtain ⟨k, hk⟩ := a.property
  rw [hk]
  exact Nat.two_pow_pos k

/-- The largest of two alignments, which is a multiple of both. -/
def Alignment.max (a b : Alignment) : Alignment :=
  if a.val ≤ b.val then b else a

theorem Alignment.dvd_max_left (a b : Alignment) : a.val ∣ (Alignment.max a b).val := by
  obtain ⟨i, hi⟩ := a.property
  obtain ⟨j, hj⟩ := b.property
  unfold Alignment.max
  split
  · rw [hi, hj] at *
    exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ‹_›)
  · exact Nat.dvd_refl _

theorem Alignment.dvd_max_right (a b : Alignment) : b.val ∣ (Alignment.max a b).val := by
  obtain ⟨i, hi⟩ := a.property
  obtain ⟨j, hj⟩ := b.property
  unfold Alignment.max
  split
  · exact Nat.dvd_refl _
  · rw [hi, hj] at *
    exact Nat.pow_dvd_pow 2 (Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (Nat.lt_of_not_le ‹_›)))

/-- The offset of the second component of a pair. -/
def prodOffset (ra : Repr A) (rb : Repr B) : Nat := roundUp ra.size rb.align.val

/-- The size of a pair: the end of the second component, rounded up to the alignment of the pair. -/
def prodSize (ra : Repr A) (rb : Repr B) : Nat :=
  roundUp (prodOffset ra rb + rb.size) (Alignment.max ra.align rb.align).val

theorem prodOffset_le (ra : Repr A) (rb : Repr B) : ra.size ≤ prodOffset ra rb := le_roundUp _ _

theorem prodEnd_le (ra : Repr A) (rb : Repr B) : prodOffset ra rb + rb.size ≤ prodSize ra rb :=
  le_roundUp _ _

/-- The bytes of the first component of a pair. -/
def fstBytes (ra : Repr A) (rb : Repr B) (bytes : Vector Byte (prodSize ra rb)) :
    Vector Byte ra.size :=
  Vector.ofFn fun i => bytes[i.val]'(by
    have := prodOffset_le ra rb; have := prodEnd_le ra rb; omega)

/-- The bytes of the second component of a pair. -/
def sndBytes (ra : Repr A) (rb : Repr B) (bytes : Vector Byte (prodSize ra rb)) :
    Vector Byte rb.size :=
  Vector.ofFn fun i => bytes[prodOffset ra rb + i.val]'(by have := prodEnd_le ra rb; omega)

/-- The padding of a pair, which is not used by its components. -/
def IsPadding (ra : Repr A) (rb : Repr B) (i : Nat) : Prop :=
  ¬ i < ra.size ∧ ¬ (prodOffset ra rb ≤ i ∧ i < prodOffset ra rb + rb.size)

/-- The bytes of a pair, from the bytes of its components (the padding is uninitialized). -/
def prodBytes (ra : Repr A) (rb : Repr B) (ba : Vector Byte ra.size) (bb : Vector Byte rb.size) :
    Vector Byte (prodSize ra rb) :=
  Vector.ofFn fun i =>
    if h : i.val < ra.size then ba[i.val]
    else if h' : prodOffset ra rb ≤ i.val ∧ i.val < prodOffset ra rb + rb.size then
      bb[i.val - prodOffset ra rb]'(by omega)
    else .uninit

/-- The representation of a pair: the first component, then the second one aligned. -/
def prod {A B : Type} (ra : Repr A) (rb : Repr B) : Repr (A × B) where
  size := prodSize ra rb
  align := Alignment.max ra.align rb.align
  decode bytes := do
    let a ← ra.decode (fstBytes ra rb bytes)
    let b ← rb.decode (sndBytes ra rb bytes)
    some (a, b)
  encode value bytes :=
    ra.encode value.1 (fstBytes ra rb bytes) ∧ rb.encode value.2 (sndBytes ra rb bytes) ∧
    ∀ (i : Nat) (h : i < prodSize ra rb), IsPadding ra rb i → bytes[i] = .uninit
  aligned := dvd_roundUp _ _ (Alignment.pos _)
  encode_complete value := by
    obtain ⟨ba, ha⟩ := ra.encode_complete value.1
    obtain ⟨bb, hb⟩ := rb.encode_complete value.2
    have hoff := prodOffset_le ra rb
    refine ⟨prodBytes ra rb ba bb, ?_, ?_, ?_⟩
    · have : fstBytes ra rb (prodBytes ra rb ba bb) = ba := by
        apply Vector.ext; intro i hi; simp [fstBytes, prodBytes]
      rw [this]; exact ha
    · have : sndBytes ra rb (prodBytes ra rb ba bb) = bb := by
        apply Vector.ext; intro i hi
        by_cases h0 : rb.size = 0
        · omega
        · simp [sndBytes, prodBytes]
          intro hlt
          omega
      rw [this]; exact hb
    · intro i h hp
      obtain ⟨h1, h2⟩ := hp
      simp [prodBytes, h1, h2]
  encode_decode := by
    intro value bytes h
    obtain ⟨ha, hb, _⟩ := h
    simp [ra.encode_decode _ _ ha, rb.encode_decode _ _ hb]
  decode_mono := by
    intro bytes bytes' value decoded agree
    cases hda : ra.decode (fstBytes ra rb bytes) with
    | none => simp [hda] at decoded
    | some a =>
      cases hdb : rb.decode (sndBytes ra rb bytes) with
      | none => simp [hda, hdb] at decoded
      | some b =>
        have hoff := prodOffset_le ra rb
        have hend := prodEnd_le ra rb
        have ha' := ra.decode_mono _ (fstBytes ra rb bytes') a hda (by
          intro i hi
          simp only [fstBytes, Vector.getElem_ofFn] at hi ⊢
          exact agree ⟨i.val, by omega⟩ hi)
        have hb' := rb.decode_mono _ (sndBytes ra rb bytes') b hdb (by
          intro i hi
          simp only [sndBytes, Vector.getElem_ofFn] at hi ⊢
          exact agree ⟨prodOffset ra rb + i.val, by omega⟩ hi)
        simp [hda, hdb] at decoded
        simp [ha', hb', decoded]
  encode_valid := by
    intro value bytes i h
    obtain ⟨ha, hb, hpad⟩ := h
    have hoff := prodOffset_le ra rb
    by_cases h1 : i.val < ra.size
    · have := ra.encode_valid _ _ ⟨i.val, h1⟩ ha
      simpa [fstBytes] using this
    · by_cases h2 : prodOffset ra rb ≤ i.val ∧ i.val < prodOffset ra rb + rb.size
      · have := rb.encode_valid _ _ ⟨i.val - prodOffset ra rb, by omega⟩ hb
        simp only [sndBytes, Vector.getElem_ofFn] at this
        have e : prodOffset ra rb + (i.val - prodOffset ra rb) = i.val := by omega
        simpa [e] using this
      · rw [hpad i.val i.isLt ⟨h1, h2⟩]
        trivial

end Repr

/-! ### Instances -/

instance (ty : UScalarTy) : Pointee (UScalar ty) := ⟨Repr.uscalar ty⟩
instance (ty : IScalarTy) : Pointee (IScalar ty) := ⟨Repr.iscalar ty⟩
instance : Pointee Bool := ⟨Repr.bool⟩
instance {T : Type} : Pointee (RawPtr T) := ⟨Repr.pointer T⟩
instance : Pointee Unit := ⟨Repr.unit Unit () (fun _ => rfl)⟩
instance {A B : Type} [Pointee A] [Pointee B] : Pointee (A × B) :=
  ⟨Repr.prod (Pointee.repr (T := A)) (Pointee.repr (T := B))⟩

/-! ### Properties of the representations -/

/-- The representation of `T` is not zero-sized (the reads and writes of zero-sized values don't
access the heap). -/
class Pointee.Sized (T : Type) [Pointee T] : Prop where
  pos : 0 < (Pointee.repr (T := T)).size

/-- The encodings of the values of `T` contain no pointer bytes: writing them needs no provenance
evidence. -/
class Pointee.NoPointers (T : Type) [Pointee T] : Prop where
  no_pointers : ∀ (value : T) q, ¬ (Pointee.repr (T := T)).Carries value q

theorem Repr.ofBytes_noPointers (T : Type) (size : Nat) (align : Alignment)
    (aligned : align.val ∣ size) (encode : T → List U8) (decode : List U8 → Option T)
    (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value) (value : T) (q : RawPtr Unit) :
    ¬ (Repr.ofBytes T size align aligned encode decode length_encode decode_encode).Carries
      value q := by
  rintro ⟨bytes, hEnc, i, lane, hi⟩
  have hList : bytes.toList = (encode value).map Byte.data := hEnc
  have hGet : bytes[i.val] = ((encode value).map Byte.data)[i.val]'(by
      simp [length_encode]; exact i.isLt) := by
    simp only [← hList, Vector.getElem_toList]
  rw [hGet] at hi
  simp at hi

theorem _root_.Aeneas.Std.UScalarTy.numBits_div_eight_pos (ty : UScalarTy) :
    0 < ty.numBits / 8 := by
  cases ty <;> simp only [UScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_div_eight_pos (ty : IScalarTy) :
    0 < ty.numBits / 8 := by
  cases ty <;> simp only [IScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

instance (ty : UScalarTy) : Pointee.Sized (UScalar ty) := ⟨ty.numBits_div_eight_pos⟩
instance (ty : IScalarTy) : Pointee.Sized (IScalar ty) := ⟨ty.numBits_div_eight_pos⟩
instance : Pointee.Sized Bool := ⟨Nat.one_pos⟩
instance {T : Type} : Pointee.Sized (RawPtr T) := ⟨Nat.succ_pos 7⟩

instance (ty : UScalarTy) : Pointee.NoPointers (UScalar ty) :=
  ⟨fun value q => by
    show ¬ (Repr.uscalar ty).Carries value q
    unfold Repr.uscalar
    exact Repr.ofBytes_noPointers _ _ _ _ _ _ _ _ value q⟩
instance (ty : IScalarTy) : Pointee.NoPointers (IScalar ty) :=
  ⟨fun value q => by
    show ¬ (Repr.iscalar ty).Carries value q
    unfold Repr.iscalar
    exact Repr.ofBytes_noPointers _ _ _ _ _ _ _ _ value q⟩
instance : Pointee.NoPointers Bool :=
  ⟨fun value q => by
    show ¬ Repr.bool.Carries value q
    unfold Repr.bool
    exact Repr.ofBytes_noPointers _ _ _ _ _ _ _ _ value q⟩

/-! ### Calibrated representations

A representation is calibrated if the bytes from which a value is decoded (and whose pointer
bytes, if any, are carried by the value) are an admissible encoding of the value: exposing a safe
place, whose bytes are only known to decode to its value, then gives an admissible encoding. -/

theorem _root_.BitVec.toLEBytes_fromLEBytes (xs : List _root_.Byte) :
    (BitVec.fromLEBytes xs).toLEBytes = xs := by
  apply List.ext_getElem
  · rw [BitVec.toLEBytes_length]; omega
  · intro i h1 h2
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have := BitVec.toLEBytes_getElem_testBit (BitVec.fromLEBytes xs) i j h1 ⟨hj, by omega⟩
    rw [BitVec.getElem_eq_testBit_toNat, ← _root_.Byte.testBit, this, BitVec.fromLEBytes_getElem]
    have hd : (8 * i + j) / 8 = i := by omega
    have hm : (8 * i + j) % 8 = j := by omega
    simp only [hd, hm, _root_.Byte.testBit, BitVec.getElem_eq_testBit_toNat]

theorem _root_.BitVec.toLEBytes_cast {m n : Nat} (h : m = n) (x : BitVec m) :
    (x.cast h).toLEBytes = x.toLEBytes := by
  subst h; rfl

class Pointee.Calibrated (T : Type) [Pointee T] : Prop where
  calibrated : ∀ (value : T) (bytes : Vector Byte (Pointee.repr (T := T)).size),
    (Pointee.repr (T := T)).decode bytes = some value →
    (∀ i : Fin (Pointee.repr (T := T)).size, ∀ q lane, bytes[i.val] = .pointer q lane →
      (Pointee.repr (T := T)).Carries value q) →
    (Pointee.repr (T := T)).encode value bytes

theorem Repr.mapM_numeric_eq {bytes : List Byte} {xs : List U8}
    (h : bytes.mapM Byte.numeric = some xs) (noPointer : ∀ b ∈ bytes, ∀ q lane, b ≠ .pointer q lane) :
    bytes = xs.map Byte.data := by
  induction bytes generalizing xs with
  | nil => simp at h; simp [← h]
  | cons b bytes ih =>
    simp only [List.mapM_cons] at h
    cases hb : b.numeric with
    | none => simp [hb] at h
    | some x =>
      cases hr : bytes.mapM Byte.numeric with
      | none => simp [hb, hr] at h
      | some ys =>
        simp [hb, hr] at h
        subst h
        have hbx : b = .data x := by
          cases b with
          | uninit => simp [Byte.numeric] at hb
          | data v => simp [Byte.numeric] at hb; rw [hb]
          | pointer q lane => exact absurd rfl (noPointer _ (List.mem_cons_self) q lane)
        rw [hbx, ih hr (fun b hb => noPointer b (List.mem_cons_of_mem _ hb))]
        rfl

theorem Repr.ofBytes_calibrated (T : Type) (size : Nat) (align : Alignment)
    (aligned : align.val ∣ size) (encode : T → List U8) (decode : List U8 → Option T)
    (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value)
    (encode_decode : ∀ xs value, decode xs = some value → encode value = xs)
    (value : T) (bytes : Vector Byte size)
    (hdec : (Repr.ofBytes T size align aligned encode decode length_encode decode_encode).decode
      bytes = some value)
    (hptr : ∀ i : Fin size, ∀ q lane, bytes[i.val] = .pointer q lane →
      (Repr.ofBytes T size align aligned encode decode length_encode decode_encode).Carries
        value q) :
    (Repr.ofBytes T size align aligned encode decode length_encode decode_encode).encode
      value bytes := by
  change bytes.toList.mapM Byte.numeric >>= decode = some value at hdec
  show bytes.toList = (encode value).map Byte.data
  cases hm : bytes.toList.mapM Byte.numeric with
  | none => simp [hm] at hdec
  | some xs =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at hdec
    have noPointer : ∀ b ∈ bytes.toList, ∀ q lane, b ≠ .pointer q lane := by
      intro b hb q lane he
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hb
      have hi' : i < size := by simpa using hi
      apply Repr.ofBytes_noPointers T size align aligned encode decode length_encode
        decode_encode value q
      apply hptr ⟨i, hi'⟩ q lane
      simpa [← hget] using he
    rw [Repr.mapM_numeric_eq hm noPointer, encode_decode xs value hdec]

theorem Repr.uscalar_encode_decode (ty : UScalarTy) (xs : List U8) (value : UScalar ty)
    (h : (Repr.decodeLE ty.numBits xs).map UScalar.mk = some value) :
    value.bv.toLEBytes.map (UScalar.mk (ty := .U8)) = xs := by
  unfold Repr.decodeLE at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [BitVec.toLEBytes_cast, BitVec.toLEBytes_fromLEBytes, List.map_map]
    exact List.map_id _
  · simp at h

theorem Repr.iscalar_encode_decode (ty : IScalarTy) (xs : List U8) (value : IScalar ty)
    (h : (Repr.decodeLE ty.numBits xs).map IScalar.mk = some value) :
    value.bv.toLEBytes.map (UScalar.mk (ty := .U8)) = xs := by
  unfold Repr.decodeLE at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [BitVec.toLEBytes_cast, BitVec.toLEBytes_fromLEBytes, List.map_map]
    exact List.map_id _
  · simp at h

instance (ty : UScalarTy) : Pointee.Calibrated (UScalar ty) :=
  ⟨fun value bytes hdec hptr => by
    revert hdec hptr
    show (Repr.uscalar ty).decode bytes = some value → _ → (Repr.uscalar ty).encode value bytes
    unfold Repr.uscalar
    exact fun hdec hptr => Repr.ofBytes_calibrated _ _ _ _ _ _ _ _
      (fun xs v h => Repr.uscalar_encode_decode ty xs v h) value bytes hdec hptr⟩

instance (ty : IScalarTy) : Pointee.Calibrated (IScalar ty) :=
  ⟨fun value bytes hdec hptr => by
    revert hdec hptr
    show (Repr.iscalar ty).decode bytes = some value → _ → (Repr.iscalar ty).encode value bytes
    unfold Repr.iscalar
    exact fun hdec hptr => Repr.ofBytes_calibrated _ _ _ _ _ _ _ _
      (fun xs v h => Repr.iscalar_encode_decode ty xs v h) value bytes hdec hptr⟩

instance : Pointee.Calibrated Bool :=
  ⟨fun value bytes hdec hptr => by
    revert hdec hptr
    show Repr.bool.decode bytes = some value → _ → Repr.bool.encode value bytes
    unfold Repr.bool
    refine fun hdec hptr => Repr.ofBytes_calibrated _ _ _ _ _ _ _ _ ?_ value bytes hdec hptr
    intro xs v h
    match xs, h with
    | [x], h =>
      by_cases h0 : x = (⟨0#8⟩ : U8)
      · simp only [h0, if_true, Option.some.injEq] at h
        subst h; simp [h0]
      · by_cases h1 : x = (⟨1#8⟩ : U8)
        · have h10 : ¬ ((⟨1#8⟩ : U8) = (⟨0#8⟩ : U8)) := by decide
          simp only [h1, h10, if_false, if_true, Option.some.injEq] at h
          subst h; simp [h1]
        · simp [h0, h1] at h⟩

end Aeneas.Std
