/- The byte representations of the values stored behind raw pointers. -/
module
public import Aeneas.Std.Heap
public import Aeneas.Std.Scalar.Core
public import Aeneas.Data.BitVec
public section

namespace Aeneas.Std

/-- The byte representation (see `Repr`) of the values of type `T`, used by the models of the
raw-pointer functions to read and write values of type `T` in the heap.

The extracted code doesn't pass it explicitly: it is found by instance resolution. The stateful
functions receive the instances of their type parameters, and Aeneas generates the instances of the
structures (see `Repr.unspecified`, `Repr.prod` and `Repr.iso`). -/
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

The *model* of the representation of a structure stores the values of its fields, one after the
other, with padding to align them (as nested pairs: see `prod`). But Rust doesn't specify the layout
of the structures and tuples (`repr(Rust)`): the compiler can reorder the fields, add padding, and two
structures with the same fields need not have the same layout. The representation of a structure is
thus `Repr.unspecified`, an unknown representation of its own, of which only a few properties of the
model are known: the code which depends on the layout (through `size_of`, `align_of`, or byte
accesses of the structure) can't be verified. -/

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

/-- The properties which every representation of a structure (or tuple) by rustc has, given its
model `model` (the fields one after the other, see `prod`), whatever its layout: the actual
representation stores the encodings of the fields at some offsets, without overlap, and leaves the
rest (the padding) uninitialized.
- `sized`: if a field isn't zero-sized, the structure isn't either (the fields don't overlap and are
  within the structure).
- `carries`: the pointers carried by the encodings of a value (see `Repr.Carries`) are carried by the
  encodings of its fields, thus by the model.

It contains nothing about the size, the alignment or the offsets of the fields, which depend on the
layout. In particular, the model being calibrated (see `Pointee.Calibrated`) doesn't imply that the
actual representation is: a calibrated model has no padding, but the actual layout may have some (for
instance after reordering the fields, as with `-Zrandomize-layout`), and the padding of an encoding is
uninitialized whereas the bytes from which a value is decoded may initialize it. -/
structure Repr.LayoutOf {T : Type} (model r : Repr T) : Prop where
  sized : 0 < model.size → 0 < r.size
  carries : ∀ value q, r.Carries value q → model.Carries value q

/-- The unknown representation of the structure (or tuple) `T`, whose model is `model` (see
`Repr.LayoutOf`). It is indexed by the type `T`, so that two distinct types with the same model can't be
proved to have the same representation. It is opaque: its value (the model) is only used to show that
such a representation exists. -/
opaque Repr.unspecified (T : Type) (model : Repr T) : {r : Repr T // Repr.LayoutOf model r} :=
  ⟨model, ⟨id, fun _ _ h => h⟩⟩

theorem Repr.unspecified_sized {T : Type} {model : Repr T} (h : 0 < model.size) :
    0 < (Repr.unspecified T model).1.size :=
  (Repr.unspecified T model).2.sized h

theorem Repr.unspecified_carries {T : Type} {model : Repr T} {value : T} {q : RawPtr Unit}
    (h : (Repr.unspecified T model).1.Carries value q) : model.Carries value q :=
  (Repr.unspecified T model).2.carries value q h

/-! ### Instances -/

instance (ty : UScalarTy) : Pointee (UScalar ty) := ⟨Repr.uscalar ty⟩
instance (ty : IScalarTy) : Pointee (IScalar ty) := ⟨Repr.iscalar ty⟩
instance : Pointee Bool := ⟨Repr.bool⟩
instance {T : Type} : Pointee (RawPtr T) := ⟨Repr.pointer T⟩
/-- The unit type `()` is guaranteed to have size 0 and alignment 1. -/
instance : Pointee Unit := ⟨Repr.unit Unit () (fun _ => rfl)⟩
/-- The layout of the tuples is unspecified (see `Repr.unspecified`). -/
instance {A B : Type} [Pointee A] [Pointee B] : Pointee (A × B) :=
  ⟨(Repr.unspecified (A × B) (Repr.prod (Pointee.repr (T := A)) (Pointee.repr (T := B)))).1⟩

end Aeneas.Std
