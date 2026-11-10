/- Separation-logic specifications for typed accesses through casts to byte buffers. -/
module
public import Aeneas.Std.UninitSpecs
public import Aeneas.Std.CopySpecs
public import Aeneas.Std.Core.PointeeArray
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.RawPtrOps
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
@[expose] public section

/-! # Typed views of byte buffers, through casts

A value written or read through `p.cast U` (for a byte pointer `p : RawPtr U8`) corresponds to its
little-endian bytes in the `u8` cells. `Pointee.Plain U` gives these bytes (`toBytes v`) and states
that the representation of `U` stores exactly them (`Repr.IsPlain`: no padding, no pointer byte).
The scalars and the arrays of plain values are plain.

- Views: `RawPtr.readable_cast_bytes` (a readable value, for instance a `from_ref` exposure, is
  readable as its bytes), `RawPtr.readable_bytes_cast`, `RawPtr.pointsTo_cast_bytes`,
  `RawPtr.bytes_pointsTo_cast` (the typed direction needs an aligned address).
- Unaligned accesses within a `↦?*` byte buffer: `MutRawPtr.write_unaligned.spec_cast` and
  `RawPtr.read_unaligned.spec_cast` (no alignment needed), and `read_unaligned` from readable bytes.
- `size_of` and `align_of` of the scalars and of the arrays.

The size lemmas (`Pointee.size_uscalar`, `Pointee.size_iscalar`, `Pointee.size_u8`,
`Pointee.size_array`) are in `scalar_tac_simps` and `step_pre_simps`, for the side conditions on byte
counts, but not `@[simp]` (making them so changes the behavior of `simp` in existing proofs, which
unfold the sizes of the structures): pass them to `simp` explicitly.

`copy_nonoverlapping(from_ref(&x).cast::<u8>(), dst, n)` (copying the bytes of a value) has its
specification, `core.ptr.copy_nonoverlapping.spec_readable_cast`, which keeps the typed view of the
source (for the backward function of `from_ref`). It is not `@[step]`: its program also matches
`core.ptr.copy_nonoverlapping.spec_readable_src_head`, and `step` doesn't backtrack; use it with
`step with`. -/

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP core.mem.maybe_uninit

set_option maxHeartbeats 1000000

/-! ## Plain byte representations -/

namespace Repr

/-- `r` stores a value `v` as the data bytes `bytes v` (no padding, no pointer): the admissible
encodings are exactly these data bytes, and a chunk decodes to `v` exactly when the numerical values
of its bytes are `bytes v`. -/
structure IsPlain {T : Type} (r : Repr T) (bytes : T → List U8) : Prop where
  length : ∀ v, (bytes v).length = r.size
  encode_iff : ∀ v (b : Vector Byte r.size), r.encode v b ↔ b.toList = (bytes v).map Byte.data
  decode_iff : ∀ v (b : Vector Byte r.size),
    r.decode b = some v ↔ b.toList.mapM Byte.numeric = some (bytes v)

theorem IsPlain.unaligned {T : Type} {r : Repr T} {bytes : T → List U8} (h : r.IsPlain bytes) :
    r.unaligned.IsPlain bytes := ⟨h.1, h.2, h.3⟩

theorem IsPlain.noPointers {T : Type} {r : Repr T} {bytes : T → List U8} (h : r.IsPlain bytes)
    (v : T) (q : RawPtr Unit) : ¬ r.Carries v q := by
  rintro ⟨b, he, i, lane, hi⟩
  have hl := (h.encode_iff v b).mp he
  have hg : b[i.val] = ((bytes v).map Byte.data)[i.val]'(by simp [h.length]) := by
    simp only [← hl, Vector.getElem_toList]
  rw [hg] at hi
  simp at hi

theorem ofBytes_isPlain (T : Type) (size : Nat) (align : Alignment)
    (aligned : align.val ∣ size) (encode : T → List U8) (decode : List U8 → Option T)
    (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value)
    (encode_decode : ∀ xs value, decode xs = some value → encode value = xs) :
    (Repr.ofBytes T size align aligned encode decode length_encode decode_encode).IsPlain
      encode where
  length := length_encode
  encode_iff _ _ := Iff.rfl
  decode_iff v b := by
    show b.toList.mapM Byte.numeric >>= decode = some v ↔ _
    cases hm : b.toList.mapM Byte.numeric with
    | none => simp
    | some xs =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
      constructor
      · intro hd; exact (encode_decode xs v hd).symm
      · intro he; subst he; exact decode_encode v

theorem unit_isPlain (T : Type) (value : T) (unique : ∀ x : T, x = value) :
    (Repr.unit T value unique).IsPlain (fun _ => []) where
  length _ := rfl
  encode_iff _ b := by
    show True ↔ _
    have : b.toList = [] := by apply List.eq_nil_of_length_eq_zero; simp; rfl
    simp [this]
  decode_iff v b := by
    show some value = some v ↔ _
    have : b.toList = [] := by apply List.eq_nil_of_length_eq_zero; simp; rfl
    simp [this, ← unique v]

theorem iso_isPlain {A B : Type} {r : Repr A} {fa : A → List U8} (h : r.IsPlain fa)
    (f : B → A) (g : A → B) (gf : ∀ b, g (f b) = b) (fg : ∀ a, f (g a) = a) :
    (Repr.iso r f g gf).IsPlain (fun b => fa (f b)) where
  length b := h.length (f b)
  encode_iff b bytes := h.encode_iff (f b) bytes
  decode_iff b := by
    show ∀ bytes : Vector Byte r.size, (r.decode bytes).map g = some b ↔
      bytes.toList.mapM Byte.numeric = some (fa (f b))
    intro bytes
    rw [← h.decode_iff]
    constructor
    · intro hd
      cases hr : r.decode bytes with
      | none => simp [hr] at hd
      | some a =>
        simp only [hr, Option.map_some, Option.some.injEq] at hd
        subst hd
        rw [fg]
    · intro hd
      simp [hd, gf]

theorem roundUp_of_dvd {n a : Nat} (h : a ∣ n) : roundUp n a = n := by
  unfold roundUp
  rw [Nat.mod_eq_zero_of_dvd h, Nat.sub_zero, Nat.mod_self, Nat.add_zero]

/-- Without padding, the bytes of a pair are the bytes of its first component followed by the bytes
of its second component. -/
theorem prod_toList {A B : Type} (ra : Repr A) (rb : Repr B)
    (hoff : prodOffset ra rb = ra.size) (hsize : prodSize ra rb = ra.size + rb.size)
    (bytes : Vector Byte (prodSize ra rb)) :
    bytes.toList = (fstBytes ra rb bytes).toList ++ (sndBytes ra rb bytes).toList := by
  apply List.ext_getElem
  · simp [hsize]
  · intro k h1 h2
    simp only [Vector.getElem_toList]
    by_cases hk : k < ra.size
    · rw [List.getElem_append_left (by simpa using hk)]
      simp [fstBytes]
    · rw [List.getElem_append_right (by simpa using hk)]
      simp only [sndBytes,
        Vector.toList_ofFn, List.getElem_ofFn]
      congr 1
      simp at hk ⊢
      omega

theorem mapM_numeric_length {bytes : List Byte} {xs : List U8}
    (h : bytes.mapM Byte.numeric = some xs) : xs.length = bytes.length := by
  induction bytes generalizing xs with
  | nil => simp at h; simp [← h]
  | cons b bs ih =>
    simp only [List.mapM_cons] at h
    cases hb : b.numeric <;> simp [hb] at h
    cases hr : bs.mapM Byte.numeric <;> simp [hr] at h
    subst h
    simp [ih hr]

theorem mapM_numeric_append {l₁ l₂ : List Byte} {xs₁ xs₂ : List U8}
    (hl : l₁.length = xs₁.length) :
    (l₁ ++ l₂).mapM Byte.numeric = some (xs₁ ++ xs₂) ↔
      l₁.mapM Byte.numeric = some xs₁ ∧ l₂.mapM Byte.numeric = some xs₂ := by
  rw [List.mapM_append]
  constructor
  · intro h
    cases h₁ : l₁.mapM Byte.numeric with
    | none => simp [h₁] at h
    | some ys₁ =>
      cases h₂ : l₂.mapM Byte.numeric with
      | none => simp [h₁, h₂] at h
      | some ys₂ =>
        simp only [h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        have hlen : ys₁.length = xs₁.length := by rw [mapM_numeric_length h₁, hl]
        obtain ⟨e₁, e₂⟩ := List.append_inj h hlen
        subst e₁ e₂
        exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem prod_isPlain {A B : Type} {ra : Repr A} {rb : Repr B} {fa : A → List U8}
    {fb : B → List U8} (ha : ra.IsPlain fa) (hb : rb.IsPlain fb)
    (hoff : prodOffset ra rb = ra.size) (hsize : prodSize ra rb = ra.size + rb.size) :
    (Repr.prod ra rb).IsPlain (fun p => fa p.1 ++ fb p.2) where
  length p := by
    show _ = prodSize ra rb
    simp [ha.length, hb.length, hsize]
  encode_iff p := by
    show ∀ bytes : Vector Byte (prodSize ra rb), (ra.encode p.1 (fstBytes ra rb bytes) ∧ rb.encode p.2 (sndBytes ra rb bytes) ∧
      ∀ (i : Nat) (h : i < prodSize ra rb), IsPadding ra rb i → bytes[i] = .uninit) ↔
        bytes.toList = (fa p.1 ++ fb p.2).map Byte.data
    intro bytes
    rw [ha.encode_iff, hb.encode_iff, prod_toList ra rb hoff hsize, List.map_append]
    have hnopad : ∀ (i : Nat) (h : i < prodSize ra rb), IsPadding ra rb i →
        bytes[i] = .uninit := by
      intro i h hp
      exfalso
      obtain ⟨h1, h2⟩ := hp
      omega
    constructor
    · rintro ⟨e₁, e₂, _⟩; rw [e₁, e₂]
    · intro he
      obtain ⟨e₁, e₂⟩ := List.append_inj he (by simp [ha.length])
      exact ⟨e₁, e₂, hnopad⟩
  decode_iff p := by
    show ∀ bytes : Vector Byte (prodSize ra rb), (do
      let a ← ra.decode (fstBytes ra rb bytes)
      let b ← rb.decode (sndBytes ra rb bytes)
      some (a, b)) = some p ↔ bytes.toList.mapM Byte.numeric = some (fa p.1 ++ fb p.2)
    intro bytes
    rw [prod_toList ra rb hoff hsize, mapM_numeric_append (by simp [ha.length]),
      ← ha.decode_iff, ← hb.decode_iff]
    obtain ⟨a, b⟩ := p
    cases h₁ : ra.decode (fstBytes ra rb bytes) <;>
      cases h₂ : rb.decode (sndBytes ra rb bytes) <;> simp

theorem Alignment.max_self (a : Alignment) : Alignment.max a a = a := by
  simp [Alignment.max]

theorem Alignment.max_val_of_dvd (a b : Alignment) (h : b.val ∣ a.val) :
    (Alignment.max a b).val = a.val := by
  unfold Alignment.max
  split
  · exact Nat.le_antisymm (Nat.le_of_dvd (Alignment.pos a) h) ‹_›
  · rfl

theorem listN_size_align {T : Type} (r : Repr T) (n : Nat) :
    (Repr.listN r n).size = n * r.size ∧ (Repr.listN r n).align.val ∣ r.align.val := by
  induction n with
  | zero => exact ⟨by show 0 = 0 * r.size; simp, Nat.one_dvd _⟩
  | succ n ih =>
    obtain ⟨hs, ha⟩ := ih
    have hoff : prodOffset r (Repr.listN r n) = r.size :=
      roundUp_of_dvd (Nat.dvd_trans ha r.aligned)
    have hmax := Alignment.max_val_of_dvd r.align (Repr.listN r n).align ha
    refine ⟨?_, ?_⟩
    · show prodSize r (Repr.listN r n) = _
      unfold prodSize
      rw [hoff, hmax, hs, roundUp_of_dvd]
      · ring
      · exact Nat.dvd_add r.aligned (Nat.dvd_trans r.aligned (Nat.dvd_mul_left _ _))
    · show (Alignment.max r.align (Repr.listN r n).align).val ∣ _
      rw [hmax]

theorem listN_size {T : Type} (r : Repr T) (n : Nat) : (Repr.listN r n).size = n * r.size :=
  (listN_size_align r n).1

theorem listN_align {T : Type} (r : Repr T) (n : Nat) (hn : 0 < n) :
    (Repr.listN r n).align.val = r.align.val := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Alignment.max_val_of_dvd r.align _ (listN_size_align r m).2

theorem listN_isPlain {T : Type} {r : Repr T} {f : T → List U8} (h : r.IsPlain f) (n : Nat) :
    (Repr.listN r n).IsPlain (fun l => l.val.flatMap f) := by
  induction n with
  | zero =>
    have := unit_isPlain {l : List T // l.length = 0} ⟨[], rfl⟩ (by
      rintro ⟨l, hl⟩
      cases l with
      | nil => rfl
      | cons _ _ => simp at hl)
    refine ⟨fun l => ?_, fun l b => ?_, fun l b => ?_⟩
    · obtain ⟨l, hl⟩ := l
      cases l with
      | nil => exact this.length ⟨[], hl⟩
      | cons => simp at hl
    · obtain ⟨l, hl⟩ := l
      cases l with
      | nil => exact this.encode_iff ⟨[], hl⟩ b
      | cons => simp at hl
    · obtain ⟨l, hl⟩ := l
      cases l with
      | nil => exact this.decode_iff ⟨[], hl⟩ b
      | cons => simp at hl
  | succ n ih =>
    obtain ⟨hs, ha⟩ := listN_size_align r n
    have hoff : prodOffset r (Repr.listN r n) = r.size :=
      roundUp_of_dvd (Nat.dvd_trans ha r.aligned)
    have hsize : prodSize r (Repr.listN r n) = r.size + (Repr.listN r n).size :=
      (listN_size_align r (n + 1)).1.trans (by rw [hs]; ring)
    have hp := prod_isPlain h ih hoff hsize
    have hi := iso_isPlain hp
      (fun l : {l : List T // l.length = n + 1} => match l with
        | ⟨x :: xs, h⟩ => (x, ⟨xs, by simpa using h⟩)
        | ⟨[], h⟩ => absurd h (by simp))
      (fun p => ⟨p.1 :: p.2.val, by simp [p.2.property]⟩)
      (by
        rintro ⟨l, h⟩
        cases l with
        | nil => simp at h
        | cons x xs => rfl)
      (by rintro ⟨x, xs⟩; rfl)
    have e : ∀ l : {l : List T // l.length = n + 1}, l.val.flatMap f =
        (fun p : T × {l : List T // l.length = n} => f p.1 ++ p.2.val.flatMap f)
          (match l with
            | ⟨x :: xs, h⟩ => (x, ⟨xs, by simpa using h⟩)
            | ⟨[], h⟩ => absurd h (by simp)) := by
      rintro ⟨l, h⟩
      cases l with
      | nil => simp at h
      | cons x xs => simp
    simp only [e]
    exact hi

end Repr

/-! ## The `Pointee.Plain` class -/

/-- The values of `T` are stored as the plain little-endian data bytes `toBytes v` (no padding, no
pointer bytes): see `Repr.IsPlain`. The scalars and the arrays of plain values are plain. -/
class Pointee.Plain (T : Type) [Pointee T] where
  toBytes : T → List U8
  isPlain : (Pointee.repr (T := T)).IsPlain toBytes

export Pointee.Plain (toBytes)

/-- The little-endian bytes of an unsigned scalar. -/
def UScalar.leBytes {ty : UScalarTy} (v : UScalar ty) : List U8 := v.bv.toLEBytes.map (UScalar.mk (ty := .U8))

/-- The little-endian (two's complement) bytes of a signed scalar. -/
def IScalar.leBytes {ty : IScalarTy} (v : IScalar ty) : List U8 := v.bv.toLEBytes.map (UScalar.mk (ty := .U8))

instance (ty : UScalarTy) : Pointee.Plain (UScalar ty) where
  toBytes := UScalar.leBytes
  isPlain := by
    show (Repr.uscalar ty).IsPlain _
    unfold Repr.uscalar
    exact Repr.ofBytes_isPlain _ _ _ _ _ _ _ _ (fun xs v h => Repr.uscalar_encode_decode ty xs v h)

instance (ty : IScalarTy) : Pointee.Plain (IScalar ty) where
  toBytes := IScalar.leBytes
  isPlain := by
    show (Repr.iscalar ty).IsPlain _
    unfold Repr.iscalar
    exact Repr.ofBytes_isPlain _ _ _ _ _ _ _ _ (fun xs v h => Repr.iscalar_encode_decode ty xs v h)

instance {T : Type} [Pointee T] [Pointee.Plain T] {N : Usize} : Pointee.Plain (Array T N) where
  toBytes a := a.val.flatMap toBytes
  isPlain := Repr.iso_isPlain (Repr.listN_isPlain Pointee.Plain.isPlain N.val) _ _ _
    (fun l => Subtype.ext (Array.from_val l.val l.property))

namespace Pointee

@[simp] theorem toBytes_uscalar {ty : UScalarTy} (v : UScalar ty) :
    toBytes v = v.bv.toLEBytes.map (UScalar.mk (ty := .U8)) := rfl

@[simp] theorem toBytes_iscalar {ty : IScalarTy} (v : IScalar ty) :
    toBytes v = v.bv.toLEBytes.map (UScalar.mk (ty := .U8)) := rfl

@[simp] theorem toBytes_array {T : Type} [Pointee T] [Pointee.Plain T] {N : Usize}
    (a : Array T N) : toBytes a = a.val.flatMap toBytes := rfl

@[simp] theorem length_toBytes {T : Type} [Pointee T] [Pointee.Plain T] (v : T) :
    (toBytes v).length = (Pointee.repr (T := T)).size :=
  Pointee.Plain.isPlain.length v

@[scalar_tac_simps, step_pre_simps]
theorem size_uscalar (ty : UScalarTy) :
    (Pointee.repr (T := UScalar ty)).size = ty.numBits / 8 := rfl

@[scalar_tac_simps, step_pre_simps]
theorem size_iscalar (ty : IScalarTy) :
    (Pointee.repr (T := IScalar ty)).size = ty.numBits / 8 := rfl

theorem align_uscalar (ty : UScalarTy) :
    (Pointee.repr (T := UScalar ty)).align.val = ty.numBits / 8 := rfl

theorem align_iscalar (ty : IScalarTy) :
    (Pointee.repr (T := IScalar ty)).align.val = ty.numBits / 8 := rfl

@[scalar_tac_simps, step_pre_simps]
theorem size_array (T : Type) [Pointee T] (N : Usize) :
    (Pointee.repr (T := Array T N)).size = N.val * (Pointee.repr (T := T)).size :=
  Repr.listN_size _ _

theorem align_array (T : Type) [Pointee T] (N : Usize) (hN : 0 < N.val) :
    (Pointee.repr (T := Array T N)).align.val = (Pointee.repr (T := T)).align.val :=
  Repr.listN_align _ _ hN

@[scalar_tac_simps, step_pre_simps]
theorem size_u8 : (Pointee.repr (T := U8)).size = 1 := rfl

theorem align_u8 : (Pointee.repr (T := U8)).align.val = 1 := rfl

/-- A byte is its own byte list. -/
@[simp] theorem toBytes_u8 (x : U8) : toBytes x = [x] := by
  show (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))) = [x]
  obtain ⟨bv⟩ := x
  have h : ∀ b : BitVec 8, b.toLEBytes = [b] := by
    intro b
    unfold BitVec.toLEBytes
    simp [BitVec.toLEBytes]
  show List.map (UScalar.mk (ty := .U8)) (BitVec.toLEBytes (w := 8) bv) = [⟨bv⟩]
  rw [h bv]; rfl

/-- An array of positive length of a type which isn't zero-sized isn't zero-sized. -/
theorem Sized.array (T : Type) [Pointee T] [Pointee.Sized T] (N : Usize) (hN : 0 < N.val) :
    Pointee.Sized (Array T N) :=
  ⟨by rw [size_array]; exact Nat.mul_pos hN Pointee.Sized.pos⟩

instance (T : Type) [Pointee T] [Pointee.Sized T] (N : Usize) [Fact (0 < N.val)] :
    Pointee.Sized (Array T N) :=
  Sized.array T N Fact.out

/-- An array whose length is a positive numeral (`Array U64 2#usize`): no `Fact` needed (the
numeral unifies with `n + 1`). -/
instance Sized.array_ofNat (T : Type) [Pointee T] [Pointee.Sized T] (n : Nat)
    (h : n + 1 ≤ UScalar.cMax .Usize) : Pointee.Sized (Array T (Usize.ofNat (n + 1) h)) :=
  Sized.array T _ (by simp)

theorem Plain.noPointers (T : Type) [Pointee T] [Pointee.Plain T] : Pointee.NoPointers T :=
  ⟨Pointee.Plain.isPlain.noPointers⟩

instance (T : Type) [Pointee T] [Pointee.Plain T] (N : Usize) : Pointee.NoPointers (Array T N) :=
  Plain.noPointers _

end Pointee

/-! ## Byte cells, and typed views of them -/

theorem mapM_numeric_iff (bs : List Byte) (xs : List U8) :
    bs.mapM Byte.numeric = some xs ↔
      bs.length = xs.length ∧ ∀ i (h₁ : i < bs.length) (h₂ : i < xs.length), bs[i].numeric = some xs[i] := by
  induction bs generalizing xs with
  | nil => cases xs <;> simp
  | cons b bs ih =>
    cases xs with
    | nil =>
      simp only [List.mapM_cons, List.length_cons, List.length_nil]
      constructor
      · intro h; cases hb : b.numeric <;> cases hr : bs.mapM Byte.numeric <;> simp [hb, hr] at h
      · intro h; omega
    | cons x xs =>
      simp only [List.mapM_cons, List.length_cons]
      constructor
      · intro h
        cases hb : b.numeric <;> cases hr : bs.mapM Byte.numeric <;> simp [hb, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hall⟩ := (ih _).mp hr
        refine ⟨by omega, fun i h₁ h₂ => ?_⟩
        cases i with
        | zero => simpa using hb
        | succ i => exact hall i (by simp at h₁; omega) (by simp at h₂; omega)
      · rintro ⟨hl, hall⟩
        have hb := hall 0 (by simp) (by simp)
        have hr := (ih xs).mpr ⟨by omega, fun i h₁ h₂ =>
          hall (i + 1) (by simp; omega) (by simp; omega)⟩
        simp only [List.getElem_cons_zero] at hb
        simp [hb, hr]

namespace Bytes

/-- The single cell of a byte, as a chunk of a `u8` range. -/
def u8Chunk (b : Byte) : Vector Byte (Pointee.repr (T := U8)).size := ⟨#[b], rfl⟩

theorem u8Chunk_eq (c : Vector Byte (Pointee.repr (T := U8)).size) :
    c = u8Chunk (c[0]'(by rw [Pointee.size_u8]; decide)) := by
  apply Vector.ext
  intro i hi
  have : i = 0 := by rw [Pointee.size_u8] at hi; omega
  subst this
  rfl

theorem decode_u8Chunk (b : Byte) :
    (Pointee.repr (T := U8)).decode (u8Chunk b) = b.numeric := by
  apply Option.ext
  intro x
  rw [(Pointee.Plain.isPlain (T := U8)).decode_iff, Pointee.toBytes_u8]
  show [b].mapM Byte.numeric = some [x] ↔ _
  cases hb : b.numeric <;> simp [hb]

theorem u8Chunk_map_toList (b : Byte) (f : Byte → Cell) : ((u8Chunk b).map f).toList = [f b] := by
  rw [Vector.toList_map]; rfl

theorem flatMap_u8 (l : List (Vector Byte (Pointee.repr (T := U8)).size)) (f : Byte → Cell)
    (h0 : 0 < (Pointee.repr (T := U8)).size) :
    l.flatMap (fun a => (a.map f).toList) = (l.map (fun c => c[0]'h0)).map f := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, ih, u8Chunk_eq c, u8Chunk_map_toList]
    rfl

theorem flatMap_u8Chunk (bs : List Byte) (f : Byte → Cell) :
    (bs.map u8Chunk).flatMap (fun a => (a.map f).toList) = bs.map f := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.map_cons, List.flatMap_cons, ih, u8Chunk_map_toList]; rfl

/-- A range of `u8` cells is a list of bytes, one per element. -/
theorem rangeWith_u8_iff {V : Type} (valid : V → Vector Byte (Pointee.repr (T := U8)).size → Prop)
    (p : RawPtr U8) (bptr : BasePtr) (vs : List V) (d : Nat) (h : Fragment) :
    rangeWith (Pointee.repr (T := U8)) valid p bptr (listVec vs) d h ↔
      ∃ bs : List Byte, bs.length = vs.length ∧
        (∀ i (hb : i < bs.length) (hv : i < vs.length), valid vs[i] (u8Chunk bs[i])) ∧
        block (Pointee.repr (T := U8)) p bptr (bs.map (Cell.shared d)) h := by
  have h0 : 0 < (Pointee.repr (T := U8)).size := by rw [Pointee.size_u8]; decide
  constructor
  · rintro ⟨data, hv, hb⟩
    refine ⟨data.toList.map (fun c => c[0]'h0), by rw [List.length_map]; exact data.length_toList,
      fun i hb hv' => ?_, ?_⟩
    · have := hv ⟨i, by simpa using hv'⟩
      simp only [List.getElem_map, Vector.getElem_toList]
      rw [← u8Chunk_eq]
      simpa [listVec] using this
    · have e : (data.flatMap (fun bytes => bytes.map (Cell.shared d))).toList =
          (data.toList.map (fun c => c[0]'h0)).map (Cell.shared d) := by
        rw [Vector.toList_flatMap', flatMap_u8 _ _ h0]
      rwa [← e]
  · rintro ⟨bs, hl, hv, hb⟩
    refine ⟨⟨(bs.map u8Chunk).toArray, by simp only [List.size_toArray]; exact (List.length_map _).trans hl⟩, fun i => ?_, ?_⟩
    · have := hv i.val (by rw [hl]; exact i.isLt) i.isLt
      simp only [listVec, Vector.getElem_mk, List.getElem_toArray, List.getElem_map]
      exact this
    · have e : ((⟨(bs.map u8Chunk).toArray, by simp only [List.size_toArray]; exact (List.length_map _).trans hl⟩ : Vector _ vs.length).flatMap
          (fun bytes => bytes.map (Cell.shared d))).toList = bs.map (Cell.shared d) := by
        rw [Vector.toList_flatMap']
        exact flatMap_u8Chunk bs _
      rwa [e]

theorem block_cast {T U : Type} (r : Repr T) (r' : Repr U) (p : RawPtr T) (bptr : BasePtr)
    (cells : List Cell) (h : Fragment) (ha : r'.align.val ∣ p.address.val) :
    block r p bptr cells h → block r' (p.cast U) bptr cells h := by
  rintro ⟨hlo, _, rfl⟩
  exact ⟨hlo, ha, rfl⟩

theorem block_cast_u8 {T : Type} (r : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (cells : List Cell) (h : Fragment) :
    block r p bptr cells h → block (Pointee.repr (T := U8)) (p.cast U8) bptr cells h :=
  block_cast r _ p bptr cells h (by rw [Pointee.align_u8]; exact Nat.one_dvd _)

/-- The cells of a value `v` of a plain type are byte cells whose numerical values are the bytes of
`v`. -/
theorem readable_bytes {U : Type} {r : Repr U} {f : U → List U8} (hp : r.IsPlain f) (q : RawPtr U)
    (bptr : BasePtr) (v : U) (d : Nat) (h : Fragment) (hr : readable r q bptr v d h) :
    ∃ bs : List Byte, bs.mapM Byte.numeric = some (f v) ∧
      block (Pointee.repr (T := U8)) (q.cast U8) bptr (bs.map (Cell.shared d)) h := by
  obtain ⟨data, hdec, hb⟩ := hr
  refine ⟨data.toList, (hp.decode_iff v data).mp hdec, ?_⟩
  rw [← Vector.toList_map]
  exact block_cast_u8 r q bptr _ h hb

/-- Byte cells whose numerical values are the bytes of `v` are cells of `v`, at an aligned
address. -/
theorem bytes_readable {U : Type} {r : Repr U} {f : U → List U8} (hp : r.IsPlain f)
    (p : RawPtr U8) (bptr : BasePtr) (v : U) (d : Nat) (h : Fragment) (bs : List Byte)
    (hbs : bs.mapM Byte.numeric = some (f v)) (ha : r.align.val ∣ p.address.val)
    (hb : block (Pointee.repr (T := U8)) p bptr (bs.map (Cell.shared d)) h) :
    readable r (p.cast U) bptr v d h := by
  have hl : bs.length = r.size := by rw [← Repr.mapM_numeric_length hbs, hp.length]
  refine ⟨⟨bs.toArray, by simpa using hl⟩, (hp.decode_iff v _).mpr (by simpa using hbs), ?_⟩
  have : (Vector.map (Cell.shared d) (⟨bs.toArray, by simpa using hl⟩ : Vector Byte r.size)).toList =
      bs.map (Cell.shared d) := by
    rw [Vector.toList_map]; rfl
  rw [this]
  exact block_cast _ r p bptr _ h ha hb

/-- The owned cells of a value `v` of a plain type are the data bytes of `v`. -/
theorem pointsTo_bytes {U : Type} {r : Repr U} {f : U → List U8} (hp : r.IsPlain f)
    (q : RawPtr U) (bptr : BasePtr) (v : U) (d : Nat) (h : Fragment) (hr : pointsTo r q bptr v d h) :
    block (Pointee.repr (T := U8)) (q.cast U8) bptr (((f v).map Byte.data).map (Cell.shared d)) h := by
  obtain ⟨data, henc, hb⟩ := hr
  rw [← (hp.encode_iff v data).mp henc, ← Vector.toList_map]
  exact block_cast_u8 r q bptr _ h hb

theorem bytes_pointsTo {U : Type} {r : Repr U} {f : U → List U8} (hp : r.IsPlain f)
    (p : RawPtr U8) (bptr : BasePtr) (v : U) (d : Nat) (h : Fragment)
    (ha : r.align.val ∣ p.address.val)
    (hb : block (Pointee.repr (T := U8)) p bptr (((f v).map Byte.data).map (Cell.shared d)) h) :
    pointsTo r (p.cast U) bptr v d h := by
  have hl : ((f v).map Byte.data).length = r.size := by rw [List.length_map, hp.length]
  refine ⟨⟨((f v).map Byte.data).toArray, by simpa using hl⟩, (hp.encode_iff v _).mpr rfl, ?_⟩
  have : (Vector.map (Cell.shared d)
      (⟨((f v).map Byte.data).toArray, by simpa using hl⟩ : Vector Byte r.size)).toList =
      ((f v).map Byte.data).map (Cell.shared d) := by
    rw [Vector.toList_map]; rfl
  rw [this]
  exact block_cast _ r p bptr _ h ha hb

/-- A readable range of `u8` is a list of byte cells with these numerical values. -/
theorem readableRange_u8_iff (p : RawPtr U8) (bptr : BasePtr) (xs : List U8) (d : Nat)
    (h : Fragment) :
    readableRange (Pointee.repr (T := U8)) p bptr (listVec xs) d h ↔
      ∃ bs : List Byte, bs.mapM Byte.numeric = some xs ∧
        block (Pointee.repr (T := U8)) p bptr (bs.map (Cell.shared d)) h := by
  rw [readableRange_eq_rangeWith, rangeWith_u8_iff]
  constructor
  · rintro ⟨bs, hl, hv, hb⟩
    refine ⟨bs, (mapM_numeric_iff bs xs).mpr ⟨hl, fun i h₁ h₂ => ?_⟩, hb⟩
    rw [← decode_u8Chunk]; exact hv i h₁ h₂
  · rintro ⟨bs, hm, hb⟩
    obtain ⟨hl, hall⟩ := (mapM_numeric_iff bs xs).mp hm
    exact ⟨bs, hl, fun i h₁ h₂ => by rw [decode_u8Chunk]; exact hall i h₁ h₂, hb⟩

/-- A range of `u8` values is the list of their data bytes. -/
theorem pointsToRange_u8_iff (p : RawPtr U8) (bptr : BasePtr) (xs : List U8) (d : Nat)
    (h : Fragment) :
    pointsToRange (Pointee.repr (T := U8)) p bptr (listVec xs) d h ↔
      block (Pointee.repr (T := U8)) p bptr ((xs.map Byte.data).map (Cell.shared d)) h := by
  have henc : ∀ x b, (Pointee.repr (T := U8)).encode x (u8Chunk b) ↔ b = Byte.data x := by
    intro x b
    rw [(Pointee.Plain.isPlain (T := U8)).encode_iff, Pointee.toBytes_u8]
    show [b] = [Byte.data x] ↔ _
    simp
  rw [pointsToRange_eq_rangeWith, rangeWith_u8_iff]
  constructor
  · rintro ⟨bs, hl, hv, hb⟩
    have : bs = xs.map Byte.data := by
      apply List.ext_getElem (by simp [hl])
      intro i h₁ h₂
      simpa using (henc _ _).mp (hv i h₁ (by omega))
    rwa [← this]
  · intro hb
    exact ⟨xs.map Byte.data, by simp, fun i h₁ h₂ => (henc _ _).mpr (by simp), hb⟩

end Bytes

/-! ## Typed views of byte ranges -/

namespace RawPtr

/-- A readable value of a plain type (for instance the exposure of a `u64` by `from_ref`, which
gives `q.readable 1 [v]`) is readable, through `q.cast U8`, as its little-endian bytes. -/
theorem readable_cast_bytes {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U) (d : Nat)
    (v : U) : q.readable d [v] ⊢ (q.cast U8).readable d (toBytes v) := by
  rintro h ⟨bptr, a, ha, hsub⟩
  rw [Bytes.readableRange_eq_rangeWith] at ha
  obtain ⟨bytes, hdec, hb⟩ := Bytes.rangeWith_singleton.mp ha
  obtain ⟨bs, hm, hb'⟩ := Bytes.readable_bytes Pointee.Plain.isPlain q bptr v d a ⟨bytes, hdec, hb⟩
  exact ⟨bptr, a, (Bytes.readableRange_u8_iff _ _ _ _ _).mpr ⟨bs, hm, hb'⟩, hsub⟩

/-- Readable bytes, at an address aligned for `U`, are a readable value of `U` through
`p.cast U`. -/
theorem readable_bytes_cast {U : Type} [Pointee U] [Pointee.Plain U] (p : RawPtr U8) (d : Nat)
    (v : U) (ha : (Pointee.repr (T := U)).align.val ∣ p.address.val) :
    p.readable d (toBytes v) ⊢ (p.cast U).readable d [v] := by
  rintro h ⟨bptr, a, hr, hsub⟩
  obtain ⟨bs, hm, hb⟩ := (Bytes.readableRange_u8_iff _ _ _ _ _).mp hr
  obtain ⟨bytes, hdec, hb'⟩ :=
    Bytes.bytes_readable Pointee.Plain.isPlain p bptr v d a bs hm ha hb
  refine ⟨bptr, a, ?_, hsub⟩
  rw [Bytes.readableRange_eq_rangeWith]
  exact Bytes.rangeWith_singleton.mpr ⟨bytes, hdec, hb'⟩

/-- `copy_nonoverlapping(q.cast::<u8>(), dst.add(i), count)` from a readable value of a plain type
(for instance a `u64` exposed by `ptr::from_ref`): copies the first `count` little-endian bytes of
the value, and keeps the typed view of the source (`readable_cast_bytes`, `readable_bytes_cast`,
with the alignment of `q`). -/
theorem _root_.Aeneas.Std.core.ptr.copy_nonoverlapping.spec_readable_cast {U : Type} [Pointee U]
    [Pointee.Plain U] [Pointee.Sized U] (q : RawPtr U) (dst : RawPtr U8) (d : Nat) (v : U)
    (ys : List (MaybeUninit U8)) (i : Nat) (count : Usize)
    (hj : count.val ≤ (Pointee.repr (T := U)).size) (hi : i + count.val ≤ ys.length)
    (hys : 0 < ys.length) (hfits : (count.val : Int) ≤ IScalar.cMax .Isize) :
    ⦃ q.readable d [v] ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (q.cast U8) (dst.elem i) count
    ⦃ q.readable d [v] ∗ dst ↦?* (ys.take i ++
        ((toBytes v).take count.val).map (fun x => ⟨some x⟩) ++ ys.drop (i + count.val)) ⦄ := by
  refine ispec_conseq (P' := ⌜(Pointee.repr (T := U)).align.val ∣ q.address.val⌝ ∗
    (q.readable d [v] ∗ dst ↦?* ys)) ?_
    (entails_trans (sep_mono (RawPtr.readable_aligned q d [v]) (entails_refl _))
      (entails_of_eq (sep_assoc_eq _ _ _))) (fun _ => entails_refl _)
  refine ispec_ipure.mpr fun hal => ?_
  have hlen : (toBytes v).length = (Pointee.repr (T := U)).size := Pointee.length_toBytes v
  have hc := core.ptr.copy_nonoverlapping.spec_readable_src_head (q.cast U8) dst d (toBytes v) ys
    i count (by omega) hi (by have := Pointee.Sized.pos (T := U); omega) hys
    (by rw [Pointee.size_u8]; simpa using hfits)
  refine ispec_conseq hc (sep_mono (readable_cast_bytes q d v) (entails_refl _))
    (fun _ => sep_mono ?_ (entails_refl _))
  simpa using readable_bytes_cast (q.cast U8) d v (by simpa using hal)

/-- An owned value of a plain type is, through `q.cast U8`, the range of its bytes. -/
theorem pointsTo_cast_bytes {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U) (v : U) :
    q ↦ v ⊢ (q.cast U8) ↦* toBytes v := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, (Bytes.pointsToRange_u8_iff _ _ _ _ _).mpr
    (Bytes.pointsTo_bytes Pointee.Plain.isPlain q bptr v 0 a ha), hsub⟩

/-- The range of the bytes of a value of a plain type, at an address aligned for `U`, is the owned
value through `p.cast U`. -/
theorem bytes_pointsTo_cast {U : Type} [Pointee U] [Pointee.Plain U] (p : RawPtr U8) (v : U)
    (ha : (Pointee.repr (T := U)).align.val ∣ p.address.val) :
    p ↦* toBytes v ⊢ (p.cast U) ↦ v := by
  rintro h ⟨bptr, a, hr, hsub⟩
  exact ⟨bptr, a, Bytes.bytes_pointsTo Pointee.Plain.isPlain p bptr v 0 a ha
    ((Bytes.pointsToRange_u8_iff _ _ _ _ _).mp hr), hsub⟩

/-- An owned value of a plain type, viewed as possibly uninitialized bytes. -/
theorem pointsTo_cast_uninitRange {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U)
    (v : U) : q ↦ v ⊢ (q.cast U8) ↦?* (toBytes v).map (fun x => ⟨some x⟩) :=
  entails_trans (pointsTo_cast_bytes q v) (range_uninitRange _ _)

/-- Initialized bytes, at an address aligned for `U`, are a readable value of `U`. -/
theorem uninitRange_bytes_readable {U : Type} [Pointee U] [Pointee.Plain U] (p : RawPtr U8)
    (v : U) (ha : (Pointee.repr (T := U)).align.val ∣ p.address.val) :
    p ↦?* (toBytes v).map (fun x => ⟨some x⟩) ⊢ (p.cast U).readable 0 [v] := by
  rw [← readable_eq_uninitRange]
  exact readable_bytes_cast p 0 v ha

end RawPtr

/-! ## Unaligned accesses through a cast of a byte buffer -/

namespace Bytes

/-- An unaligned write of a value of a plain type over owned byte cells, whatever they were. -/
theorem writeCast.local {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U8) (bptr : BasePtr)
    (mid : List (MaybeUninit U8)) (v : U) (hlen : mid.length = (Pointee.repr (T := U)).size)
    (hsize : 0 < (Pointee.repr (T := U)).size) :
    LocalOp (uninitRange (Pointee.repr (T := U8)) q bptr (listVec mid))
      (State.write (Pointee.repr (T := U)).unaligned (q.cast U) v)
      (fun _ => uninitRange (Pointee.repr (T := U8)) q bptr
        (listVec ((toBytes v).map (fun x => ⟨some x⟩)))) := by
  intro h F s hp hd hm hi
  obtain ⟨bs, hl, _, hb⟩ := (rangeWith_u8_iff _ q bptr mid 0 h).mp hp
  let old : Vector Byte (Pointee.repr (T := U)).unaligned.size :=
    ⟨bs.toArray, by show bs.toArray.size = (Pointee.repr (T := U)).size; simp [hl, hlen]⟩
  have hb' : block (Pointee.repr (T := U)).unaligned (q.cast U) bptr
      (old.map (Cell.shared 0)).toList h := by
    rw [Vector.toList_map]
    exact block_cast _ _ q bptr _ h (Nat.one_dvd _) hb
  obtain ⟨hE, hPost⟩ := write.spec _ (q.cast U) bptr old v
    (Pointee.Plain.isPlain.unaligned.noPointers v) hsize h F s hb' hd hm hi
  refine ⟨hE, fun x s' hx => ?_⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := hPost x s' hx
  refine ⟨h', hd', hm', hi', ?_⟩
  have hq' := pointsTo_bytes Pointee.Plain.isPlain.unaligned (q.cast U) bptr v 0 h' hq
  simp only [RawPtr.cast_cast, RawPtr.cast_self] at hq'
  refine (rangeWith_u8_iff _ q bptr _ 0 h').mpr ⟨(toBytes v).map Byte.data, by simp,
    fun i h₁ h₂ => ?_, hq'⟩
  simp [decode_u8Chunk, Byte.numeric]

theorem writeCast.auth {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U8) (bptr : BasePtr)
    (mid : List (MaybeUninit U8)) (v : U) (hlen : mid.length = (Pointee.repr (T := U)).size)
    (hsize : 0 < (Pointee.repr (T := U)).size) :
    WP.Bytes.AuthPres (uninitRange (Pointee.repr (T := U8)) q bptr (listVec mid))
      (State.write (Pointee.repr (T := U)).unaligned (q.cast U) v)
      (fun _ => uninitRange (Pointee.repr (T := U8)) q bptr
        (listVec ((toBytes v).map (fun x => ⟨some x⟩)))) := by
  refine AuthPres.of_step (fun _ _ h => NoOwned_rangeWith h) ?_
  rintro h F s hp hd hm hi x s' hx a' _ _ _ _ base hEx _
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨bs, hl, _, hb⟩ := (rangeWith_u8_iff _ q bptr mid 0 h).mp hp
  let old : Vector Byte (Pointee.repr (T := U)).unaligned.size :=
    ⟨bs.toArray, by show bs.toArray.size = (Pointee.repr (T := U)).size; simp [hl, hlen]⟩
  have hb' : block (Pointee.repr (T := U)).unaligned (q.cast U) bptr
      (old.map (Cell.shared 0)).toList h := by
    rw [Vector.toList_map]
    exact block_cast _ _ q bptr _ h (Nat.one_dvd _) hb
  obtain ⟨_, _, hcells⟩ := hb'
  rw [hcells] at localMatch
  exact write_step (repr := (Pointee.repr (T := U)).unaligned) hsize localMatch hx base hEx

/-- An unaligned read of a value of a plain type from readable byte cells. -/
theorem readCast.local {U : Type} [Pointee U] [Pointee.Plain U] (q : RawPtr U8) (bptr : BasePtr)
    (v : U) (d : Nat) (hsize : 0 < (Pointee.repr (T := U)).size) :
    LocalOp (readableRange (Pointee.repr (T := U8)) q bptr (listVec (toBytes v)) d)
      (State.read (Pointee.repr (T := U)).unaligned (q.cast U))
      (fun r h => r = v ∧ readableRange (Pointee.repr (T := U8)) q bptr (listVec (toBytes v)) d h) := by
  intro h F s hp hd hm hi
  obtain ⟨bs, hmm, hb⟩ := (readableRange_u8_iff _ _ _ _ _).mp hp
  have hr := bytes_readable Pointee.Plain.isPlain.unaligned q bptr v d h bs hmm (Nat.one_dvd _) hb
  have hread := read_of_readable (repr := (Pointee.repr (T := U)).unaligned) hsize hr ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨v, s, hread, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hread), hp⟩

end Bytes

/-- `q.cast::<U>().write_unaligned(v)` over `size_of::<U>()` owned byte cells, whatever they were:
they become the little-endian bytes of `v`. -/
theorem MutRawPtr.write_unaligned.spec_cast_bytes {U : Type} [Pointee U] [Pointee.Plain U]
    [Pointee.Sized U] (q : MutRawPtr U8) (mid : List (MaybeUninit U8)) (v : U)
    (hlen : mid.length = (Pointee.repr (T := U)).size) :
    ⦃ q ↦?* mid ⦄ MutRawPtr.write_unaligned (q.cast U) v
      ⦃ q ↦?* (toBytes v).map (fun x => ⟨some x⟩) ⦄ := by
  unfold MutRawPtr.write_unaligned
  exact ispec_checked_local
    (fun bptr => Bytes.writeCast.local q bptr mid v hlen Pointee.Sized.pos)
    (fun bptr => Bytes.writeCast.auth q bptr mid v hlen Pointee.Sized.pos)

/-- `q.cast::<U>().read_unaligned()` from readable bytes which are the bytes of `v`. -/
theorem RawPtr.read_unaligned.spec_cast_readable {U : Type} [Pointee U] [Pointee.Plain U]
    [Pointee.Sized U] (q : RawPtr U8) (d : Nat) (v : U) :
    ⦃ q.readable d (toBytes v) ⦄ RawPtr.read_unaligned (q.cast U)
      ⦃ r => ⌜r = v⌝ ∗ q.readable d (toBytes v) ⦄ := by
  unfold RawPtr.read_unaligned
  exact ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.readCast.local q bptr v d Pointee.Sized.pos)
      (fun _ => Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.readableRange h.2)
        (fun _ _ _ h => h.2)))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

/-- `q.cast::<U>().read_unaligned()` from initialized bytes which are the bytes of `v`. -/
theorem RawPtr.read_unaligned.spec_cast_bytes {U : Type} [Pointee U] [Pointee.Plain U]
    [Pointee.Sized U] (q : RawPtr U8) (v : U) :
    ⦃ q ↦?* (toBytes v).map (fun x => ⟨some x⟩) ⦄ RawPtr.read_unaligned (q.cast U)
      ⦃ r => ⌜r = v⌝ ∗ q ↦?* (toBytes v).map (fun x => ⟨some x⟩) ⦄ := by
  rw [← readable_eq_uninitRange]
  exact RawPtr.read_unaligned.spec_cast_readable q 0 v

/-! ## Accesses within a larger `↦?*` range -/

/-- Lifts a specification of an operation on the sub-range `[i, i + n)` of a range to the whole
range (splitting it and merging it back). -/
theorem ispec_uninitRange_focus {T α : Type} [Pointee T] [Pointee.Sized T] {m : Result α}
    (p : RawPtr T) (ys : List (MaybeUninit T)) (i n : Nat) (hi : i + n ≤ ys.length)
    (P : α → Prop) (mid : α → List (MaybeUninit T)) (hmid : ∀ x, (mid x).length = n)
    (hspec : ispec ((p.elem i) ↦?* (ys.drop i).take n) m
      (fun x => ⌜P x⌝ ∗ (p.elem i) ↦?* mid x)) :
    ispec (p ↦?* ys) m (fun x => ⌜P x⌝ ∗ p ↦?* (ys.take i ++ mid x ++ ys.drop (i + n))) := by
  have hA : (ys.take i).length = i := by simp; omega
  have hB : ((ys.drop i).take n).length = n := by simp; omega
  have hys : ys = ys.take i ++ ((ys.drop i).take n ++ ys.drop (i + n)) := by
    conv_lhs => rw [← List.take_append_drop i ys, ← List.take_append_drop n (ys.drop i)]
    rw [List.drop_drop]
  have framed := ispec_frame_left (ispec_frame hspec (((p.elem i).elem n) ↦?* ys.drop (i + n)))
    (p ↦?* ys.take i)
  refine ispec_realEntails_pre ?_ (ispec_realEntails_post (ispec_conseq framed (entails_refl _)
    (Q := fun x => ⌜P x⌝ ∗ (p ↦?* ys.take i ∗ ((p.elem i) ↦?* mid x ∗
      ((p.elem i).elem n) ↦?* ys.drop (i + n)))) ?_) ?_)
  · have h1 := uninitRange_split_real p (ys.take i) ((ys.drop i).take n ++ ys.drop (i + n))
    rw [← hys, hA] at h1
    have h2 := uninitRange_split_real (p.elem i) ((ys.drop i).take n) (ys.drop (i + n))
    rw [hB] at h2
    exact h1.trans (h2.frame_left _)
  · intro x
    show (p ↦?* ys.take i ∗ ((⌜P x⌝ ∗ (p.elem i) ↦?* mid x) ∗
      ((p.elem i).elem n) ↦?* ys.drop (i + n))) ⊢ _
    apply entails_of_eq
    rw [sep_assoc_eq, ← sep_assoc_eq (p ↦?* ys.take i), sep_comm_eq (p ↦?* ys.take i),
      sep_assoc_eq]
  · intro x
    have h2 := uninitRange_merge (p.elem i) (mid x) (ys.drop (i + n))
    rw [hmid] at h2
    have h1 := uninitRange_merge p (ys.take i) (mid x ++ ys.drop (i + n))
    rw [hA] at h1
    rw [List.append_assoc]
    exact ((h2.frame_left _).trans h1).frame_left _

/-- `p.add(i).cast::<U>().write_unaligned(v)` into a byte buffer: the `size_of::<U>()` bytes from
`i` on become the little-endian bytes of `v`, whatever they were. No alignment is needed. -/
@[step]
theorem MutRawPtr.write_unaligned.spec_cast {U : Type} [Pointee U] [Pointee.Plain U]
    [Pointee.Sized U] (p : MutRawPtr U8) (ys : List (MaybeUninit U8)) (i : Nat) (v : U)
    (hi : i + (Pointee.repr (T := U)).size ≤ ys.length) :
    ⦃ p ↦?* ys ⦄ MutRawPtr.write_unaligned ((p.elem i).cast U) v
      ⦃ p ↦?* (ys.take i ++ (toBytes v).map (fun x => ⟨some x⟩) ++
        ys.drop (i + (Pointee.repr (T := U)).size)) ⦄ := by
  have h := ispec_uninitRange_focus (m := MutRawPtr.write_unaligned ((p.elem i).cast U) v)
    p ys i _ hi (fun _ => True) (fun _ => (toBytes v).map (fun x => ⟨some x⟩)) (by simp)
    (ispec_conseq (MutRawPtr.write_unaligned.spec_cast_bytes (p.elem i) _ v (by simp; omega))
      (entails_refl _) (fun _ h hq => (sep_pure_l _ _ h).mpr ⟨trivial, hq⟩))
  exact ispec_conseq h (entails_refl _) (fun _ h hq => ((sep_pure_l _ _ h).mp hq).2)

/-- `p.add(i).cast::<U>().read_unaligned()` from a byte buffer whose `size_of::<U>()` bytes from
`i` on are initialized to the little-endian bytes of `v`. No alignment is needed. -/
@[step]
theorem RawPtr.read_unaligned.spec_cast {U : Type} [Pointee U] [Pointee.Plain U]
    [Pointee.Sized U] (p : RawPtr U8) (ys : List (MaybeUninit U8)) (i : Nat) (v : U)
    (hv : (ys.drop i).take (Pointee.repr (T := U)).size = (toBytes v).map (fun x => ⟨some x⟩)) :
    ⦃ p ↦?* ys ⦄ RawPtr.read_unaligned ((p.elem i).cast U) ⦃ r => ⌜r = v⌝ ∗ p ↦?* ys ⦄ := by
  have hi : i + (Pointee.repr (T := U)).size ≤ ys.length := by
    have := congrArg List.length hv
    have hpos := Pointee.Sized.pos (T := U)
    simp at this
    omega
  have h := ispec_uninitRange_focus (m := RawPtr.read_unaligned ((p.elem i).cast U))
    p ys i _ hi (fun r => r = v) (fun _ => (ys.drop i).take (Pointee.repr (T := U)).size)
    (by simp; omega)
    (by rw [hv]; exact RawPtr.read_unaligned.spec_cast_bytes (p.elem i) v)
  have hys : ys.take i ++ (ys.drop i).take (Pointee.repr (T := U)).size ++
      ys.drop (i + (Pointee.repr (T := U)).size) = ys := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  simpa only [hys] using h

/-! ## `size_of` and `align_of` -/

theorem usize_max_eq : Usize.max = 2 ^ System.Platform.numBits - 1 := by
  simp [Usize.max, Usize.numBits]

theorem le_usize_max_of_le {n : Nat} (h : n ≤ 2 ^ 32 - 1) : n ≤ Usize.max := by
  rw [usize_max_eq]
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

theorem usize_ofNat_val {n : Nat} (h : n ≤ Usize.max) :
    (⟨BitVec.ofNat _ n⟩ : Usize).val = n := by
  rw [usize_max_eq] at h
  show (BitVec.ofNat _ n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [UScalarTy.Usize_numBits_eq]
  have := Nat.one_le_two_pow (n := System.Platform.numBits)
  omega

theorem numBits_div_eight_le_usize_max (ty : UScalarTy) : ty.numBits / 8 ≤ Usize.max := by
  apply le_usize_max_of_le
  cases ty <;> simp only [UScalarTy.numBits] <;> try decide
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> decide

theorem inumBits_div_eight_le_usize_max (ty : IScalarTy) : ty.numBits / 8 ≤ Usize.max := by
  apply le_usize_max_of_le
  cases ty <;> simp only [IScalarTy.numBits] <;> try decide
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> decide

/-- `size_of::<T>()` is the size of the representation of `T`. -/
theorem core.mem.size_of.spec (T : Type) [Pointee T]
    (h : (Pointee.repr (T := T)).size ≤ Usize.max) :
    core.mem.size_of T ⦃ r => r.val = (Pointee.repr (T := T)).size ⦄ := by
  simp only [core.mem.size_of, h, dite_true, spec_ok]
  exact usize_ofNat_val h

/-- `align_of::<T>()` is the alignment of the representation of `T`. -/
theorem core.mem.align_of.spec (T : Type) [Pointee T]
    (h : (Pointee.repr (T := T)).align.val ≤ Usize.max) :
    core.mem.align_of T ⦃ r => r.val = (Pointee.repr (T := T)).align.val ⦄ := by
  simp only [core.mem.align_of, h, dite_true, spec_ok]
  exact usize_ofNat_val h

/-- `size_of::<u32>() = 4`, ... -/
@[step]
theorem core.mem.size_of.spec_uscalar (ty : UScalarTy) :
    core.mem.size_of (UScalar ty) ⦃ r => r.val = ty.numBits / 8 ⦄ :=
  core.mem.size_of.spec _ (numBits_div_eight_le_usize_max ty)

@[step]
theorem core.mem.size_of.spec_iscalar (ty : IScalarTy) :
    core.mem.size_of (IScalar ty) ⦃ r => r.val = ty.numBits / 8 ⦄ :=
  core.mem.size_of.spec _ (inumBits_div_eight_le_usize_max ty)

/-- `size_of::<[T; N]>() = N * size_of::<T>()`. -/
@[step]
theorem core.mem.size_of.spec_array (T : Type) [Pointee T] (N : Usize)
    (h : N.val * (Pointee.repr (T := T)).size ≤ Usize.max) :
    core.mem.size_of (Array T N) ⦃ r => r.val = N.val * (Pointee.repr (T := T)).size ⦄ := by
  have := core.mem.size_of.spec (Array T N) (by rw [Pointee.size_array]; exact h)
  rwa [Pointee.size_array] at this

@[step]
theorem core.mem.align_of.spec_uscalar (ty : UScalarTy) :
    core.mem.align_of (UScalar ty) ⦃ r => r.val = ty.numBits / 8 ⦄ :=
  core.mem.align_of.spec _ (numBits_div_eight_le_usize_max ty)

@[step]
theorem core.mem.align_of.spec_iscalar (ty : IScalarTy) :
    core.mem.align_of (IScalar ty) ⦃ r => r.val = ty.numBits / 8 ⦄ :=
  core.mem.align_of.spec _ (inumBits_div_eight_le_usize_max ty)

/-- `align_of::<[T; N]>() = align_of::<T>()` (for `0 < N`). -/
@[step]
theorem core.mem.align_of.spec_array (T : Type) [Pointee T] (N : Usize) (hN : 0 < N.val)
    (h : (Pointee.repr (T := T)).align.val ≤ Usize.max) :
    core.mem.align_of (Array T N) ⦃ r => r.val = (Pointee.repr (T := T)).align.val ⦄ := by
  have := core.mem.align_of.spec (Array T N) (by rw [Pointee.align_array T N hN]; exact h)
  rwa [Pointee.align_array T N hN] at this

end Aeneas.Std
