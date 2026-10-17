module
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.GaloisConnection

@[expose] public section

namespace Aeneas
namespace Layout
namespace ReprC

/-! ## Part 2: Shallow `#[repr(C)]` Tuple / Struct Layout (with Optional Packing) -/

/-- Effective alignment when capped by an optional `#[repr(packed(P))]` bound. -/
@[simp, grind =]
def effAlign (max_align : Option { a : Nat // a.isPowerOfTwo }) (a : Nat) : Nat :=
  match max_align with
  | none => a
  | some ⟨p, _⟩ => min a p

@[simp, grind ←]
lemma effAlign_isPowerOfTwo (max_align : Option { a : Nat // a.isPowerOfTwo })
    {a : Nat} (ha : a.isPowerOfTwo) : (effAlign max_align a).isPowerOfTwo := by
  cases max_align with
  | none => exact ha
  | some p =>
    by_cases h : a ≤ p.val <;> simp [effAlign] <;> grind

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`,
    starting at initial offset `init_off`. -/
def tupleCursor {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) (init_off : Nat := 0) :
    (k : Nat) → k ≤ n → Nat
  | 0, _ => init_off
  | k + 1, hk =>
    alignUp (tupleCursor fsize falign init_off k (Nat.le_of_succ_le hk)) (falign k hk) + fsize k hk

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `falign i hi`. -/
@[grind =]
def tupleFieldOffset {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) (init_off : Nat := 0)
    (i : Nat) (hi : i < n) : Nat :=
  alignUp (tupleCursor fsize falign init_off i (by omega)) (falign i hi)

@[grind ←] private lemma tupleCursor_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsize falign init_off k1 hk1 ≤ tupleCursor fsize falign init_off k2 hk2
  | 0, 0, _, _, _ => Nat.le_refl _
  | _ + 1, 0, _, _, h => nomatch h
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have := tupleCursor_mono fsize falign init_off h_pos hk1 (by omega) h
      simp [tupleCursor]; grind
    · rfl

grind_pattern tupleCursor_mono => tupleCursor fsize falign init_off k1 _, tupleCursor fsize falign init_off k2 _

private lemma init_off_le_tupleCursor {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (k : Nat) (hk : k ≤ n) :
    init_off ≤ tupleCursor fsize falign init_off k hk :=
  tupleCursor_mono fsize falign init_off h_pos (Nat.zero_le n) hk (Nat.zero_le k)

grind_pattern init_off_le_tupleCursor => tupleCursor fsize falign init_off k hk

private lemma init_off_le_tupleFieldOffset {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (i : Nat) (hi : i < n) :
    init_off ≤ tupleFieldOffset fsize falign init_off i hi := by
  grind

grind_pattern init_off_le_tupleFieldOffset => tupleFieldOffset fsize falign init_off i hi

private lemma tupleFieldOffset_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a < b) :
    tupleFieldOffset fsize falign init_off a ha + fsize a ha ≤ tupleFieldOffset fsize falign init_off b hb := by
  have h1 : tupleFieldOffset fsize falign init_off a ha + fsize a ha = tupleCursor fsize falign init_off (a + 1) ha := rfl
  grind

grind_pattern tupleFieldOffset_mono => tupleFieldOffset fsize falign init_off a ha, tupleFieldOffset fsize falign init_off b hb

private lemma tupleFieldOffset_le_end {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat) (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (i : Nat) (hi : i < n) :
    tupleFieldOffset fsize falign init_off i hi + fsize i hi ≤ tupleCursor fsize falign init_off n (Nat.le_refl n) :=
  tupleCursor_mono fsize falign init_off h_pos hi (Nat.le_refl n) hi

grind_pattern tupleFieldOffset_le_end => tupleFieldOffset fsize falign init_off i hi

/-- Total `SizeAndAlign` of a `#[repr(C)]` tuple/struct with field sizes `fsize`,
    effective field alignments `falign`, and initial offset `init_off`. -/
@[grind =]
def tupleSizeAndAlign {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat := 0) (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) : SizeAndAlign :=
  let A := natMax n falign 1
  let sz := alignUp (tupleCursor fsize falign init_off n (Nat.le_refl _)) A
  ⟨sz, A, by grind, by grind⟩

@[grind ←]
lemma tupleValid {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (init_off : Nat := 0) (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) :
    TupleValid n (tupleFieldOffset fsize falign init_off) fsize (tupleSizeAndAlign fsize falign init_off h_align) := by
  grind

/-- All fields of a tuple layout are placed at byte offset `≥ min_off`
    (leaving `[0 ..< min_off)` untouched as prefix padding). -/
def TupleMinOffset (min_off : Nat) : {t : MType} → Layout t → Prop
  | .tuple ts, .tuple vfo _ _ => ∀ j (hj : j < ts.length), min_off ≤ vfo j hj
  | _, _ => True

@[simp, grind =]
lemma tupleMinOffset_tuple (min_off : Nat) {ts : List MType}
    (vfo : (idx : Nat) → idx < ts.length → Nat)
    (vfl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (sa : SizeAndAlign) :
    TupleMinOffset min_off (.tuple vfo vfl sa) = (∀ j (hj : j < ts.length), min_off ≤ vfo j hj) := rfl

@[simp, grind .]
lemma tupleMinOffset_zero {t : MType} (cl : Layout t) : TupleMinOffset 0 cl := by
  cases cl <;> simp [TupleMinOffset]

/-- Shallow `#[repr(C)]` layout for a tuple/struct given arbitrary layouts for its fields,
    with an optional `max_align` cap for `#[repr(C, packed(N))]` and an optional initial
    cursor `init_off` (used e.g. for `#[repr(primitive)]` enum variants after the tag). -/
@[grind =]
noncomputable def mkTuple (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0) :
    Layout (.tuple ts) :=
  let fsize : (idx : Nat) → idx < ts.length → Nat := λ idx h ↦ (fl idx h).size
  let falign : (idx : Nat) → idx < ts.length → Nat :=
    λ idx h ↦ effAlign max_align (fl idx h).size_and_align.align
  .tuple (tupleFieldOffset fsize falign init_off) fl (tupleSizeAndAlign fsize falign init_off (by grind))

@[grind ←]
lemma mkTuple_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts fl max_align init_off).Valid :=
  .tuple ts _ fl _ h_fl (tupleValid _ _ init_off _)

@[grind ←]
lemma mkTuple_reasonablyAligned (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (init_off : Nat := 0) :
    (mkTuple ts fl none init_off).ReasonablyAligned :=
  .tuple ts _ fl _ (by grind)

@[simp, grind ←]
lemma mkTuple_minOffset (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (init_off : Nat := 0) :
    TupleMinOffset init_off (mkTuple ts fl max_align init_off) := by
  grind

-- having a packed(n) where n is greater than the existing alignment has no effect
@[grind =]
lemma mkTuple_large_packed_nop ts fl (a : { a : Nat // a.isPowerOfTwo }) (init_off : Nat := 0)
  (hge : a.val ≥ (mkTuple ts fl .none init_off).size_and_align.align) :
  mkTuple ts fl (.some a) init_off = mkTuple ts fl .none init_off := by grind

@[grind ←]
lemma mkTuple_packed_bounds_align ts fl (a : { a : Nat // a.isPowerOfTwo }) (init_off : Nat := 0) :
  (mkTuple ts fl (max_align := .some a) init_off).size_and_align.align ≤ ↑a := by
  grind [lub_natMax]

private lemma tupleSizeAndAlign_size_eq_natMax : ∀ {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo),
    let sa := tupleSizeAndAlign fsize falign 0 h_align
    sa.size = natMax n (λ x hx ↦ alignUp (tupleFieldOffset fsize falign 0 x hx + fsize x hx) sa.align) 0
  | 0, _, _, _ => by simp [tupleSizeAndAlign, tupleCursor, natMax]
  | m + 1, fsize, falign, h_align => by
    intro sa
    apply Nat.le_antisymm
    · trans; swap
      apply le_natMax (i := m)
      grind
      trivial
    · apply lub_natMax; grind
      grind

@[grind ←]
lemma mkTuple_packed (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (a : { a : Nat // a.isPowerOfTwo }) :
    (mkTuple ts fl (.some a) 0).Packed a.val := by
  refine .tuple ts _ fl id _ a.property (mkTuple_packed_bounds_align ts fl a 0) Function.bijective_id ?_ ?_
    (tupleSizeAndAlign_size_eq_natMax _ _ _) ?_
  · intro i hle
    simp [tupleFieldOffset, tupleCursor, effAlign]
    grind
  · intro hl
    simp [tupleFieldOffset, tupleCursor]
  · grind

grind_pattern mkTuple_packed => mkTuple ts fl (.some a) 0

/-! ## Part 3: Shallow `#[repr(C)]` and `#[repr(primitive)]` Enum Layouts -/

/-- Shifts a tuple variant's field offsets right by `payload_off` and sets its `SizeAndAlign` to `sa`,
    leaving prefix bytes `[0 ..< min_off + payload_off)` as padding for the discriminant tag. -/
def padVariantLayout : {t : MType} → Layout t → Nat → SizeAndAlign → Layout t
  | .tuple _, .tuple vfo vfl _, payload_off, sa =>
      .tuple (λ j hj ↦ payload_off + vfo j hj) vfl sa
  | _, l, _, _ => l

/-- Shared core for `#[repr(C)]` (`mkEnum`) and `#[repr(primitive)]` (`mkEnumPrimitive`) enum layouts.
    - When `shift_payload = true` (`#[repr(C)]` / `#[repr(C, Int)]`), variants are shifted by `alignUp tagTy.size A`.
    - When `shift_payload = false` (`#[repr(Int)]`), variants already place their fields at `≥ tagTy.size`
      (e.g. via `mkTuple ts fl max_align tagTy.size`), so `payload_off = 0` and only their outer `SizeAndAlign` is padded to `sa`. -/
noncomputable def mkEnumCore (tagTy : IUScalarTy) (shift_payload : Bool) (vs : List MType)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := if shift_payload then alignUp tagTy.size A else 0
  let min_sz := if shift_payload then 0 else tagTy.size
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) min_sz
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  .enum vt vl discr sa

/-- `#[repr(C)]` (and `#[repr(C, Int)]`) layout for an enum given layouts for its tuple variants. -/
noncomputable def mkEnum (tagTy : IUScalarTy := .unsigned .Usize) (vs : List MType)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  mkEnumCore tagTy true vs cl

/-- `#[repr(Int)]` (`#[repr(primitive)]`, e.g. `#[repr(u8)]`, `#[repr(i8)]`) layout for an enum,
    given tuple variant layouts whose fields have already been laid out after the tag
    (e.g. via `mkTuple ts fl max_align tagTy.size`). -/
noncomputable def mkEnumPrimitive (tagTy : IUScalarTy) (vs : List MType)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  mkEnumCore tagTy false vs cl

private lemma encode_tuple_prefix_uninit {ts : List MType}
    (fo : (idx : Nat) → idx < ts.length → Nat)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (v : MVal) (hv : v.valid_for (.tuple ts)) {j : Nat} (hj : j < sa.size)
    (hoff : ∀ idx (h : idx < ts.length), j < fo idx h) :
    (encode (.tuple fo fl sa) v hv)[j] = .uninit := by
  cases v with
  | int _ | variant _ _ => nomatch hv
  | tuple values => simp only [encode]; rw [Bytes.foldl_write_subslice_getElem_eq] <;> grind

@[simp]
private lemma padVariantLayout_size_and_align {t : MType} (ht : t.isTuple) (cl : Layout t)
    (payload_off : Nat) (sa : SizeAndAlign) :
    (padVariantLayout cl payload_off sa).size_and_align = sa :=
  match t, ht, cl with
  | .int _, h, _ | .enum _, h, _ => nomatch h
  | .tuple _, _, .tuple _ _ _ => rfl

grind_pattern padVariantLayout_size_and_align => padVariantLayout cl payload_off sa

@[simp]
private lemma padVariantLayout_size {t : MType} (ht : t.isTuple) (cl : Layout t)
    (payload_off : Nat) (sa : SizeAndAlign) :
    (padVariantLayout cl payload_off sa).size = sa.size := by
  rw [← size_known, padVariantLayout_size_and_align ht]

private lemma padVariantLayout_spec {t : MType} (ht : t.isTuple) (cl : Layout t) (hcl : cl.Valid)
    (min_off payload_off : Nat) (h_min : TupleMinOffset min_off cl)
    (sa : SizeAndAlign) (h_size : payload_off + cl.size ≤ sa.size) :
    let vl := padVariantLayout cl payload_off sa
    vl.Valid ∧ ∀ (v : MVal) (hv : v.valid_for t) (j : Nat) (hj : j < vl.size),
      j < min_off + payload_off → (encode vl v hv)[j] = .uninit :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _, h, _, _ => nomatch h
  | .tuple ts, _, .tuple _ vfl _, .tuple _ _ _ _ h_vfl_valid h_vtuple =>
    ⟨.tuple ts _ vfl sa h_vfl_valid
      ⟨by intro i1 i2 hi1 hi2 hne n
          have := h_vtuple.fields_disj i1 i2 hi1 hi2 hne (n - payload_off)
          grind,
       by grind⟩,
     λ v hv j hj _ ↦ encode_tuple_prefix_uninit _ vfl sa v hv hj (by grind)⟩

private lemma usize_max_lt_two_pow : Std.Usize.max < 2 ^ (IUScalarTy.unsigned .Usize).numBits := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp [Std.Usize.max, Std.Usize.numBits, IUScalarTy.numBits, Std.UScalarTy.numBits, h]

grind_pattern usize_max_lt_two_pow => Std.Usize.max

@[grind ←]
lemma mkEnumCore_valid (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset (if shift_payload then 0 else tagTy.size) (cl idx h)) :
    (mkEnumCore tagTy shift_payload vs cl).Valid := by
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := if shift_payload then alignUp tagTy.size A else 0
  let min_sz := if shift_payload then 0 else tagTy.size
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) min_sz
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  have hTagBounds : 0 + tagTy.size ≤ sa.size := by grind
  have h_pad := λ (idx : Nat) (h : idx < vs.length) ↦
    padVariantLayout_spec (ht idx h) (cl idx h) (h_cl idx h)
      (if shift_payload then 0 else tagTy.size) payload_off (h_min idx h) sa (by grind)
  refine .enum vs vt vl discr sa (λ idx h ↦ (h_pad idx h).1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind [List.Forall]
  · grind
  -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tagTy.size) ⊆ [0 ..< min_off + payload_off)`, which is `.uninit`.
  · intro idx h_idx v hv payload_bs k hk
    have := (h_pad idx h_idx).2 v hv k (by simp [hk])
    simp [encode_discriminant, vt, payload_bs, vl, hk]
    grind
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx`.
  · intro idx h_idx v hv
    unfold decode_discriminant
    simp [encode_discriminant, vt, Nat.mod_eq_of_lt (by omega : idx < 2 ^ tagTy.numBits), h_idx]
    grind
  -- 3. `discr_tags_le_defined`: if `decode_discriminant bytes discr = some idx`, `bytes[0 ..< tagTy.size)` matches `vt idx`.
  · intro bytes idx h_idx h_dec
    simp only [discr, decode_discriminant, hTagBounds, ↓reduceDIte] at h_dec
    cases h_data : (bytes.subslice_with_length 0 tagTy.size hTagBounds).toData with
    | none => simp [h_data] at h_dec
    | some bytes_data =>
      simp [h_data, apply_ite (decode_discriminant bytes)] at h_dec
      have : Endianness.encode_bitvec tagTy.size (BitVec.ofNat tagTy.numBits idx) = bytes_data := by
        simp [← h_dec.2]
      intro k hk
      simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv_fromBv]
      grind

@[grind ←]
lemma mkEnum_valid (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid) :
    (mkEnum tagTy vs cl).Valid := by apply mkEnumCore_valid <;> grind

@[grind ←]
lemma mkEnumPrimitive_valid (tagTy : IUScalarTy)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid)
    (h_min : ∀ idx (h : idx < vs.length), TupleMinOffset tagTy.size (cl idx h)) :
    (mkEnumPrimitive tagTy vs cl).Valid := by apply mkEnumCore_valid <;> grind

@[grind ←]
private lemma padVariantLayout_reasonablyAligned {t : MType} (ht : t.isTuple) (cl : Layout t)
    (hcl : cl.ReasonablyAligned) (payload_off : Nat) (sa : SizeAndAlign)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa).ReasonablyAligned :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _, h, _, _ => nomatch h
  | .tuple ts, _, .tuple _ vfl _, .tuple _ _ _ _ h_vtuple_aligned =>
    .tuple ts _ vfl sa
      ⟨by grind,
       λ j hj ↦ by
         have : (vfl j hj).size_and_align.align ∣ sa.align := by grind
         grind [Nat.dvd_trans, Nat.dvd_add]⟩

@[grind ←]
lemma mkEnumCore_reasonablyAligned (tagTy : IUScalarTy) (shift_payload : Bool)
    (vs : List MType) (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnumCore tagTy shift_payload vs cl).ReasonablyAligned :=
  .enum vs _ _ _ _ (by grind [Nat.dvd_zero])

@[grind ←]
lemma mkEnum_reasonablyAligned (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnum tagTy vs cl).ReasonablyAligned := by apply mkEnumCore_reasonablyAligned <;> trivial

@[grind ←]
lemma mkEnumPrimitive_reasonablyAligned (tagTy : IUScalarTy)
    (vs : List MType) (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnumPrimitive tagTy vs cl).ReasonablyAligned := by apply mkEnumCore_reasonablyAligned <;> trivial

/-! ## Part 4: Deep `#[repr(C)]` Layout (`mk`) -/

/-- Constructs the "deep `#[repr(C)]`"" layout for an `MType` (which lays out all subthings according to `#[repr(C)]` as well).
    Only `noncomputable` because scalar alignments (`IUScalarTy.size_and_align`) are `noncomputable`. -/
noncomputable def mk : (ty : MType) → Layout ty
  | .int _ => .int
  | .tuple ts => mkTuple ts (λ idx h ↦ mk ts[idx]) none
  | .enum vs => mkEnum (.unsigned .Usize) vs (λ idx h ↦ mk vs[idx])
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem (List.getElem_mem h); omega

theorem mk_valid (ty : MType) [hr : ty.Reasonable] : (mk ty).Valid := by
  induction hr <;> grind [mk, Layout.Valid.int]

theorem mk_reasonablyAligned (ty : MType) [hr : ty.Reasonable] : (mk ty).ReasonablyAligned := by
  induction hr <;> grind [mk, Layout.ReasonablyAligned.int]

end ReprC
end Layout
end Aeneas
