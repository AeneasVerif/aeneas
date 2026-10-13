module
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.GaloisConnection
@[expose] public section

namespace Aeneas
namespace Layout
namespace ReprC

open SizeAndAlign

/-! ## Part 1: Bounded Maximum (`natMax`) -/

def natMax : (n : Nat) → ((i : Nat) → i < n → Nat) → Nat → Nat
  | 0, _, init => init
  | n + 1, f, init => max (natMax n (λ i _ ↦ f i (by omega)) init) (f n (by omega))

@[simp, grind .] lemma init_le_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init, init ≤ natMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, _, init => Nat.le_trans (init_le_natMax n _ init) (Nat.le_max_left _ _)

@[simp] lemma le_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init (i : Nat) (hi : i < n), f i hi ≤ natMax n f init
  | n + 1, f, init, i, hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact Nat.le_trans (le_natMax n (λ k _ ↦ f k (by omega)) init i hlt) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

grind_pattern le_natMax => natMax n f init, i < n


lemma lub_natMax : ∀ n (f : (i : Nat) → i < n → Nat) init z (_ : init ≤ z) (_ : ∀ i, (hi : i < n) → f i hi ≤ z), natMax n f init ≤ z
  | 0, _, _, z, h1, _ => h1
  | n + 1, _, init, z, h1, h2 => by
    apply max_le_iff.mpr
    constructor; apply lub_natMax
    all_goals grind


@[simp, grind .]
lemma natMax_isPowerOfTwo : ∀ n (f : (i : Nat) → i < n → Nat) init,
    init.isPowerOfTwo → (∀ i (hi : i < n), (f i hi).isPowerOfTwo) → (natMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    have := natMax_isPowerOfTwo n (λ i _ ↦ f i (by omega)) init h0 (by grind)
    by_cases h : natMax n (λ i _ ↦ f i (by omega)) init ≤ f n (by omega)
    all_goals (simp [natMax]; grind)

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

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`. -/
def tupleCursor {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, hk =>
    alignUp (tupleCursor fsize falign k (Nat.le_of_succ_le hk)) (falign k hk) + fsize k hk

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `falign i hi`. -/
@[grind =]
def tupleFieldOffset {n : Nat} (fsize falign : (i : Nat) → i < n → Nat) (i : Nat) (hi : i < n) : Nat :=
  alignUp (tupleCursor fsize falign i (by omega)) (falign i hi)

@[grind ←] private lemma tupleCursor_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_pos : ∀ i (hi : i < n), 0 < falign i hi) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsize falign k1 hk1 ≤ tupleCursor fsize falign k2 hk2
  | 0, 0, _, _, _ => Nat.le_refl _
  | _ + 1, 0, _, _, h => nomatch h
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have := tupleCursor_mono fsize falign h_pos hk1 (by omega) h
      simp [tupleCursor]; grind
    · rfl

grind_pattern tupleCursor_mono => tupleCursor fsize falign k1 _, tupleCursor fsize falign k2 _

private lemma tupleFieldOffset_mono {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a < b) :
    tupleFieldOffset fsize falign a ha + fsize a ha ≤ tupleFieldOffset fsize falign b hb := by
  have h1 : tupleFieldOffset fsize falign a ha + fsize a ha = tupleCursor fsize falign (a + 1) ha := rfl
  grind

grind_pattern tupleFieldOffset_mono => tupleFieldOffset fsize falign a ha, tupleFieldOffset fsize falign b hb

private lemma tupleFieldOffset_le_end {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_pos : ∀ i (hi : i < n), 0 < falign i hi)
    (i : Nat) (hi : i < n) :
    tupleFieldOffset fsize falign i hi + fsize i hi ≤ tupleCursor fsize falign n (Nat.le_refl n) :=
  tupleCursor_mono fsize falign h_pos hi (Nat.le_refl n) hi

grind_pattern tupleFieldOffset_le_end => tupleFieldOffset fsize falign i hi

/-- Total `SizeAndAlign` of a `#[repr(C)]` tuple/struct with field sizes `fsize` and effective field alignments `falign`. -/
@[grind =]
def tupleSizeAndAlign {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) : SizeAndAlign :=
  let A := natMax n falign 1
  let sz := alignUp (tupleCursor fsize falign n (Nat.le_refl _)) A
  ⟨sz, A, by grind, by grind⟩

@[grind ←]
lemma tupleValid {n : Nat} (fsize falign : (i : Nat) → i < n → Nat)
    (h_align : ∀ i (hi : i < n), (falign i hi).isPowerOfTwo) :
    TupleValid n (tupleFieldOffset fsize falign) fsize (tupleSizeAndAlign fsize falign h_align) := by
  grind

/-- Shallow `#[repr(C)]` layout for a tuple/struct given arbitrary layouts for its fields,
    with an optional `max_align` cap for `#[repr(C, packed(N))]`. -/
@[grind =]
noncomputable def mkTuple (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none) :
    Layout (.tuple ts) :=
  let fsize : (idx : Nat) → idx < ts.length → Nat := λ idx h ↦ (fl idx h).size
  let falign : (idx : Nat) → idx < ts.length → Nat :=
    λ idx h ↦ effAlign max_align (fl idx h).size_and_align.align
  .tuple (tupleFieldOffset fsize falign) fl (tupleSizeAndAlign fsize falign (by grind))

@[grind ←]
lemma mkTuple_valid (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (max_align : Option { a : Nat // a.isPowerOfTwo } := none)
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts fl max_align).Valid :=
  .tuple ts _ fl _ h_fl (tupleValid _ _ _)

@[grind ←]
lemma mkTuple_reasonablyAligned (ts : List MType)
    (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
    (mkTuple ts fl none).ReasonablyAligned :=
  .tuple ts _ fl _ (by grind)

-- having a packed(n) where n is greater than the existing alignment has no effect
@[grind =]
lemma mkTuple_large_packed_nop ts fl (a : { a : Nat // a.isPowerOfTwo })
  (hge : a.val ≥ (mkTuple ts fl .none).size_and_align.align) :
  mkTuple ts fl (.some a) = mkTuple ts fl .none := by grind

@[grind ←]
lemma mkTuple_packed_bounds_align ts fl (a : { a : Nat // a.isPowerOfTwo }) :
  (mkTuple ts fl (max_align := .some a)).size_and_align.align ≤ ↑a := by
  grind [lub_natMax]

/-! ## Part 3: Shallow `#[repr(C)]` Enum Layout -/

/-- Shifts a tuple variant's field offsets right by `payload_off` and sets its `SizeAndAlign` to `sa`,
    leaving prefix bytes `[0 ..< payload_off)` as padding for the discriminant tag. -/
def padVariantLayout : {t : MType} → Layout t → Nat → SizeAndAlign → Layout t
  | .tuple _, .tuple vfo vfl _, payload_off, sa =>
      .tuple (λ j hj ↦ payload_off + vfo j hj) vfl sa
  | _, l, _, _ => l

/-- `#[repr(C)]` layout for an enum given layouts for its tuple variants. Optional `tagTy` for `#[repr(C, u8)]` and relateds. -/
noncomputable def mkEnum (tagTy : IUScalarTy := .unsigned .Usize) (vs : List MType) (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  .enum vt vl discr sa

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

private lemma padVariantLayout_spec {t : MType} (ht : t.isTuple) (cl : Layout t) (hcl : cl.Valid)
    (payload_off : Nat) (sa : SizeAndAlign) (h_size : payload_off + cl.size ≤ sa.size) :
    let vl := padVariantLayout cl payload_off sa
    vl.Valid ∧ ∀ (v : MVal) (hv : v.valid_for t) (j : Nat) (hj : j < vl.size),
      j < payload_off → (encode vl v hv)[j] = .uninit :=
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
lemma mkEnum_valid (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (h_max : vs.length ≤ 2 ^ tagTy.numBits)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid) :
    (mkEnum tagTy vs cl).Valid := by
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, IUScalar.fromBv (BitVec.ofNat tagTy.numBits idx)⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  have hTagBounds : 0 + tagTy.size ≤ sa.size := by grind
  have h_pad := λ (idx : Nat) (h : idx < vs.length) ↦
    padVariantLayout_spec (ht idx h) (cl idx h) (h_cl idx h) payload_off sa (by grind)
  refine .enum vs vt vl discr sa (λ idx h ↦ (h_pad idx h).1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind [List.Forall]
  · grind
  -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tagTy.size) ⊆ [0 ..< payload_off)`, which is `.uninit`.
  · intro idx h_idx v hv payload_bs k hk
    have := (h_pad idx h_idx).2 v hv k
    simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil]
    grind
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx`.
  · intro idx h_idx v hv
    unfold decode_discriminant
    simp [-IUScalarTy.numBits, encode_discriminant, vt, Nat.mod_eq_of_lt (by omega : idx < 2 ^ tagTy.numBits), h_idx]
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
lemma mkEnum_reasonablyAligned (tagTy : IUScalarTy := .unsigned .Usize)
    (vs : List MType) (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnum tagTy vs cl).ReasonablyAligned :=
  .enum vs _ _ _ _ (by grind)

/-! ## Part 4: Deep `#[repr(C)]` Layout (`mk`) -/

/-- Constructs the deep `#[repr(C)]` layout for an `MType` (assuming all composite types are `#[repr(C)]`).
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
