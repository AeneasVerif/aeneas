module
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.GaloisConnection
@[expose] public section

namespace Aeneas
namespace Layout
namespace ReprC

open SizeAndAlign

/-! ## Part 1: Constructing the `#[repr(C)]` Layout -/

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

@[simp, grind .]
lemma natMax_isPowerOfTwo : ∀ n (f : (i : Nat) → i < n → Nat) init,
    init.isPowerOfTwo → (∀ i (hi : i < n), (f i hi).isPowerOfTwo) → (natMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    have := natMax_isPowerOfTwo n (λ i _ ↦ f i (by omega)) init h0 (by grind)
    have := hf n (by omega)
    by_cases h : natMax n (λ i _ ↦ f i (by omega)) init ≤ f n (by omega)
    all_goals (simp [natMax]; grind)

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`. -/
def tupleCursor {n : Nat} (fsa : (i : Nat) → i < n → SizeAndAlign) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, hk =>
    alignUp (tupleCursor fsa k (Nat.le_of_succ_le hk)) (fsa k hk).align + (fsa k hk).size

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `(fsa i hi).align`. -/
@[grind =]
def tupleFieldOffset {n : Nat} (fsa : (i : Nat) → i < n → SizeAndAlign) (i : Nat) (hi : i < n) : Nat :=
  alignUp (tupleCursor fsa i (by omega)) (fsa i hi).align

/-- `#[repr(C)]` layout for a tuple/struct given layouts for its fields. -/
noncomputable def mkTuple (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
    Layout (.tuple ts) :=
  let fsa : (idx : Nat) → idx < ts.length → SizeAndAlign := λ idx h ↦ (fl idx h).size_and_align
  let A := natMax ts.length (λ i hi ↦ (fsa i hi).align) 1
  let sz := alignUp (tupleCursor fsa ts.length (Nat.le_refl _)) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  .tuple (tupleFieldOffset fsa) fl sa

/-- Shifts a tuple variant's field offsets right by `payload_off` and sets its `SizeAndAlign` to `sa`,
    leaving prefix bytes `[0 ..< payload_off)` as padding for the discriminant tag. -/
def padVariantLayout : {t : MType} → Layout t → Nat → SizeAndAlign → Layout t
  | .tuple _, .tuple vfo vfl _, payload_off, sa =>
      .tuple (λ j hj ↦ payload_off + vfo j hj) vfl sa
  | _, l, _, _ => l

/-- `#[repr(C)]` layout for an enum given layouts for its tuple variants. -/
noncomputable def mkEnum (vs : List MType) (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx⟩⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  .enum vt vl discr sa

/-- Constructs the `#[repr(C)]` layout for an `MType`.
    Only `noncomputable` because scalar alignments (`IUScalarTy.size_and_align`) are `noncomputable`. -/
noncomputable def mk : (ty : MType) → Layout ty
  | .int _ => .int
  | .tuple ts => mkTuple ts (λ idx h ↦ mk ts[idx])
  | .enum vs => mkEnum vs (λ idx h ↦ mk vs[idx])
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem (List.getElem_mem h); omega

/-! ## Part 2: Proving Layout Validity (`Valid`) -/

@[grind ←] private lemma tupleCursor_mono {n : Nat} (fsa : (i : Nat) → i < n → SizeAndAlign) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsa k1 hk1 ≤ tupleCursor fsa k2 hk2
  | 0, 0, _, _, _ => Nat.le_refl _
  | _ + 1, 0, _, _, h => nomatch h
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have := tupleCursor_mono fsa hk1 (by omega) h
      simp [tupleCursor]; grind
    · rfl

grind_pattern tupleCursor_mono => tupleCursor fsa k1 _, tupleCursor fsa k2 _

private lemma tupleFieldOffset_mono {n : Nat} (fsa : (i : Nat) → i < n → SizeAndAlign)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a < b) :
    tupleFieldOffset fsa a ha + (fsa a ha).size ≤ tupleFieldOffset fsa b hb := by
  have h1 : tupleFieldOffset fsa a ha + (fsa a ha).size = tupleCursor fsa (a + 1) ha := rfl
  grind

grind_pattern tupleFieldOffset_mono => tupleFieldOffset fsa a ha, tupleFieldOffset fsa b hb

private lemma tupleFieldOffset_le_end {n : Nat} (fsa : (i : Nat) → i < n → SizeAndAlign)
    (i : Nat) (hi : i < n) :
    tupleFieldOffset fsa i hi + (fsa i hi).size ≤ tupleCursor fsa n (Nat.le_refl n) :=
  tupleCursor_mono fsa hi (Nat.le_refl n) hi

grind_pattern tupleFieldOffset_le_end => tupleFieldOffset fsa i hi

@[grind ←]
lemma mkTuple_valid (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
    (h_fl : ∀ idx (h : idx < ts.length), (fl idx h).Valid) :
    (mkTuple ts fl).Valid :=
  .tuple ts _ fl _ h_fl (by grind)

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
lemma mkEnum_valid (vs : List MType) (h_max : vs.length ≤ Std.Usize.max)
    (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).Valid) :
    (mkEnum vs cl).Valid := by
  let fsa : (idx : Nat) → idx < vs.length → SizeAndAlign := λ idx h ↦ (cl idx h).size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := natMax vs.length (λ i hi ↦ (fsa i hi).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := natMax vs.length (λ i hi ↦ (fsa i hi).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx] := λ idx h ↦ padVariantLayout (cl idx h) payload_off sa
  let vt : (idx : Nat) → idx < vs.length → List TagToWrite := λ idx _ ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx⟩⟩]
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
    simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
    grind
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx`.
  · intro idx h_idx v hv
    unfold decode_discriminant
    simp [encode_discriminant, vt, IUScalar.bv]
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
      simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
      grind

theorem mk_valid (ty : MType) [hr : ty.Reasonable] : (mk ty).Valid := by
  induction hr <;> grind [mk, Layout.Valid.int]

/-! ## Part 3: Proving Reasonable Alignment (`ReasonablyAligned`) -/

@[grind ←]
lemma mkTuple_reasonablyAligned (ts : List MType) (fl : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx]) :
    (mkTuple ts fl).ReasonablyAligned :=
  .tuple ts _ fl _ (by grind)

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
lemma mkEnum_reasonablyAligned (vs : List MType) (ht : ∀ idx (h : idx < vs.length), vs[idx].isTuple)
    (cl : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
    (h_cl : ∀ idx (h : idx < vs.length), (cl idx h).ReasonablyAligned) :
    (mkEnum vs cl).ReasonablyAligned :=
  .enum vs _ _ _ _ (by grind)

theorem mk_reasonablyAligned (ty : MType) [hr : ty.Reasonable] : (mk ty).ReasonablyAligned := by
  induction hr <;> grind [mk, Layout.ReasonablyAligned.int]

end ReprC
end Layout
end Aeneas
