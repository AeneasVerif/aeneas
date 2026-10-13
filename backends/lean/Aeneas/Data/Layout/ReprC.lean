module
public import Aeneas.Data.Layout.Defs
public import Aeneas.Data.Layout.GaloisConnection
@[expose] public section

namespace Aeneas
namespace Layout
namespace ReprC

open SizeAndAlign

/-! ## Part 1: Constructing the `#[repr(C)]` Layout -/

def finMax : (n : Nat) → (Fin n → Nat) → Nat → Nat
  | 0, _, init => init
  | n + 1, f, init => max (f 0) (finMax n (λ i ↦ f i.succ) init)

@[simp] lemma init_le_finMax : ∀ n (f : Fin n → Nat) init, init ≤ finMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, _, init => Nat.le_trans (init_le_finMax n _ init) (Nat.le_max_right _ _)

grind_pattern init_le_finMax => finMax n f init

@[simp] lemma le_finMax : ∀ n (f : Fin n → Nat) init (i : Fin n), f i ≤ finMax n f init
  | _ + 1, _, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | n + 1, f, init, ⟨i + 1, hi⟩ =>
    Nat.le_trans (le_finMax n (λ k ↦ f k.succ) init ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (Nat.le_max_right _ _)

grind_pattern le_finMax => finMax n f init, i.val

@[simp]
lemma finMax_isPowerOfTwo : ∀ n (f : Fin n → Nat) init,
    init.isPowerOfTwo → (∀ i, (f i).isPowerOfTwo) → (finMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    have := finMax_isPowerOfTwo n (λ i ↦ f i.succ) init (by grind) (by grind)
    by_cases h : f 0 ≤ finMax n (λ i ↦ f i.succ) init
    all_goals (simp [finMax]; grind)

grind_pattern finMax_isPowerOfTwo => finMax n f init

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`. -/
def tupleCursor {n : Nat} (fsa : Fin n → SizeAndAlign) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, hk =>
    let fi : Fin n := ⟨k, hk⟩
    alignUp (tupleCursor fsa k (Nat.le_of_succ_le hk)) (fsa fi).align + (fsa fi).size

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `(fsa i).align`. -/
@[grind =]
def tupleFieldOffset {n : Nat} (fsa : Fin n → SizeAndAlign) (i : Fin n) : Nat :=
  alignUp (tupleCursor fsa i.val (by grind)) (fsa i).align

/-- `#[repr(C)]` layout for a tuple/struct given layouts for its fields. -/
noncomputable def mkTuple (ts : List MType) (fl : (idx : Fin ts.length) → Layout ts[idx]) :
    Layout (.tuple ts) :=
  let fsa : Fin ts.length → SizeAndAlign := λ idx ↦ (fl idx).size_and_align
  let A := finMax ts.length (λ i ↦ (fsa i).align) 1
  let sz := alignUp (tupleCursor fsa ts.length (by grind)) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  .tuple (tupleFieldOffset fsa) fl sa

/-- Shifts a tuple variant's field offsets right by `payload_off` and sets its `SizeAndAlign` to `sa`,
    leaving prefix bytes `[0 ..< payload_off)` as padding for the discriminant tag. -/
def padVariantLayout : {t : MType} → Layout t → Nat → SizeAndAlign → Layout t
  | .tuple _, .tuple vfo vfl _, payload_off, sa =>
      .tuple (λ j ↦ payload_off + vfo j) vfl sa
  | _, l, _, _ => l

/-- `#[repr(C)]` layout for an enum given layouts for its tuple variants. -/
noncomputable def mkEnum (vs : List MType) (cl : (idx : Fin vs.length) → Layout vs[idx]) :
    Layout (.enum vs) :=
  let fsa : Fin vs.length → SizeAndAlign := λ idx ↦ (cl idx).size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := finMax vs.length (λ i ↦ (fsa i).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Fin vs.length) → Layout vs[idx] := λ idx ↦ padVariantLayout (cl idx) payload_off sa
  let vt : Fin vs.length → List TagToWrite := λ idx ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx.val⟩⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  .enum vt vl discr sa

/-- Constructs the `#[repr(C)]` layout for an `MType`.
    Only `noncomputable` because scalar alignments (`IUScalarTy.size_and_align`) are `noncomputable`. -/
noncomputable def mk : (ty : MType) → Layout ty
  | .int _ => .int
  | .tuple ts => mkTuple ts (λ idx ↦ mk ts[idx])
  | .enum vs => mkEnum vs (λ idx ↦ mk vs[idx])
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt); omega

/-! ## Part 2: Proving Layout Validity (`Valid`) -/

@[grind ←] private lemma tupleCursor_mono {n : Nat} (fsa : Fin n → SizeAndAlign) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsa k1 hk1 ≤ tupleCursor fsa k2 hk2
  | 0, 0, _, _, _ => Nat.le_refl _
  | _ + 1, 0, _, _, h => nomatch h
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have := tupleCursor_mono fsa hk1 (by omega) h
      simp [tupleCursor]; grind
    · rfl

private lemma tupleFieldOffset_mono {n : Nat} (fsa : Fin n → SizeAndAlign)
    {a b : Fin n} (hab : a.val < b.val) :
    tupleFieldOffset fsa a + (fsa a).size ≤ tupleFieldOffset fsa b := by
  have h1 : tupleFieldOffset fsa a + (fsa a).size = tupleCursor fsa (a.val + 1) a.isLt := rfl
  have h2 := tupleCursor_mono fsa a.isLt (Nat.le_of_lt b.isLt) hab
  grind

grind_pattern tupleFieldOffset_mono => tupleFieldOffset fsa a, tupleFieldOffset fsa b

private lemma tupleFieldOffset_le_end {n : Nat} (fsa : Fin n → SizeAndAlign) (i : Fin n) :
    tupleFieldOffset fsa i + (fsa i).size ≤ tupleCursor fsa n (Nat.le_refl n) :=
  tupleCursor_mono fsa i.isLt (Nat.le_refl n) i.isLt

grind_pattern tupleFieldOffset_le_end => tupleFieldOffset fsa i

@[grind ←]
lemma mkTuple_valid (ts : List MType) (fl : (idx : Fin ts.length) → Layout ts[idx])
    (h_fl : ∀ idx, (fl idx).Valid) :
    (mkTuple ts fl).Valid :=
  .tuple ts _ fl _ h_fl ⟨by dsimp only; grind, by grind⟩

private lemma encode_tuple_prefix_uninit {ts : List MType}
    (fo : Fin ts.length → Nat) (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (prefix_len : Nat) (hoff : ∀ idx : Fin ts.length, prefix_len ≤ fo idx)
    (v : MVal) (hv : v.valid_for (.tuple ts)) {j : Fin sa.size} (hlt : j.val < prefix_len) :
    (encode (.tuple fo fl sa) v hv)[j.val] = .uninit := by
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
      ⟨by intro fields_range i1 i2 hne n
          have := h_vtuple.fields_disj i1 i2 hne (n - payload_off)
          grind,
       λ j ↦ by have := h_vtuple.size_bounds j; grind⟩,
     λ v hv j hj hlt ↦ encode_tuple_prefix_uninit _ vfl sa payload_off (by grind) v hv (j := ⟨j, hj⟩) hlt⟩

private lemma usize_max_lt_two_pow : Std.Usize.max < 2 ^ (IUScalarTy.unsigned .Usize).numBits := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp [Std.Usize.max, Std.Usize.numBits, IUScalarTy.numBits, Std.UScalarTy.numBits, h]

@[grind ←]
lemma mkEnum_valid (vs : List MType) (h_max : vs.length ≤ Std.Usize.max)
    (ht : ∀ idx : Fin vs.length, vs[idx].isTuple)
    (cl : (idx : Fin vs.length) → Layout vs[idx])
    (h_cl : ∀ idx, (cl idx).Valid) :
    (mkEnum vs cl).Valid := by
  let fsa : Fin vs.length → SizeAndAlign := λ idx ↦ (cl idx).size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
  let payload_off := alignUp tagTy.size A
  let max_var_sz := finMax vs.length (λ i ↦ (fsa i).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, by grind, by grind⟩
  let vl : (idx : Fin vs.length) → Layout vs[idx] := λ idx ↦ padVariantLayout (cl idx) payload_off sa
  let vt : Fin vs.length → List TagToWrite := λ idx ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx.val⟩⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  have hTagBounds : 0 + tagTy.size ≤ sa.size := by grind
  have h_pad := λ (idx : Fin vs.length) ↦ padVariantLayout_spec (ht idx) (cl idx) (h_cl idx) payload_off sa (by grind)
  refine .enum vs vt vl discr sa (λ idx ↦ (h_pad idx).1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind [List.Forall]
  · grind
  -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tagTy.size) ⊆ [0 ..< payload_off)`, which is `.uninit`.
  · intro idx v hv payload_bs k
    have := (h_pad idx).2 v hv k.val
    simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
    grind
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx.val`.
  · intro idx v hv
    have := usize_max_lt_two_pow
    unfold decode_discriminant
    simp [encode_discriminant, vt, IUScalar.bv]
    grind
  -- 3. `discr_tags_le_defined`: if `decode_discriminant bytes discr = some idx.val`, `bytes[0 ..< tagTy.size)` matches `vt idx`.
  · intro bytes idx h_dec
    simp only [discr, decode_discriminant, hTagBounds, ↓reduceDIte] at h_dec
    cases h_data : (bytes.subslice_with_length 0 tagTy.size hTagBounds).toData with
    | none => simp [h_data] at h_dec
    | some bytes_data =>
      simp [h_data, apply_ite (decode_discriminant bytes)] at h_dec
      have : Endianness.encode_bitvec tagTy.size (BitVec.ofNat tagTy.numBits idx.val) = bytes_data := by
        simp [← h_dec.2]
      intro k
      have := Bytes.getElem_of_toData h_data k.val
      simp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
      grind

theorem mk_valid (ty : MType) [hr : ty.Reasonable] : (mk ty).Valid := by
  induction hr <;> grind [mk, Layout.Valid.int]

/-! ## Part 3: Proving Reasonable Alignment (`ReasonablyAligned`) -/

@[grind ←]
lemma mkTuple_reasonablyAligned (ts : List MType) (fl : (idx : Fin ts.length) → Layout ts[idx])
    (h_fl : ∀ idx, (fl idx).ReasonablyAligned) :
    (mkTuple ts fl).ReasonablyAligned :=
  .tuple ts _ fl _ h_fl ⟨λ i ↦ by grind, λ i ↦ by grind⟩

private lemma padVariantLayout_reasonablyAligned {t : MType} (ht : t.isTuple) (cl : Layout t)
    (hcl : cl.ReasonablyAligned) (payload_off : Nat) (sa : SizeAndAlign)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa).ReasonablyAligned :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _, h, _, _ => nomatch h
  | .tuple ts, _, .tuple _ vfl _, .tuple _ _ _ _ h_vfl_aligned h_vtuple_aligned =>
    .tuple ts _ vfl sa h_vfl_aligned
      ⟨λ j ↦ by have := h_vtuple_aligned.fields_aligned j; grind,
       λ j ↦ by
         have : (vfl j).size_and_align.align ∣ sa.align := by
           have := h_vtuple_aligned.fields_aligned j; grind
         have := h_vtuple_aligned.offs_aligned j
         grind [Nat.dvd_trans, Nat.dvd_add]⟩

@[grind ←]
lemma mkEnum_reasonablyAligned (vs : List MType) (ht : ∀ idx : Fin vs.length, vs[idx].isTuple)
    (cl : (idx : Fin vs.length) → Layout vs[idx])
    (h_cl : ∀ idx, (cl idx).ReasonablyAligned) :
    (mkEnum vs cl).ReasonablyAligned :=
  .enum vs _ _ _ _
    (λ idx ↦ padVariantLayout_reasonablyAligned (ht idx) (cl idx) (h_cl idx) _ _ (by grind) (by grind))
    (λ _ ↦ by grind [List.Forall, Nat.dvd_zero])

theorem mk_reasonablyAligned (ty : MType) [hr : ty.Reasonable] : (mk ty).ReasonablyAligned := by
  induction hr <;> grind [mk, Layout.ReasonablyAligned.int]

end ReprC
end Layout
end Aeneas
