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

@[simp, grind ←] lemma init_le_finMax : ∀ n (f : Fin n → Nat) init, init ≤ finMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, _, init => Nat.le_trans (init_le_finMax n _ init) (Nat.le_max_right _ _)

@[simp] lemma le_finMax : ∀ n (f : Fin n → Nat) init (i : Fin n), f i ≤ finMax n f init
  | _ + 1, _, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | n + 1, f, init, ⟨i + 1, hi⟩ =>
    Nat.le_trans (le_finMax n (λ k ↦ f k.succ) init ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (Nat.le_max_right _ _)

@[simp, grind ←]
lemma finMax_isPowerOfTwo : ∀ n (f : Fin n → Nat) init,
    init.isPowerOfTwo → (∀ i, (f i).isPowerOfTwo) → (finMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    have := finMax_isPowerOfTwo n (λ i ↦ f i.succ) init (by grind) (by grind)
    by_cases h : f 0 ≤ finMax n (λ i ↦ f i.succ) init
    all_goals (simp [finMax]; grind)

@[simp, grind ←]
lemma one_isPowerOfTwo : Nat.isPowerOfTwo 1 := by decide

/-- Byte offset after placing the first `k` fields sequentially under `#[repr(C)]`. -/
def tupleCursor {n : Nat} (fsa : Fin n → SizeAndAlign) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, hk =>
    let fi : Fin n := ⟨k, hk⟩
    alignUp (tupleCursor fsa k (Nat.le_of_succ_le hk)) (fsa fi).align + (fsa fi).size

/-- Byte offset of field `i` under `#[repr(C)]`: current cursor aligned up to `(fsa i).align`. -/
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

private lemma tupleCursor_mono {n : Nat} (fsa : Fin n → SizeAndAlign) :
    ∀ {k1 k2 : Nat} (hk1 : k1 ≤ n) (hk2 : k2 ≤ n), k1 ≤ k2 →
      tupleCursor fsa k1 hk1 ≤ tupleCursor fsa k2 hk2
  | _, 0, _, _, hle => by cases Nat.eq_zero_of_le_zero hle; rfl
  | k1, k2 + 1, hk1, hk2, hle => by
    rcases Nat.of_le_succ hle with h | rfl
    · have ih := tupleCursor_mono fsa hk1 (Nat.le_of_succ_le hk2) h
      have h_align := le_alignUp (tupleCursor fsa k2 (Nat.le_of_succ_le hk2))
        (Nat.pos_of_isPowerOfTwo (fsa ⟨k2, hk2⟩).wf_align)
      simp only [tupleCursor]
      omega
    · rfl

private lemma tupleFieldOffset_end_le_cursor {n : Nat} (fsa : Fin n → SizeAndAlign) (i : Fin n)
    {k : Nat} (hk : k ≤ n) (hik : i.val + 1 ≤ k) :
    tupleFieldOffset fsa i + (fsa i).size ≤ tupleCursor fsa k hk := by
  have : tupleFieldOffset fsa i + (fsa i).size = tupleCursor fsa (i.val + 1) i.isLt := rfl
  exact this ▸ tupleCursor_mono fsa i.isLt hk hik

lemma mkTuple_valid (ts : List MType) (fl : (idx : Fin ts.length) → Layout ts[idx])
    (h_fl : ∀ idx, (fl idx).Valid) :
    (mkTuple ts fl).Valid := by
  let fsa : Fin ts.length → SizeAndAlign := λ idx ↦ (fl idx).size_and_align
  let A := finMax ts.length (λ i ↦ (fsa i).align) 1
  have hA : A.isPowerOfTwo := finMax_isPowerOfTwo ts.length _ 1 Nat.isPowerOfTwo_one (λ i ↦ (fsa i).wf_align)
  refine .tuple ts _ fl _ h_fl ⟨?_, ?_⟩
  · dsimp only
    intro i1 i2 hne n h1 h2 h3 h4
    have h_ord : ∀ {a b : Fin ts.length}, a < b →
        tupleFieldOffset fsa a + (fl a).size ≤ tupleFieldOffset fsa b := λ {a b} hab ↦ by
      have h_cur := tupleFieldOffset_end_le_cursor fsa a (Nat.le_of_lt b.isLt) hab
      have h_aln := le_alignUp (tupleCursor fsa b.val (Nat.le_of_lt b.isLt))
        (Nat.pos_of_isPowerOfTwo (fsa b).wf_align)
      simpa [fsa, tupleFieldOffset] using Nat.le_trans h_cur h_aln
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h <;>
      [have := h_ord h; have := h_ord h] <;> dsimp only [fsa] at this <;> omega
  · intro i
    have h_cur := tupleFieldOffset_end_le_cursor fsa i (Nat.le_refl ts.length) i.isLt
    have h_aln := le_alignUp (tupleCursor fsa ts.length (Nat.le_refl _)) (Nat.pos_of_isPowerOfTwo hA)
    simpa [fsa] using Nat.le_trans h_cur h_aln

private lemma encode_tuple_prefix_uninit {ts : List MType}
    (fo : Fin ts.length → Nat) (fl : (idx : Fin ts.length) → Layout ts[idx]) (sa : SizeAndAlign)
    (prefix_len : Nat) (hoff : ∀ idx : Fin ts.length, prefix_len ≤ fo idx)
    (v : MVal) (hv : v.valid_for (.tuple ts)) {j : Fin sa.size} (hlt : j.val < prefix_len) :
    (encode (.tuple fo fl sa) v hv)[j.val] = .uninit := by
  cases v with
  | int _ | variant _ _ => nomatch hv
  | tuple values =>
    suffices ∀ (idxs : List (Fin ts.length)) (acc : Bytes sa.size),
        (idxs.foldl (init := acc) λ (bytes : Bytes sa.size) (idx : Fin ts.length) ↦
          let i : Fin values.length := ⟨idx.val, by rw [hv.tuple_len]; exact idx.isLt⟩
          bytes.write_subslice_at_index (fo idx) (encode (fl idx) values[i] (by simpa [i] using hv.tuple_proj i)))[j] = acc[j] by
      exact (this _ _).trans (Bytes.uninit_getElem sa.size j)
    intro idxs acc; induction idxs generalizing acc with
    | nil => rfl
    | cons hd _ ih =>
      exact (ih _).trans (Bytes.write_subslice_at_index_lt acc _ _ (Nat.lt_of_lt_of_le hlt (hoff hd)))

private lemma padVariantLayout_spec {t : MType} (ht : t.isTuple) (cl : Layout t) (hcl : cl.Valid)
    (payload_off : Nat) (sa : SizeAndAlign) (h_size : payload_off + cl.size ≤ sa.size) :
    let vl := padVariantLayout cl payload_off sa
    vl.Valid ∧ vl.size_and_align = sa ∧
      ∀ (v : MVal) (hv : v.valid_for t) (j : Nat) (hj : j < vl.size),
        j < payload_off → (encode vl v hv)[j] = .uninit :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _, h, _, _ => nomatch h
  | .tuple ts, _, .tuple _ vfl _, .tuple _ _ _ _ h_vfl_valid h_vtuple =>
    ⟨.tuple ts _ vfl sa h_vfl_valid
      ⟨by dsimp only; intro i1 i2 hne n h1 h2 h3 h4
          have hdisj := h_vtuple.fields_disj; dsimp only at hdisj
          exact hdisj i1 i2 hne (n - payload_off) (by omega) (by omega) (by omega) (by omega),
       λ j ↦ by have := h_vtuple.size_bounds j; dsimp [size] at h_size; omega⟩,
     rfl,
     λ v hv j hj hlt ↦ encode_tuple_prefix_uninit _ vfl sa payload_off
       (λ _ ↦ Nat.le_add_right _ _) v hv (j := ⟨j, hj⟩) hlt⟩

lemma mkEnum_valid (vs : List MType) (h_max : vs.length ≤ Std.Usize.max)
    (ht : ∀ idx : Fin vs.length, vs[idx].isTuple)
    (cl : (idx : Fin vs.length) → Layout vs[idx])
    (h_cl : ∀ idx, (cl idx).Valid) :
    (mkEnum vs cl).Valid := by
  let fsa : Fin vs.length → SizeAndAlign := λ idx ↦ (cl idx).size_and_align
  let tagTy : IUScalarTy := .unsigned .Usize
  let A := finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
  have hA : A.isPowerOfTwo := finMax_isPowerOfTwo vs.length _ _ tagTy.size_and_align.wf_align (λ i ↦ (fsa i).wf_align)
  let payload_off := alignUp tagTy.size A
  let max_var_sz := finMax vs.length (λ i ↦ (fsa i).size) 0
  let sz := alignUp (payload_off + max_var_sz) A
  let sa : SizeAndAlign := ⟨sz, A, hA, Nat.dvd_mul_left A _⟩
  let vl : (idx : Fin vs.length) → Layout vs[idx] := λ idx ↦ padVariantLayout (cl idx) payload_off sa
  let vt : Fin vs.length → List TagToWrite := λ idx ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx.val⟩⟩]
  let discr : Discriminator := .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
  have hTagLePayload : tagTy.size ≤ payload_off := le_alignUp tagTy.size (Nat.pos_of_isPowerOfTwo hA)
  have hPayloadLeSz : payload_off + max_var_sz ≤ sa.size := le_alignUp _ (Nat.pos_of_isPowerOfTwo hA)
  have hTagBounds : 0 + tagTy.size ≤ sa.size := by omega
  have h_pad := λ (idx : Fin vs.length) ↦ padVariantLayout_spec (ht idx) (cl idx) (h_cl idx) payload_off sa
    (by have := le_finMax vs.length (λ i ↦ (fsa i).size) 0 idx
        simpa [fsa] using Nat.le_trans (Nat.add_le_add_left this _) hPayloadLeSz)
  refine .enum vs vt vl discr sa (λ idx ↦ (h_pad idx).1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx; rw [← size_known, (h_pad idx).2.1]
  · intro idx; rw [(h_pad idx).2.1]
  · intro idx; exact ⟨hTagBounds⟩
  · exact .read 0 tagTy _ ⟨hTagBounds⟩ (λ _ ↦ by split <;> [exact .known _ ‹_›; exact .invalid])
  -- 1. `tags_preserve_payload`: tag writes into `[0 ..< tagTy.size) ⊆ [0 ..< payload_off)`, which is `.uninit`.
  · intro idx v hv payload_bs k
    dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]
    by_cases hk : k.val < tagTy.size
    · have h_vsz : k.val < (vl idx).size := by rw [← size_known, (h_pad idx).2.1]; exact k.isLt
      rw [Bytes.write_subslice_at_index_zero_lt _ _ h_vsz,
          (h_pad idx).2.2 v hv k.val h_vsz (Nat.lt_of_lt_of_le hk hTagLePayload)]
      exact AbstractByte.le_defined_uninit _
    · rw [Bytes.write_subslice_at_index_zero_ge _ _ (Nat.le_of_not_lt hk)]
      exact AbstractByte.le_defined_refl _
  -- 2. `discr_complete`: reading `tagTy` back from `[0 ..< tagTy.size)` recovers `idx.val`.
  · intro idx v hv
    dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, discr, IUScalar.bv]
    unfold decode_discriminant; rw [dif_pos hTagBounds]
    simp only [Bytes.subslice_write_subslice_zero, Bytes.toData_map_init, Option.bind_eq_bind, Option.bind_some,
               Endianness.decode_bitvec_encode_bitvec]
    have h_lt_max : idx.val < 2 ^ tagTy.numBits := by
      have : Std.Usize.max < 2 ^ tagTy.numBits := by
        rcases System.Platform.numBits_eq with h | h <;>
          simp [Std.Usize.max, Std.Usize.numBits, tagTy, IUScalarTy.numBits, Std.UScalarTy.numBits, h]
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt_max, if_pos idx.isLt]; rfl
  -- 3. `discr_tags_le_defined`: if `decode_discriminant bytes discr = some idx.val`, `bytes[0 ..< tagTy.size)` matches `vt idx`.
  · intro bytes idx h_dec
    dsimp only [discr] at h_dec; unfold decode_discriminant at h_dec; rw [dif_pos hTagBounds] at h_dec
    dsimp only [Option.bind_eq_bind] at h_dec
    cases h_data : (bytes.subslice_with_length 0 tagTy.size hTagBounds).toData with
    | none => simp [h_data] at h_dec
    | some bytes_data =>
      rw [h_data] at h_dec; dsimp only [Option.bind_some] at h_dec
      have h_nat : (Endianness.decode_bitvec tagTy bytes_data).toNat = idx.val := by
        split at h_dec <;> [injection h_dec; nomatch h_dec]
      have h_tag_vec : Endianness.encode_bitvec tagTy.size (BitVec.ofNat tagTy.numBits idx.val) = bytes_data := by
        rw [show BitVec.ofNat tagTy.numBits idx.val = Endianness.decode_bitvec tagTy bytes_data by
              rw [← h_nat, BitVec.ofNat_toNat]; simp]
        exact Endianness.encode_bitvec_decode_bitvec tagTy bytes_data
      dsimp only [encode_discriminant, vt, List.foldl_cons, List.foldl_nil, IUScalar.bv]; rw [h_tag_vec]
      intro k
      by_cases hk : k.val < tagTy.size
      · rw [Bytes.write_subslice_at_index_zero_lt _ _ hk]
        rw [show bytes[k] = .init bytes_data[k.val] from by
              simpa [Bytes.subslice_with_length] using Bytes.getElem_of_toData h_data k.val hk]
        simp
      · rw [Bytes.write_subslice_at_index_zero_ge _ _ (Nat.le_of_not_lt hk)]; simp [Bytes.uninit]

theorem mk_valid (ty : MType) [hr : ty.Reasonable] : (mk ty).Valid := by
  induction hr with
  | int st => unfold mk; exact .int st
  | tuple ts _ ih => unfold mk; exact mkTuple_valid ts _ ih
  | enum vs h_max ht _ ih => unfold mk; exact mkEnum_valid vs h_max ht _ ih

/-! ## Part 3: Proving Reasonable Alignment (`ReasonablyAligned`) -/

lemma mkTuple_reasonablyAligned (ts : List MType) (fl : (idx : Fin ts.length) → Layout ts[idx])
    (h_fl : ∀ idx, (fl idx).ReasonablyAligned) :
    (mkTuple ts fl).ReasonablyAligned :=
  .tuple ts _ fl _ h_fl
    ⟨λ i ↦ le_finMax ts.length (λ j ↦ (fl j).size_and_align.align) 1 i,
     λ i ↦ Nat.dvd_mul_left (fl i).size_and_align.align _⟩

private lemma padVariantLayout_reasonablyAligned {t : MType} (ht : t.isTuple) (cl : Layout t)
    (hcl : cl.ReasonablyAligned) (payload_off : Nat) (sa : SizeAndAlign)
    (h_align : cl.size_and_align.align ≤ sa.align) (h_dvd : sa.align ∣ payload_off) :
    (padVariantLayout cl payload_off sa).ReasonablyAligned :=
  match t, ht, cl, hcl with
  | .int _, h, _, _ | .enum _, h, _, _ => nomatch h
  | .tuple ts, _, .tuple _ vfl _, .tuple _ _ _ _ h_vfl_aligned h_vtuple_aligned =>
    .tuple ts _ vfl sa h_vfl_aligned
      ⟨λ j ↦ Nat.le_trans (h_vtuple_aligned.fields_aligned j) h_align,
       λ j ↦ Nat.dvd_add
         (Nat.dvd_trans
           (dvd_of_isPowerOfTwo_le (vfl j).size_and_align.wf_align sa.wf_align
             (Nat.le_trans (h_vtuple_aligned.fields_aligned j) h_align))
           h_dvd)
         (h_vtuple_aligned.offs_aligned j)⟩

lemma mkEnum_reasonablyAligned (vs : List MType) (ht : ∀ idx : Fin vs.length, vs[idx].isTuple)
    (cl : (idx : Fin vs.length) → Layout vs[idx])
    (h_cl : ∀ idx, (cl idx).ReasonablyAligned) :
    (mkEnum vs cl).ReasonablyAligned :=
  .enum vs _ _ _ _
    (λ idx ↦ padVariantLayout_reasonablyAligned (ht idx) (cl idx) (h_cl idx) _ _
      (le_finMax vs.length (λ i ↦ (cl i).size_and_align.align) _ idx)
      (Nat.dvd_mul_left _ _))
    (λ _ ↦ Nat.dvd_zero _)

theorem mk_reasonablyAligned (ty : MType) [hr : ty.Reasonable] : (mk ty).ReasonablyAligned := by
  induction hr with
  | int st => unfold mk; exact .int st
  | tuple ts _ ih => unfold mk; exact mkTuple_reasonablyAligned ts _ ih
  | enum vs _ ht _ ih => unfold mk; exact mkEnum_reasonablyAligned vs ht _ ih

end ReprC
end Layout
end Aeneas
