module
public import Aeneas.Data.MTypes
import all Init.Data.Nat.Power2.Basic
public section

namespace Aeneas

/-! ## Size and Alignment -/

structure SizeAndAlign : Type 0 where
  size : Nat
  align : Nat
  wf_align : align.isPowerOfTwo
  wf_size : align ∣ size

namespace SizeAndAlign

lemma dvd_of_isPowerOfTwo_le {a b : Nat} (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo) (hle : a ≤ b) :
    a ∣ b := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle)

def alignUp (x A : Nat) : Nat := ((x + A - 1) / A) * A

lemma le_alignUp (x : Nat) {A : Nat} (hA : 0 < A) : x ≤ alignUp x A := by
  have h := Nat.div_add_mod (x + A - 1) A
  rw [Nat.mul_comm] at h
  have := Nat.mod_lt (x + A - 1) hA
  dsimp [alignUp]; omega

lemma num_bytes_is_power_of_two {ty : IUScalarTy} : (ty.numBits / 8).isPowerOfTwo := by
  rcases ty with ⟨ty⟩ | ⟨ty⟩ <;> cases ty <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h] <;> decide

end SizeAndAlign

def IUScalarTy.size_and_align (ty : IUScalarTy) : SizeAndAlign :=
  ⟨ty.numBits / 8, ty.numBits / 8, SizeAndAlign.num_bytes_is_power_of_two, by simp⟩

/-! ## Core Layout Representation (`Discriminator`, `TagToWrite`, `Layout`) -/

inductive Discriminator where
  | known (n : Nat)
  | invalid
  -- the matcher is a finite total function
  | read (offset : Nat) (ty : IUScalarTy) (matcher : BitVec ty.numBits -> Discriminator)

structure TagToWrite where
  offset : Nat
  ty : IUScalarTy
  data : IUScalar ty

-- We leverage dependent types. For now, Lean seems to be able to handle it.
inductive Layout : MType → Type 0 where
  | int : Layout (.int ty)
  | tuple
      (field_offs : Fin ts.length → Nat)
      -- NB: Lean is sensitive to the specifics of this inductive definition.
      -- For example, merging `field_layouts` and `field_offs` into one function
      -- returning a pair is not possible, as that prevents Lean from seeing that
      -- the inductive is strictly positive.
      (field_layouts : (idx : Fin ts.length) → Layout ts[idx])
      (sa : SizeAndAlign) :
      Layout (.tuple ts)
  | enum
      (variant_tags : Fin vs.length → List TagToWrite)
      (variant_layouts : (idx : Fin vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) :
      Layout (.enum vs)

namespace Layout

def size_and_align : {ty : MType} → Layout ty → SizeAndAlign
  | .int ty, .int => ty.size_and_align
  | _, .tuple _ _ sa => sa
  | _, .enum _ _ _ sa => sa

/-! ## Layout Validity -/

structure ScalarValidAt (st : IUScalarTy) (off : Nat) (sa : SizeAndAlign) where
  in_bounds : off + st.size_and_align.size ≤ sa.size
  aligned : st.size_and_align.align ∣ off

end Layout

def TagToWrite.Valid (t : TagToWrite) (sa : SizeAndAlign) :=
  Layout.ScalarValidAt t.ty t.offset sa

inductive Discriminator.Valid (sa : SizeAndAlign) (n : Nat) : Discriminator → Prop where
  | known d : d < n → Discriminator.Valid _ _ (.known d)
  | invalid : Discriminator.Valid _ _ .invalid
  | read off ty matcher :
      Layout.ScalarValidAt ty off sa →
      (∀ idx, (matcher idx).Valid sa n) →
      Discriminator.Valid _ _ (.read off ty matcher)

namespace Layout

def disj_range (r1 r2 : Nat × Nat) : Prop :=
  ∀ n, r1.1 ≤ n → n < r1.2 → r2.1 ≤ n → n < r2.2 → False

structure TupleValid
      (field_offs : Fin n → Nat)
      (field_layouts : (idx : Fin n) → SizeAndAlign)
      (sa : SizeAndAlign) where
  fields_disj :
    let field_range := λ (i : Fin n) ↦ (field_offs i, field_offs i + (field_layouts i).size)
    ∀ (i1 i2 : Fin n), i1 ≠ i2 → disj_range (field_range i1) (field_range i2)
  fields_aligned : ∀ i, sa.align ≥ (field_layouts i).2
  size_bounds : ∀ i, sa.size ≥ field_offs i + (field_layouts i).1
  offs_aligned : ∀ i, (field_layouts i).2 ∣ field_offs i

structure EnumValid
      (variant_tags : Fin n → List TagToWrite)
      (variant_layouts : (idx : Fin n) → SizeAndAlign)
      (discr : Discriminator)
      (sa : SizeAndAlign) where
  data_sizes : ∀ idx, (variant_layouts idx).size = sa.size
  data_aligns : ∀ idx, (variant_layouts idx).align ≤ sa.align
  taggers_valid : discr.Valid sa n

inductive Valid : {ty : MType} → Layout ty → Prop where
  | int ty : Valid (.int : Layout (.int ty))
  | tuple ts fo fl sa :
      (∀ idx, (fl idx).Valid) →
      TupleValid fo (λ i ↦ (fl i).size_and_align) sa →
      Valid (.tuple fo fl sa : Layout (.tuple ts))
  | enum vs vt vl dc sa :
      (∀ idx, (vl idx).Valid) →
      EnumValid vt (λ i ↦ (vl i).size_and_align) dc sa →
      Valid (.enum vt vl dc sa : Layout (.enum vs))

/-! ## Canonical Witness Layout Construction -/

namespace Example

open SizeAndAlign

def finMax : (n : Nat) → (Fin n → Nat) → Nat → Nat
  | 0, _, init => init
  | n + 1, f, init => max (f 0) (finMax n (λ i ↦ f i.succ) init)

lemma init_le_finMax : (n : Nat) → (f : Fin n → Nat) → (init : Nat) → init ≤ finMax n f init
  | 0, _, _ => Nat.le_refl _
  | n + 1, f, init => Nat.le_trans (init_le_finMax n (λ i ↦ f i.succ) init) (Nat.le_max_right _ _)

lemma le_finMax : (n : Nat) → (f : Fin n → Nat) → (init : Nat) → (i : Fin n) →
    f i ≤ finMax n f init
  | _ + 1, _, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | n + 1, f, init, ⟨i + 1, hi⟩ =>
    Nat.le_trans (le_finMax n (λ k ↦ f k.succ) init ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      (Nat.le_max_right _ _)

lemma finMax_isPowerOfTwo : (n : Nat) → (f : Fin n → Nat) → (init : Nat) →
    init.isPowerOfTwo → (∀ i, (f i).isPowerOfTwo) → (finMax n f init).isPowerOfTwo
  | 0, _, _, h0, _ => h0
  | n + 1, f, init, h0, hf => by
    by_cases h : f 0 ≤ finMax n (λ i ↦ f i.succ) init
    · simp [finMax, Nat.max_eq_right h, finMax_isPowerOfTwo n _ init h0 (λ i ↦ hf i.succ)]
    · simp [finMax, Nat.max_eq_left (Nat.le_of_not_le h), hf 0]

def padVariantLayout {t : MType} (ht : t.isTuple) (cl : { l : Layout t // l.Valid })
    (sa : SizeAndAlign)
    (h_size : cl.1.size_and_align.size + sa.align ≤ sa.size)
    (h_align : cl.1.size_and_align.align ≤ sa.align) :
    { l : Layout t // l.Valid ∧ l.size_and_align = sa } :=
  match t, ht, cl with
  | .int _, h, _ => nomatch h
  | .enum _, h, _ => nomatch h
  | .tuple ts, _, ⟨.tuple vfo vfl vsa, h_valid⟩ =>
    ⟨.tuple (λ j ↦ sa.align + vfo j) vfl sa, by
      cases h_valid with
      | tuple _ _ _ _ h_vfl_valid h_vtuple =>
        refine ⟨.tuple ts _ vfl sa h_vfl_valid ⟨?_, ?_, ?_, ?_⟩, rfl⟩
        · dsimp only
          intro i1 i2 hne n h1 h2 h3 h4
          have hdisj := h_vtuple.fields_disj
          dsimp only at hdisj
          exact hdisj i1 i2 hne (n - sa.align) (by omega) (by omega) (by omega) (by omega)
        · intro j
          exact Nat.le_trans (h_vtuple.fields_aligned j) h_align
        · intro j
          have := h_vtuple.size_bounds j
          dsimp [Layout.size_and_align] at h_size
          omega
        · intro j
          have hdvd : (vfl j).size_and_align.align ∣ sa.align :=
            dvd_of_isPowerOfTwo_le (vfl j).size_and_align.wf_align sa.wf_align
              (Nat.le_trans (h_vtuple.fields_aligned j) h_align)
          exact Nat.dvd_add hdvd (h_vtuple.offs_aligned j)⟩

def mk (ty : MType) {hr : ty.Reasonable} : { l : Layout ty // l.Valid } :=
  match ty with
  | .int ty => ⟨.int, .int ty⟩
  | .tuple ts =>
    let child_layouts : (idx : Fin ts.length) → { l : Layout ts[idx] // l.Valid } :=
      λ idx ↦
        have h_child : ts[idx].Reasonable := by cases hr with | tuple _ h => exact h idx
        mk ts[idx] (hr := h_child)
    let fl : (idx : Fin ts.length) → Layout ts[idx] := λ idx ↦ (child_layouts idx).1
    let fsa : Fin ts.length → SizeAndAlign := λ idx ↦ (fl idx).size_and_align
    let A := finMax ts.length (λ i ↦ (fsa i).align) 1
    let hA : A.isPowerOfTwo :=
      finMax_isPowerOfTwo ts.length _ 1 Nat.isPowerOfTwo_one (λ i ↦ (fsa i).wf_align)
    let S := (finMax ts.length (λ i ↦ (fsa i).size) 0 + A - 1) / A
    let fo : Fin ts.length → Nat := λ i ↦ (i.val * S) * A
    let sa : SizeAndAlign := ⟨(ts.length * S) * A, A, hA, Nat.dvd_mul_left A _⟩
    have h_end_le : ∀ i : Fin ts.length, (i.val * S) * A + (fsa i).size ≤ ((i.val + 1) * S) * A := λ i ↦ by
      have : (fsa i).size ≤ S * A :=
        Nat.le_trans (le_finMax _ (λ j ↦ (fsa j).size) 0 i)
          (le_alignUp _ (Nat.pos_of_isPowerOfTwo hA))
      calc (i.val * S) * A + (fsa i).size
        _ ≤ (i.val * S) * A + S * A := by omega
        _ = (i.val * S + S) * A := (Nat.add_mul _ _ A).symm
        _ = ((i.val + 1) * S) * A := by rw [Nat.add_one_mul]
    have h_lt : ∀ {i1 i2 : Fin ts.length}, i1 < i2 → (i1.val * S) * A + (fsa i1).size ≤ (i2.val * S) * A :=
      λ hlt ↦ Nat.le_trans (h_end_le _) (Nat.mul_le_mul_right A (Nat.mul_le_mul_right S hlt))
    ⟨.tuple fo fl sa,
     .tuple ts fo fl sa (λ idx ↦ (child_layouts idx).2)
       ⟨by dsimp only [fo]; intro i1 i2 hne n h1 h2 h3 h4
           rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
           · have := h_lt h; dsimp only [fsa] at this; omega
           · have := h_lt h; dsimp only [fsa] at this; omega,
        λ i ↦ le_finMax _ (λ j ↦ (fsa j).align) 1 i,
        λ i ↦ Nat.le_trans (h_end_le i) (Nat.mul_le_mul_right A (Nat.mul_le_mul_right S i.isLt)),
        λ i ↦ Nat.dvd_trans (dvd_of_isPowerOfTwo_le (fsa i).wf_align hA (le_finMax _ (λ j ↦ (fsa j).align) 1 i))
                (Nat.dvd_mul_left A _)⟩⟩
  | .enum vs =>
    let child_layouts : (idx : Fin vs.length) → { l : Layout vs[idx] // l.Valid } :=
      λ idx ↦
        have h_child : vs[idx].Reasonable := by cases hr with | enum _ _ _ h => exact h idx
        mk vs[idx] (hr := h_child)
    have ht : ∀ idx : Fin vs.length, vs[idx].isTuple := by
      cases hr with | enum _ _ ht _ => exact ht
    let fsa : Fin vs.length → SizeAndAlign := λ idx ↦ (child_layouts idx).1.size_and_align
    let tagTy : IUScalarTy := .unsigned .Usize
    let A := finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
    let hA : A.isPowerOfTwo :=
      finMax_isPowerOfTwo vs.length _ _ tagTy.size_and_align.wf_align (λ i ↦ (fsa i).wf_align)
    let S := (finMax vs.length (λ i ↦ (fsa i).size) 0 + A - 1) / A
    let sa : SizeAndAlign := ⟨(S + 1) * A, A, hA, Nat.dvd_mul_left A (S + 1)⟩
    let vl := λ idx ↦
      padVariantLayout (ht idx) (child_layouts idx) sa
        (by
          have h1 : (fsa idx).size ≤ S * A :=
            Nat.le_trans (le_finMax _ (λ j ↦ (fsa j).size) 0 idx)
              (le_alignUp _ (Nat.pos_of_isPowerOfTwo hA))
          have h2 : S * A + A = (S + 1) * A := (Nat.add_one_mul S A).symm
          dsimp [fsa, sa] at *; omega)
        (le_finMax _ (λ i ↦ (fsa i).align) _ idx)
    let vt : Fin vs.length → List TagToWrite :=
      λ idx ↦ [⟨0, tagTy, ⟨BitVec.ofNat tagTy.numBits idx.val⟩⟩]
    let discr : Discriminator :=
      .read 0 tagTy (λ bv ↦ if bv.toNat < vs.length then .known bv.toNat else .invalid)
    have hTagValid : ScalarValidAt tagTy 0 sa :=
      ⟨by have := init_le_finMax vs.length (λ i ↦ (fsa i).align) tagTy.size_and_align.align
          have := Nat.le_mul_of_pos_left A (Nat.succ_pos S)
          dsimp [sa, A, IUScalarTy.size_and_align] at *; omega,
       Nat.dvd_zero _⟩
    have hDiscrValid : discr.Valid sa vs.length :=
      .read 0 tagTy _ hTagValid (λ bv ↦ by
        split <;> [exact .known _ ‹_›; exact .invalid])
    ⟨.enum vt (λ idx ↦ (vl idx).1) discr sa,
     .enum vs vt (λ idx ↦ (vl idx).1) discr sa
       (λ idx ↦ (vl idx).2.1)
       ⟨λ idx ↦ by rw [(vl idx).2.2],
        λ idx ↦ by rw [(vl idx).2.2],
        hDiscrValid⟩⟩
termination_by sizeOf ty
decreasing_by
  all_goals
    simp_wf
    have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt)
    omega

end Example

end Layout

end Aeneas
