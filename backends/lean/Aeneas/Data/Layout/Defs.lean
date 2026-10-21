module
public import Aeneas.Data.Byte
public import Aeneas.Data.BitVec
public import Aeneas.Data.Layout.Prelims
public import Aeneas.Data.Layout.Bytes
public import Aeneas.Data.Layout.MTypes
@[expose] public section

namespace Aeneas

/-! ## Size and Alignment -/

structure SizeAndAlign : Type 0 where
  size : Nat
  align : Nat
  wf_align : align.isPowerOfTwo
  wf_size : align ∣ size

@[ext]
lemma SizeAndAlign.ext {a b : SizeAndAlign} (h_size : a.size = b.size) (h_align : a.align = b.align) :
    a = b := by
  cases a; cases b; simp_all

lemma SizeAndAlign.grind_wf_align (sa : SizeAndAlign) : sa.align.isPowerOfTwo := sa.wf_align
grind_pattern SizeAndAlign.grind_wf_align => sa.align

lemma SizeAndAlign.grind_wf_size (sa : SizeAndAlign) : sa.align ∣ sa.size := sa.wf_size
grind_pattern SizeAndAlign.grind_wf_size => sa.size

namespace SizeAndAlign

lemma num_bytes_is_power_of_two {ty : IUScalarTy} : (ty.numBits / 8).isPowerOfTwo := by
  rcases ty with ⟨ty⟩ | ⟨ty⟩ <;>
    cases ty <;>
    rcases System.Platform.numBits_eq with h | h <;>
    simp [IUScalarTy.numBits, Std.IScalarTy.numBits, Std.UScalarTy.numBits, h] <;>
    decide

lemma align_pos (sa : SizeAndAlign) : 0 < sa.align :=
  Nat.pos_of_isPowerOfTwo sa.wf_align
grind_pattern align_pos => sa.align

end SizeAndAlign

@[reducible, simp, grind =] def SizeAndAlign.ValidForScalar (sa : SizeAndAlign) (ty : IUScalarTy) : Prop :=
  sa.size = ty.numBits / 8

@[reducible, simp, grind =] def IUScalarTy.size (ty : IUScalarTy) : Nat := ty.numBits / 8

@[simp, grind →] lemma SizeAndAlign.ValidForScalar.size_eq (ty : IUScalarTy) (sa : SizeAndAlign) (h : sa.ValidForScalar ty) : sa.size = ty.size := h

@[simp, grind =] def IUScalarTy.reasonablyAligned (ty : IUScalarTy) : SizeAndAlign :=
  ⟨ty.size, ty.size, SizeAndAlign.num_bytes_is_power_of_two, by simp⟩

@[simp, grind .] lemma IUScalarTy.reasonablyAligned_isReasonable {ty : IUScalarTy} : ty.reasonablyAligned.ValidForScalar ty := by rfl

@[simp, grind →] lemma SizeAndAlign.sizeOneAlignOne (sa : SizeAndAlign) : sa.size = 1 → sa.align = 1 := by
  intros h
  apply Nat.le_antisymm
  · apply Nat.le_of_dvd
    { omega }
    rw [←h]
    apply sa.wf_size
  · apply Nat.pos_of_isPowerOfTwo
    apply sa.wf_align

@[simp, grind =, reducible, match_pattern] def SizeAndAlign.zero_sized_minimally_aligned : SizeAndAlign :=
  ⟨0, 1, by grind, by grind⟩

/-! ## Core Layout Representation (`Discriminator`, `TagToWrite`, `Layout`) -/

inductive Discriminator where
  | known (n : Nat)
  | invalid
  -- the matcher is a finite total function. Almost always it will match on several ranges,
  -- and return a "default" instance for everything outside of these ranges.
  | read (offset : Nat) (ty : IUScalarTy) (matcher : BitVec ty.numBits -> Discriminator)

structure TagToWrite where
  offset : Nat
  ty : IUScalarTy
  data : IUScalar ty

-- We leverage dependent types. For now, Lean seems to be able to handle it.
inductive Layout : MType → Type 0 where
  | int (sa : SizeAndAlign) :
      sa.ValidForScalar ty →
      Layout (.int ty)
  | tuple
      (field_offs : (idx : Nat) → idx < ts.length → Nat)
      -- NB: Lean is sensitive to the specifics of this inductive definition.
      -- For example, merging `field_layouts` and `field_offs` into one function
      -- returning a pair is not possible, as that prevents Lean from seeing that
      -- the inductive is strictly positive.
      (field_layouts : (idx : Nat) → (h : idx < ts.length) → Layout ts[idx])
      (sa : SizeAndAlign) :
      Layout (.tuple ts f)
  | enum
      (variant_tags : (idx : Nat) → idx < vs.length → List TagToWrite)
      (variant_layouts : (idx : Nat) → (h : idx < vs.length) → Layout vs[idx])
      (discr : Discriminator)
      (sa : SizeAndAlign) :
      Layout (.enum vs f)

namespace Layout

@[implicit_reducible]
def size : {ty : MType} → Layout ty → Nat
  | _, .int sa _ => sa.size
  | _, .tuple _ _ sa => sa.size
  | _, .enum _ _ _ sa => sa.size

def size_and_align : {ty : MType} → Layout ty → SizeAndAlign
  | _, .int sa _ => sa
  | _, .tuple _ _ sa => sa
  | _, .enum _ _ _ sa => sa

@[simp, grind =] lemma size_known (l : Layout ty) : l.size_and_align.size = l.size :=
  by cases l <;> simp [size, size_and_align]

grind_pattern size_known => l.size_and_align
grind_pattern size_known => l.size

@[simp, grind =] lemma int_size (ty : IUScalarTy) sa h : (@Layout.int ty sa h).size = sa.size := rfl
@[simp, grind =] lemma tuple_size {ts f} fo fl sa : (@Layout.tuple ts f fo fl sa).size = sa.size := rfl
@[simp, grind =] lemma enum_size {vs f} vt vl d sa : (@Layout.enum vs f vt vl d sa).size = sa.size := rfl

@[simp, grind =] lemma int_size_and_align (ty : IUScalarTy) sa h : (@Layout.int ty sa h).size_and_align = sa := rfl
@[simp, grind =] lemma tuple_size_and_align ty f ts fo sa : (@Layout.tuple ty f ts fo sa).size_and_align = sa := rfl
@[simp, grind =] lemma enum_size_and_align ty f vt vl d sa : (@Layout.enum ty f vt vl d sa).size_and_align = sa := rfl

end Layout

end Aeneas
