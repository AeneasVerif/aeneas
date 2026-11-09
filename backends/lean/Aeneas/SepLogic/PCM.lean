module
public import Aeneas.SepLogic.Resource
public section

/-! Partial commutative monoids, and the order "is a part of" (`Subheap`) on which the assertions of
the separation logic are upward closed. -/

namespace Aeneas

universe u

/-- A partial commutative monoid: a total `∪`, meaningful on `Compatible` inputs. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

namespace PartialCommMonoid

variable {α : Type u} [EmptyCollection α] [Union α] [PartialCommMonoid α]

/-- `h'` is `h` extended with a compatible part. -/
def Subheap (h h' : α) : Prop :=
  ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest

theorem subheap_iff {h h' : α} :
    Subheap h h' ↔ ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest :=
  Iff.rfl

namespace Subheap

@[refl]
theorem refl (h : α) : Subheap h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : α} (hSub₁₂ : Subheap h₁ h₂)
    (hSub₂₃ : Subheap h₂ h₃) : Subheap h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : α) : Subheap ∅ h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Subheap h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Subheap h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

theorem split {h₁ h₂ h' : α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Subheap (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Subheap h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

theorem compatible {h h' frame : α} (hSub : Subheap h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

theorem union_mono_left {h h' frame : α} (hSub : Subheap h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Subheap (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

theorem union_mono {A B h₁ h₂ : α}
    (hSub₁ : Subheap A h₁) (hSub₂ : Subheap B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Subheap (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    hSub₁.compatible hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (hSub₂.compatible
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Subheap (B ∪ A) (h₂ ∪ A) :=
    Subheap.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Subheap (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Subheap.union_mono_left hSub₁ hCompatible)

end Subheap

end PartialCommMonoid

end Aeneas

namespace Aeneas.SepLogic

open Aeneas.Std

/-- The fragments of the byte heap (sets of resources) form a partial commutative monoid: two
fragments are compatible if they are disjoint. -/
instance : PartialCommMonoid Fragment where
  Compatible := Fragment.Disjoint
  compatible_comm := Fragment.Disjoint.symm
  compatible_empty_left := Fragment.disjoint_empty_left
  compatible_assoc a b c := by
    simp only [Fragment.disjoint_union_left, Fragment.disjoint_union_right]
    constructor
    · rintro ⟨hab, hac, hbc⟩
      exact ⟨hbc, hab, hac⟩
    · rintro ⟨hbc, hab, hac⟩
      exact ⟨hab, hac, hbc⟩
  union_assoc _ _ := Fragment.union_assoc _ _ _
  empty_union := Fragment.empty_union
  union_empty := Fragment.union_empty
  union_comm_of_compatible _ := Fragment.union_comm _ _

/-- A fragment is determined by its union with a disjoint fragment: no resource is compatible with
itself. -/
theorem Fragment.eq_of_union_eq {h₁ h₂ frame : Fragment}
    (hDisjoint₁ : h₁.Disjoint frame) (hDisjoint₂ : h₂.Disjoint frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) : h₁ = h₂ := by
  have half {a b : Fragment} (ha : a.Disjoint frame) (hEq : a ∪ frame = b ∪ frame) :
      ∀ r, a r → b r := by
    intro r hr
    have : (b ∪ frame) r := hEq ▸ (Or.inl hr : (a ∪ frame) r)
    rcases this with hb | hf
    · exact hb
    · exact absurd (ha r hr r hf) (Resource.not_compatible_self r)
  funext r
  exact propext ⟨half hDisjoint₁ hEq r, half hDisjoint₂ hEq.symm r⟩

theorem Fragment.exists_subheap_of_union_eq {h₁ h₂ frame : Fragment}
    (hCompatible₁ : PartialCommMonoid.Compatible h₁ frame)
    (hCompatible₂ : PartialCommMonoid.Compatible h₂ frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) :
    ∃ h, PartialCommMonoid.Compatible h frame ∧ h ∪ frame = h₁ ∪ frame ∧
      PartialCommMonoid.Subheap h₁ h ∧ PartialCommMonoid.Subheap h₂ h := by
  have h12 := Fragment.eq_of_union_eq hCompatible₁ hCompatible₂ hEq
  subst h12
  exact ⟨h₁, hCompatible₁, rfl, PartialCommMonoid.Subheap.refl _,
    PartialCommMonoid.Subheap.refl _⟩

end Aeneas.SepLogic
