module
public import Aeneas.SepLogic.IProp
@[expose] public section

namespace Aeneas.SepLogic

universe u

open Aeneas.Std (Heap Loc)

theorem entails_refl (H : IProp) : H ⊢ H :=
  fun _ hH => hH

theorem entails_trans {P Q R : IProp} (hPQ : P ⊢ Q) (hQR : Q ⊢ R) :
    P ⊢ R :=
  fun h hP => hQR h (hPQ h hP)

theorem entails_of_eq {P Q : IProp} (hEq : P = Q) : P ⊢ Q := by
  subst Q
  exact entails_refl P

theorem entails_antisymm {P Q : IProp} (hPQ : P ⊢ Q) (hQP : Q ⊢ P) : P = Q :=
  IProp.ext fun h => ⟨hPQ h, hQP h⟩

theorem iand_intro {H P Q : IProp} (hP : H ⊢ P) (hQ : H ⊢ Q) :
    H ⊢ iprop(P ∧ Q) :=
  fun heap hH => ⟨hP heap hH, hQ heap hH⟩

theorem iand_elim_left {P Q : IProp} : iprop(P ∧ Q) ⊢ P :=
  fun _ h => h.1

theorem iand_elim_right {P Q : IProp} : iprop(P ∧ Q) ⊢ Q :=
  fun _ h => h.2

theorem iand_mono {P₁ P₂ Q₁ Q₂ : IProp} (hP : P₁ ⊢ P₂) (hQ : Q₁ ⊢ Q₂) :
    iprop(P₁ ∧ Q₁) ⊢ iprop(P₂ ∧ Q₂) :=
  iand_intro (entails_trans iand_elim_left hP) (entails_trans iand_elim_right hQ)

theorem iand_comm (P Q : IProp) : iprop(P ∧ Q) = iprop(Q ∧ P) :=
  entails_antisymm (iand_intro iand_elim_right iand_elim_left)
    (iand_intro iand_elim_right iand_elim_left)

theorem iand_assoc (P Q R : IProp) : iprop((P ∧ Q) ∧ R) = iprop(P ∧ (Q ∧ R)) :=
  entails_antisymm (fun _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

@[simp]
theorem iand_self_eq (P : IProp) : iprop(P ∧ P) = P :=
  entails_antisymm iand_elim_left (iand_intro (entails_refl P) (entails_refl P))

@[simp]
theorem iand_ipure_eq (P Q : Prop) : iprop(⌜P⌝ ∧ ⌜Q⌝) = ⌜P ∧ Q⌝ :=
  rfl

theorem sep_assoc_eq (H₁ H₂ H₃ : IProp) :
    ((H₁ ∗ H₂) ∗ H₃) = (H₁ ∗ (H₂ ∗ H₃)) := by
  apply entails_antisymm
  · intro h
    rintro ⟨h₁₂, h₃, hDisjoint₁₂₃, hEq, hStar₁₂, hH₃⟩
    rcases hStar₁₂ with ⟨h₁, h₂, hDisjoint₁₂, hEq₁₂, hH₁, hH₂⟩
    have hDisjoint₁₂₃' :
        PartialCommMonoid.Compatible (h₁ ∪ h₂) h₃ := by
      rw [← hEq₁₂]; exact hDisjoint₁₂₃
    have ⟨hDisjoint₂₃, hDisjoint₁₂₃''⟩ :=
      (PartialCommMonoid.compatible_assoc h₁ h₂ h₃).mp
        ⟨hDisjoint₁₂, hDisjoint₁₂₃'⟩
    refine ⟨h₁, h₂ ∪ h₃, ?_, ?_, hH₁, ?_⟩
    · exact hDisjoint₁₂₃''
    · calc
        h = h₁₂ ∪ h₃ := hEq
        _ = (h₁ ∪ h₂) ∪ h₃ := congrArg (· ∪ h₃) hEq₁₂
        _ = h₁ ∪ (h₂ ∪ h₃) :=
          PartialCommMonoid.union_assoc hDisjoint₁₂ hDisjoint₁₂₃'
    · exact ⟨h₂, h₃, hDisjoint₂₃, rfl, hH₂, hH₃⟩
  · intro h
    rintro ⟨h₁, h₂₃, hDisjoint₁₂₃, hEq, hH₁, hStar₂₃⟩
    rcases hStar₂₃ with ⟨h₂, h₃, hDisjoint₂₃, hEq₂₃, hH₂, hH₃⟩
    have hDisjoint₁₂₃' :
        PartialCommMonoid.Compatible h₁ (h₂ ∪ h₃) := by
      rw [← hEq₂₃]; exact hDisjoint₁₂₃
    have ⟨hDisjoint₁₂, hDisjoint₁₂₃''⟩ :=
      (PartialCommMonoid.compatible_assoc h₁ h₂ h₃).mpr
        ⟨hDisjoint₂₃, hDisjoint₁₂₃'⟩
    refine ⟨h₁ ∪ h₂, h₃, hDisjoint₁₂₃'', ?_, ?_, hH₃⟩
    · calc
        h = h₁ ∪ h₂₃ := hEq
        _ = h₁ ∪ (h₂ ∪ h₃) := congrArg (h₁ ∪ ·) hEq₂₃
        _ = (h₁ ∪ h₂) ∪ h₃ :=
          (PartialCommMonoid.union_assoc
            hDisjoint₁₂ hDisjoint₁₂₃'').symm
    · exact ⟨h₁, h₂, hDisjoint₁₂, rfl, hH₁, hH₂⟩

theorem sep_comm_eq (H₁ H₂ : IProp) :
    (H₁ ∗ H₂) = (H₂ ∗ H₁) := by
  apply entails_antisymm
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, hEq, hH₁, hH₂⟩
    exact ⟨h₂, h₁, PartialCommMonoid.compatible_comm (α := Heap) hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₂, hH₁⟩
  · intro h
    rintro ⟨h₂, h₁, hDisjoint, hEq, hH₂, hH₁⟩
    exact ⟨h₁, h₂, PartialCommMonoid.compatible_comm (α := Heap) hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₁, hH₂⟩

instance : Std.Associative sep where
  assoc := sep_assoc_eq

instance : Std.Commutative sep where
  comm := sep_comm_eq

theorem sep_mono {P₁ P₂ Q₁ Q₂ : IProp}
    (hP : P₁ ⊢ P₂) (hQ : Q₁ ⊢ Q₂) :
    P₁ ∗ Q₁ ⊢ P₂ ∗ Q₂ := by
  intro h
  rintro ⟨h₁, h₂, hDisjoint, hEq, hP₁, hQ₁⟩
  exact ⟨h₁, h₂, hDisjoint, hEq, hP h₁ hP₁, hQ h₂ hQ₁⟩

@[simp]
theorem sep_emp_l_eq (H : IProp) :
    (emp ∗ H) = H := by
  apply entails_antisymm
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, rfl, -, hH⟩
    exact H.up_closed hH (Heap.Sub.union_right hDisjoint)
  · intro h hH
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, trivial, hH⟩

@[simp]
theorem sep_emp_r_eq (H : IProp) :
    (H ∗ emp) = H := by
  rw [sep_comm_eq, sep_emp_l_eq]

@[simp]
theorem ipure_true_eq_emp : (⌜True⌝ : IProp) = emp :=
  rfl

instance : Std.LawfulIdentity sep emp where
  left_id := sep_emp_l_eq
  right_id := sep_emp_r_eq

/-- Affinity: every assertion may be discarded. -/
@[simp]
theorem entails_emp_r (H : IProp) : H ⊢ emp :=
  fun _ _ => trivial

@[simp]
theorem emp_holds (h : Heap) : (emp : IProp) h ↔ True :=
  Iff.rfl

@[simp]
theorem pure_holds {P : Prop} (h : Heap) : (⌜P⌝ : IProp) h ↔ P :=
  Iff.rfl

@[simp]
theorem iand_holds (P Q : IProp) (h : Heap) : iprop(P ∧ Q) h ↔ P h ∧ Q h :=
  Iff.rfl

theorem entails_emp_ipure_iff (P : Prop) : (emp ⊢ ⌜P⌝) ↔ P := by
  constructor
  · intro h
    exact h ∅ trivial
  · intro h _ _
    exact h

@[simp]
theorem entails_ipure_iff (P Q : Prop) : (⌜P⌝ ⊢ ⌜Q⌝) ↔ (P → Q) :=
  ⟨fun h hP => h ∅ hP, fun h _ hP => h hP⟩

theorem owns_union (A B : Heap)
    (hCompatible : PartialCommMonoid.Compatible A B) :
    owns (A ∪ B) = (owns A ∗ owns B) := by
  apply entails_antisymm
  · rintro h ⟨rest, hCompatibleRest, rfl⟩
    obtain ⟨hCompatibleBRest, hCompatibleARest⟩ :=
      (PartialCommMonoid.compatible_assoc A B rest).mp
        ⟨hCompatible, hCompatibleRest⟩
    exact ⟨A, B ∪ rest, hCompatibleARest,
      PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
      Heap.Sub.refl _, Heap.Sub.union_left hCompatibleBRest⟩
  · rintro h ⟨h₁, h₂, hCompatibleHeaps, rfl, hSub₁, hSub₂⟩
    exact Heap.Sub.union_mono hSub₁ hSub₂ hCompatibleHeaps

theorem owns_singleton_exclusive {α : Type} (l : Loc) (value₁ value₂ : α) :
    owns (Heap.singleton l value₁) ∗ owns (Heap.singleton l value₂) ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hSingle₁, hSingle₂⟩
  exact Heap.disjoint_contains_false hCompatible (Heap.contains_of_sub hSingle₁)
    (Heap.contains_of_sub hSingle₂)

theorem sep_holds (H₁ H₂ : IProp) (h : Heap) :
    (H₁ ∗ H₂) h ↔
      ∃ h₁ h₂, PartialCommMonoid.Compatible h₁ h₂ ∧
        h = h₁ ∪ h₂ ∧ H₁ h₁ ∧ H₂ h₂ :=
  Iff.rfl

theorem sep_owns_holds (P : IProp) (frame heap : Heap) :
    (P ∗ owns frame) heap ↔
      ∃ owned, PartialCommMonoid.Compatible owned frame ∧
        heap = owned ∪ frame ∧ P owned := by
  constructor
  · rintro ⟨owned, _, hCompatible, rfl, hP, rest, hFrameRest, rfl⟩
    have hCompatible' : PartialCommMonoid.Compatible owned (rest ∪ frame) := by
      rwa [← PartialCommMonoid.union_comm_of_compatible (α := Heap) hFrameRest]
    obtain ⟨hOwnedRest, hCombined⟩ :=
      (PartialCommMonoid.compatible_assoc owned rest frame).mpr
        ⟨PartialCommMonoid.compatible_comm hFrameRest, hCompatible'⟩
    refine ⟨owned ∪ rest, hCombined, ?_, P.up_closed hP (Heap.Sub.union_left hOwnedRest)⟩
    rw [PartialCommMonoid.union_comm_of_compatible (α := Heap) hFrameRest,
      PartialCommMonoid.union_assoc hOwnedRest hCombined]
  · rintro ⟨owned, hCompatible, rfl, hP⟩
    exact ⟨owned, frame, hCompatible, rfl, hP, Heap.Sub.refl frame⟩

theorem sep_iand_owns (P Q : IProp) (frame : Heap) :
    (iprop(P ∧ Q) ∗ owns frame) = iprop((P ∗ owns frame) ∧ (Q ∗ owns frame)) := by
  apply entails_antisymm
  · exact iand_intro
      (sep_mono iand_elim_left (entails_refl _))
      (sep_mono iand_elim_right (entails_refl _))
  · intro heap ⟨hP, hQ⟩
    obtain ⟨owned₁, hCompatible₁, hEq₁, hP⟩ := (sep_owns_holds P frame heap).mp hP
    obtain ⟨owned₂, hCompatible₂, hEq₂, hQ⟩ := (sep_owns_holds Q frame heap).mp hQ
    have hEq := Heap.union_right_cancel hCompatible₁ hCompatible₂ (hEq₁.symm.trans hEq₂)
    subst owned₂
    exact ⟨owned₁, frame, hCompatible₁, hEq₁, ⟨hP, hQ⟩, Heap.Sub.refl frame⟩

theorem exists_holds {ι : Sort _} (J : ι → IProp) (h : Heap) :
    iexists J h ↔ ∃ x, J x h :=
  Iff.rfl

theorem sep_pure_l (P : Prop) (H : IProp) (h : Heap) :
    (⌜P⌝ ∗ H) h ↔ P ∧ H h := by
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, rfl, hP, hH⟩
    exact ⟨hP, H.up_closed hH (Heap.Sub.union_right hDisjoint)⟩
  · rintro ⟨hP, hH⟩
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, hP, hH⟩

theorem pure_sep_intro {P : Prop} (H : IProp) (hP : P) :
    H ⊢ ⌜P⌝ ∗ H := by
  intro h hH
  exact (sep_pure_l P H h).mpr ⟨hP, hH⟩

theorem entails_pure_l {P : Prop} {H H' : IProp} (h : P → H ⊢ H') :
    ⌜P⌝ ∗ H ⊢ H' := by
  intro heap hStar
  have ⟨hP, hH⟩ := (sep_pure_l P H heap).mp hStar
  exact h hP heap hH

theorem entails_exists_l {ι : Sort _} {H : IProp} {J : ι → IProp}
    (h : ∀ x, J x ⊢ H) : iexists J ⊢ H :=
  fun heap hJ => h hJ.choose heap hJ.choose_spec

/-- `iframe` uses this with a metavariable witness, instantiated by cancellation. -/
theorem entails_exists_r {ι : Sort _} {H : IProp} {J : ι → IProp} (x : ι)
    (h : H ⊢ J x) : H ⊢ iexists J :=
  fun heap hH => ⟨x, h heap hH⟩

theorem entails_exists_frame {ι : Sort _} {R : IProp} {J F : ι → IProp}
    (h : ∀ x, J x ⊢ R ∗ F x) : iexists J ⊢ R ∗ iexists F :=
  entails_exists_l fun x =>
    entails_trans (h x) (sep_mono (entails_refl R) (entails_exists_r x (entails_refl _)))

theorem sep_exists_l_eq {ι : Sort _} (J : ι → IProp) (H : IProp) :
    (iexists J ∗ H) = iprop(∃ x, J x ∗ H) := by
  apply entails_antisymm
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩
    exact ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
  · intro h
    rintro ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
    exact ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩

theorem sep_exists_r_eq {ι : Sort _} (H : IProp) (J : ι → IProp) :
    (H ∗ iexists J) = iprop(∃ x, H ∗ J x) := by
  rw [sep_comm_eq, sep_exists_l_eq]
  congr 1
  funext x
  exact sep_comm_eq _ _

theorem entails_exists_sep_l {ι : Sort _} {H H' : IProp} {J : ι → IProp}
    (h : ∀ x, J x ∗ H ⊢ H') : iexists J ∗ H ⊢ H' := by
  rw [sep_exists_l_eq]
  exact entails_exists_l h

theorem entails_exists_sep_r {ι : Sort _} {H H' : IProp} {J : ι → IProp} (x : ι)
    (h : H ⊢ J x ∗ H') : H ⊢ iexists J ∗ H' := by
  rw [sep_exists_l_eq]
  exact entails_exists_r x h

theorem sep_elim_right (P F : IProp) :
    P ∗ F ⊢ P :=
  entails_trans (sep_mono (entails_refl P) (entails_emp_r F))
    (entails_of_eq (sep_emp_r_eq P))

theorem sep_elim_left (P F : IProp) :
    F ∗ P ⊢ P :=
  entails_trans (entails_of_eq (sep_comm_eq F P)) (sep_elim_right P F)

theorem forall_intro {ι : Sort _} {H : IProp} {J : ι → IProp}
    (h : ∀ x, H ⊢ J x) : H ⊢ iforall J :=
  fun heap hH x => h x heap hH

theorem forall_specialize {ι : Sort _} {J : ι → IProp} (x : ι) :
    iforall J ⊢ J x :=
  fun _ hJ => hJ x

/-- The wand is right adjoint to `∗`. -/
theorem wand_equiv (H₀ H₁ H₂ : IProp) :
    (H₀ ⊢ H₁ -∗ H₂) ↔ (H₁ ∗ H₀ ⊢ H₂) := by
  constructor
  · rintro hWand heap ⟨h₁, h₀, hDisjoint, rfl, hH₁, hH₀⟩
    have hApplied :=
      hWand h₀ hH₀ h₁
        (PartialCommMonoid.compatible_comm (α := Heap) hDisjoint) hH₁
    rwa [PartialCommMonoid.union_comm_of_compatible
      (PartialCommMonoid.compatible_comm (α := Heap) hDisjoint)] at hApplied
  · intro hStar h₀ hH₀ h₁ hDisjoint hH₁
    exact hStar (h₀ ∪ h₁)
      ⟨h₁, h₀, PartialCommMonoid.compatible_comm (α := Heap) hDisjoint,
        PartialCommMonoid.union_comm_of_compatible hDisjoint, hH₁, hH₀⟩

theorem wand_intro {H₀ H₁ H₂ : IProp} (h : H₁ ∗ H₀ ⊢ H₂) : H₀ ⊢ H₁ -∗ H₂ :=
  (wand_equiv H₀ H₁ H₂).mpr h

theorem wand_cancel (H₁ H₂ : IProp) : H₁ ∗ (H₁ -∗ H₂) ⊢ H₂ :=
  (wand_equiv (H₁ -∗ H₂) H₁ H₂).mp (entails_refl _)

theorem wand_mono {H₁ H₁' H₂ H₂' : IProp} (h₁ : H₁' ⊢ H₁) (h₂ : H₂ ⊢ H₂') :
    (H₁ -∗ H₂) ⊢ (H₁' -∗ H₂') :=
  wand_intro (entails_trans (sep_mono h₁ (entails_refl _))
    (entails_trans (wand_cancel H₁ H₂) h₂))

theorem postWand_equiv {α : Type u} (H : IProp) (Q₁ Q₂ : IPost α) :
    (H ⊢ Q₁ -∗+ Q₂) ↔ (Q₁ ∗+ H ⊢+ Q₂) := by
  constructor
  · intro h value
    exact entails_trans (sep_mono (entails_refl _)
      (entails_trans h (forall_specialize value)))
      (wand_cancel (Q₁ value) (Q₂ value))
  · intro h
    exact forall_intro fun value =>
      wand_intro (h value)

theorem postWand_intro {α : Type u} {H : IProp} {Q₁ Q₂ : IPost α}
    (h : Q₁ ∗+ H ⊢+ Q₂) : H ⊢ Q₁ -∗+ Q₂ :=
  (postWand_equiv H Q₁ Q₂).mpr h

theorem postWand_cancel {α : Type u} (Q₁ Q₂ : IPost α) :
    Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  (postWand_equiv (Q₁ -∗+ Q₂) Q₁ Q₂).mp (entails_refl _)

theorem postWand_specialize {α : Type u} {Q₁ Q₂ : IPost α} (value : α) :
    (Q₁ -∗+ Q₂) ⊢ (Q₁ value -∗ Q₂ value) :=
  forall_specialize value

theorem entails_postWand_pure_eq {α : Type u} (H : IProp) (value : α) (Q : IPost α) :
    (H ⊢ (fun result => ⌜result = value⌝) -∗+ Q) ↔ (H ⊢ Q value) := by
  rw [postWand_equiv]
  constructor
  · intro h
    exact entails_trans (pure_sep_intro (P := value = value) H rfl) (h value)
  · intro h _
    exact entails_pure_l fun hEq => hEq ▸ h

theorem entails_emp_postWand_ipure_iff {α : Type u} (P Q : α → Prop) :
    (emp ⊢ (fun value => ⌜P value⌝) -∗+ fun value => ⌜Q value⌝) ↔
      ∀ value, P value → Q value := by
  rw [postWand_equiv]
  constructor
  · intro h value hP
    exact h value ∅ ((entails_of_eq (sep_emp_r_eq ⌜P value⌝).symm) ∅ hP)
  · intro h value heap hPre
    exact h value ((entails_of_eq (sep_emp_r_eq ⌜P value⌝)) heap hPre)

end Aeneas.SepLogic
