import Aeneas.Std.Heap

/-!
# Iris-compatible first-order separation logic

The affine, first-order separation logic Aeneas verification is built on. Its
public vocabulary and notation follow Iris-Lean. It deliberately does not import
Iris-Lean or instantiate Iris-Lean with Aeneas's model. A client can switch
implementations by changing its import while continuing to use the `IProp`,
`iprop(...)`, `∗`, `-∗`, `⊢`, `⊣⊢`, and `↦` surface.

The logic is *affine*, as Iris's is: an assertion owns the cells it describes
and says nothing about the rest of the heap, so `emp` is the affine top and the
entailment `⊢` weakens — `H ⊢ emp` for every `H`.  Resources may therefore be
discarded anywhere.  Following Iris's `uPred`, affinity is a property of the
*model*:
`IProp` bundles closure under `Heap.Sub`, which is what makes `emp ∗ H ⊣⊢ H`
provable once `emp` holds of every heap.

The predicate transformers built on these assertions are in
`Aeneas.SepLogic.PredicateTransformer`, and the proof-mode tactics (`iframe`,
`iintro`, `isimpl`, `irewrite`) in `Aeneas.Tactic.SepLogic`.
-/

namespace Aeneas.SepLogic

universe u

open Aeneas.Std (Heap Ref)

open Aeneas.Std (Heap Ref)

/-- Heap predicates describe heap fragments.  Like Iris's `uPred`, an assertion
is closed under heap extension: it constrains the cells it owns, and says
nothing about the others. -/
structure IProp where
  holds : Heap → Prop
  up_closed : ∀ {h h' : Heap}, holds h → Heap.Sub h h' → holds h'

instance : CoeFun IProp (fun _ => Heap → Prop) :=
  ⟨IProp.holds⟩

@[ext]
theorem IProp.ext {H₁ H₂ : IProp} (hIff : ∀ h, H₁ h ↔ H₂ h) : H₁ = H₂ := by
  obtain ⟨holds₁, _⟩ := H₁
  obtain ⟨holds₂, _⟩ := H₂
  have hEq : holds₁ = holds₂ := funext fun h => propext (hIff h)
  subst hEq
  rfl

/- Preconditions are separation-logic propositions. -/
abbrev IPre := IProp

/- Postconditions describe both a returned value and a heap fragment. -/
abbrev IPost (α : Type u) := α → IProp

def Entails (H₁ H₂ : IProp) : Prop :=
  ∀ h, H₁ h → H₂ h

structure BiEntails (H₁ H₂ : IProp) : Prop where
  mp : Entails H₁ H₂
  mpr : Entails H₂ H₁

/-- The empty assertion owns nothing.  Being affine it holds of *every* heap,
exactly like Iris's `emp`, which coincides with `True` there. -/
def emp : IProp where
  holds _ := True
  up_closed := fun _ _ => trivial

/-- A pure fact owns nothing, so it says nothing about the heap it is asserted
of. -/
def ipure (P : Prop) : IProp where
  holds _ := P
  up_closed := fun hP _ => hP

/-- The assertion that owns the heap fragment `A`.  Being affine it says
nothing about the slots `A` does not describe, which is exactly closure under
`Heap.Sub`. -/
def owns (A : Heap) : IProp where
  holds h := Heap.Sub A h
  up_closed := fun hSub hExtend => hSub.trans hExtend

/-- The points-to assertion of a reference: the heap owns the slot `r`, and it
holds `value`. -/
def Ref.pointsTo {α : Type} (r : Ref α) (value : α) : IProp :=
  owns (Heap.singleton r value)

/-- What `↦` means, overloaded: a reference points to the slot it names, a
pointer to the value it addresses, and a buffer to the values it spans. -/
class PointsTo (ρ : Type u) (β : outParam (Type v)) where
  pointsTo : ρ → β → IProp

instance instPointsToRef {α : Type} : PointsTo (Ref α) α :=
  ⟨Ref.pointsTo⟩

def sep (H₁ H₂ : IProp) : IProp where
  holds h :=
    ∃ h₁ h₂,
      PartialCommMonoid.Compatible h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      H₁ h₁ ∧
      H₂ h₂
  up_closed := by
    rintro h h' ⟨h₁, h₂, hDisjoint, rfl, hH₁, hH₂⟩ hExtend
    obtain ⟨h₂', hDisjoint', rfl, hExtend'⟩ := Heap.Sub.split hDisjoint hExtend
    exact ⟨h₁, h₂', hDisjoint', rfl, hH₁, H₂.up_closed hH₂ hExtend'⟩

def iexists {α : Sort _} (J : α → IProp) : IProp where
  holds h := ∃ x, J x h
  up_closed := fun ⟨x, hJ⟩ hExtend => ⟨x, (J x).up_closed hJ hExtend⟩

def postSep {α : Type u} (Q : IPost α) (H : IProp) :
    IPost α :=
  fun value => sep (Q value) H

def postEntails {α : Type u} (Q₁ Q₂ : IPost α) : Prop :=
  ∀ value, Entails (Q₁ value) (Q₂ value)

syntax:max "iprop(" term ")" : term
notation "emp" => emp
syntax "⌜" term "⌝" : term
macro_rules
  | `(⌜$P⌝) => `(ipure $P)
macro_rules
  | `(iprop(∃ $x:ident, $H)) => `(iexists fun $x => iprop($H))
  | `(iprop(∃ $x:ident : $type, $H)) =>
      `(iexists fun ($x : $type) => iprop($H))
  | `(iprop(∃ ($x:ident : $type), $H)) =>
      `(iexists fun ($x : $type) => iprop($H))
  | `(iprop($H)) => `($H)
infixr:35 " ∗ " => sep
infixr:40 " ∗+ " => postSep
syntax:25 term:29 " ⊢ " term:25 : term
syntax:25 term:29 " ⊢+ " term:25 : term
syntax:25 term:29 " ⊣⊢ " term:29 : term
macro_rules
  | `($P ⊢ $Q) => `(Entails $P $Q)
  | `($P ⊢+ $Q) => `(postEntails $P $Q)
  | `($P ⊣⊢ $Q) => `(BiEntails $P $Q)
notation:50 r:50 " ↦ " value:50 => PointsTo.pointsTo r value

theorem entails_refl (H : IProp) : H ⊢ H :=
  fun _ hH => hH

theorem entails_trans {P Q R : IProp} (hPQ : P ⊢ Q) (hQR : Q ⊢ R) :
    P ⊢ R :=
  fun h hP => hQR h (hPQ h hP)

theorem entails_of_eq {P Q : IProp} (hEq : P = Q) : P ⊢ Q := by
  subst Q
  exact entails_refl P

theorem bientails_eq {P Q : IProp} (hEquiv : P ⊣⊢ Q) : P = Q :=
  IProp.ext fun h => ⟨hEquiv.mp h, hEquiv.mpr h⟩

theorem sep_assoc (H₁ H₂ H₃ : IProp) :
    (H₁ ∗ H₂) ∗ H₃ ⊣⊢ H₁ ∗ (H₂ ∗ H₃) := by
  constructor
  · intro h
    rintro ⟨h₁₂, h₃, hDisjoint₁₂₃, hEq, hStar₁₂, hH₃⟩
    rcases hStar₁₂ with ⟨h₁, h₂, hDisjoint₁₂, hEq₁₂, hH₁, hH₂⟩
    have hDisjoint₁₂₃' :
        PartialCommMonoid.Compatible (h₁ ∪ h₂) h₃ := by
      simpa [hEq₁₂] using hDisjoint₁₂₃
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
      simpa [hEq₂₃] using hDisjoint₁₂₃
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

theorem sep_comm (H₁ H₂ : IProp) :
    H₁ ∗ H₂ ⊣⊢ H₂ ∗ H₁ := by
  constructor
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, hEq, hH₁, hH₂⟩
    exact ⟨h₂, h₁, PartialCommMonoid.compatible_comm hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₂, hH₁⟩
  · intro h
    rintro ⟨h₂, h₁, hDisjoint, hEq, hH₂, hH₁⟩
    exact ⟨h₁, h₂, PartialCommMonoid.compatible_comm hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₁, hH₂⟩

theorem sep_assoc_eq (H₁ H₂ H₃ : IProp) :
    ((H₁ ∗ H₂) ∗ H₃) = (H₁ ∗ (H₂ ∗ H₃)) :=
  bientails_eq (sep_assoc H₁ H₂ H₃)

theorem sep_comm_eq (H₁ H₂ : IProp) :
    (H₁ ∗ H₂) = (H₂ ∗ H₁) :=
  bientails_eq (sep_comm H₁ H₂)

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

theorem sep_emp_l (H : IProp) :
    emp ∗ H ⊣⊢ H := by
  constructor
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, rfl, -, hH⟩
    exact H.up_closed hH (Heap.Sub.union_right hDisjoint)
  · intro h hH
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, trivial, hH⟩

theorem sep_emp_r (H : IProp) :
    H ∗ emp ⊣⊢ H := by
  exact ⟨
    entails_trans (sep_comm H emp).mp (sep_emp_l H).mp,
    entails_trans (sep_emp_l H).mpr (sep_comm H emp).mpr⟩

@[simp]
theorem sep_emp_l_eq (H : IProp) :
    (emp ∗ H) = H :=
  bientails_eq (sep_emp_l H)

theorem sep_emp_r_eq (H : IProp) :
    (H ∗ emp) = H :=
  bientails_eq (sep_emp_r H)

instance : Std.LawfulIdentity sep emp where
  left_id := sep_emp_l_eq
  right_id := sep_emp_r_eq

/-- Affinity: every assertion may be discarded, so the affine top is simply
`emp` here. -/
theorem entails_emp_r (H : IProp) : H ⊢ emp :=
  fun _ _ => trivial

/-! ### The model, spelled out

`H h` reduces to the right-hand sides below by `rfl`; these lemmas let `simp`
and `rw` see through the `IProp` structure when a proof does go down to the
heap. -/

@[simp]
theorem emp_holds (h : Heap) : (emp : IProp) h ↔ True :=
  Iff.rfl

@[simp]
theorem pure_holds {P : Prop} (h : Heap) : (⌜P⌝ : IProp) h ↔ P :=
  Iff.rfl

/-- An entailment from `emp` to a pure assertion is exactly the pure fact. -/
theorem entails_emp_ipure_iff (P : Prop) : (emp ⊢ ⌜P⌝) ↔ P := by
  constructor
  · intro h
    exact h ∅ trivial
  · intro h _ _
    exact h

theorem Ref.pointsTo_holds {α : Type} (r : Ref α) (value : α)
    (h : Heap) : (r ↦ value) h ↔ Heap.Sub (Heap.singleton r value) h :=
  Iff.rfl

/-- Splitting and joining a heap fragment: owning two compatible fragments is
owning their union.  Every range-splitting lemma of `MutableData/` is this one
applied to a run of slots. -/
theorem owns_union (A B : Heap)
    (hCompatible : PartialCommMonoid.Compatible A B) :
    owns (A ∪ B) ⊣⊢ owns A ∗ owns B := by
  constructor
  · rintro h ⟨rest, hCompatibleRest, rfl⟩
    obtain ⟨hCompatibleBRest, hCompatibleARest⟩ :=
      (PartialCommMonoid.compatible_assoc A B rest).mp
        ⟨hCompatible, hCompatibleRest⟩
    exact ⟨A, B ∪ rest, hCompatibleARest,
      PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
      Heap.Sub.refl _, Heap.Sub.union_left hCompatibleBRest⟩
  · rintro h ⟨h₁, h₂, hCompatibleHeaps, rfl, hSub₁, hSub₂⟩
    exact Heap.Sub.union_mono hSub₁ hSub₂ hCompatibleHeaps

/-- Points-to is exclusive: affinity lets resources be *dropped*, never
duplicated, so a slot still cannot be owned twice. -/
theorem Ref.pointsTo_exclusive {α : Type} (r : Ref α) (value₁ value₂ : α) :
    r ↦ value₁ ∗ r ↦ value₂ ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hSingle₁, hSingle₂⟩
  exact Heap.disjoint_contains_false hCompatible (Heap.contains_of_sub hSingle₁)
    (Heap.contains_of_sub hSingle₂)

theorem sep_holds (H₁ H₂ : IProp) (h : Heap) :
    (H₁ ∗ H₂) h ↔
      ∃ h₁ h₂, PartialCommMonoid.Compatible h₁ h₂ ∧
        h = h₁ ∪ h₂ ∧ H₁ h₁ ∧ H₂ h₂ :=
  Iff.rfl

theorem exists_holds {ι : Sort _} (J : ι → IProp) (h : Heap) :
    iexists J h ↔ ∃ x, J x h :=
  Iff.rfl

theorem sep_exists {α : Sort _} (J : α → IProp) (H : IProp) :
    iprop(∃ x, J x) ∗ H ⊣⊢ iprop(∃ x, J x ∗ H) := by
  constructor
  · intro h
    rintro ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩
    exact ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
  · intro h
    rintro ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
    exact ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩

/-- A pure fact on the left of a separating conjunction: since pure facts own
nothing, they can be read off, and put back, without touching the heap. -/
theorem sep_pure_l (P : Prop) (H : IProp) (h : Heap) :
    (⌜P⌝ ∗ H) h ↔ P ∧ H h := by
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, rfl, hP, hH⟩
    exact ⟨hP, H.up_closed hH (Heap.Sub.union_right hDisjoint)⟩
  · rintro ⟨hP, hH⟩
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, hP, hH⟩

@[simp]
theorem sep_ipure_true_l_eq (H : IProp) :
    (⌜True⌝ ∗ H) = H := by
  apply IProp.ext
  intro h
  simpa using sep_pure_l True H h

theorem pure_sep_intro {P : Prop} (H : IProp) (hP : P) :
    H ⊢ ⌜P⌝ ∗ H := by
  intro h hH
  exact (sep_pure_l P H h).mpr ⟨hP, hH⟩

/-- Extraction of a pure fact from the left-hand side of an entailment. -/
theorem entails_pure_l {P : Prop} {H H' : IProp} (h : P → H ⊢ H') :
    ⌜P⌝ ∗ H ⊢ H' := by
  intro heap hStar
  have ⟨hP, hH⟩ := (sep_pure_l P H heap).mp hStar
  exact h hP heap hH

/-- Introduction of an existential quantifier on the left-hand side of an
entailment. -/
theorem entails_exists_l {ι : Sort _} {H : IProp} {J : ι → IProp}
    (h : ∀ x, J x ⊢ H) : iexists J ⊢ H :=
  fun heap hJ => h hJ.choose heap hJ.choose_spec

/-- Instantiation of an existential quantifier on the right-hand side of an
entailment. `isimpl` uses it with a metavariable for `x`, which the cancellation
phase then instantiates by unification. -/
theorem entails_exists_r {ι : Sort _} {H : IProp} {J : ι → IProp} (x : ι)
    (h : H ⊢ J x) : H ⊢ iexists J :=
  fun heap hH => ⟨x, h heap hH⟩

/-- Float an existential out of the left factor of a separating conjunction. -/
theorem sep_exists_l_eq {ι : Sort _} (J : ι → IProp) (H : IProp) :
    (iexists J ∗ H) = iprop(∃ x, J x ∗ H) :=
  bientails_eq (sep_exists J H)

/-- Float an existential out of the right factor of a separating conjunction. -/
theorem sep_exists_r_eq {ι : Sort _} (H : IProp) (J : ι → IProp) :
    (H ∗ iexists J) = iprop(∃ x, H ∗ J x) := by
  rw [sep_comm_eq, sep_exists_l_eq]
  exact bientails_eq ⟨
    fun heap ⟨x, hx⟩ => ⟨x, (sep_comm (J x) H).mp heap hx⟩,
    fun heap ⟨x, hx⟩ => ⟨x, (sep_comm (J x) H).mpr heap hx⟩⟩

/-- Discard a pure fact. This is a special case of `entails_emp_r`. -/
theorem pure_elim (P : Prop) :
    ⌜P⌝ ⊢ emp :=
  entails_emp_r _

/-- Drop the right factor of a separating conjunction. Affinity makes the
discardability hypothesis (`F ⊢ emp`) vacuous. -/
theorem sep_elim_right (P F : IProp) :
    P ∗ F ⊢ P :=
  entails_trans (sep_mono (entails_refl P) (entails_emp_r F))
    (sep_emp_r P).mp

/-- Drop the left factor of a separating conjunction. -/
theorem sep_elim_left (P F : IProp) :
    F ∗ P ⊢ P :=
  entails_trans (sep_comm F P).mp (sep_elim_right P F)

/-! ## The magic wand

`H₁ -∗ H₂` describes the heap fragments that, extended with a disjoint fragment
satisfying `H₁`, satisfy `H₂`. In the affine model this Kripke-style reading is
the right adjoint of the separating conjunction. -/

/-- Universal quantification over heap predicates. -/
def iforall {ι : Sort _} (J : ι → IProp) : IProp where
  holds h := ∀ x, J x h
  up_closed := fun hJ hExtend x => (J x).up_closed (hJ x) hExtend

/-- Separating implication, or magic wand. -/
def wand (H₁ H₂ : IProp) : IProp where
  holds h :=
    ∀ h', PartialCommMonoid.Compatible h h' → H₁ h' → H₂ (h ∪ h')
  up_closed := by
    intro h hBig hWand hExtend h' hDisjoint hH₁
    have hDisjoint' : PartialCommMonoid.Compatible h h' :=
      Heap.Sub.disjoint_of_sub hExtend hDisjoint
    exact H₂.up_closed (hWand h' hDisjoint' hH₁)
      (Heap.Sub.union_mono_left hExtend hDisjoint)

/-- The magic wand between postconditions. Note that it is a heap predicate,
not a postcondition. -/
def postWand {α : Type u} (Q₁ Q₂ : IPost α) : IProp :=
  iforall fun value => wand (Q₁ value) (Q₂ value)

@[inherit_doc wand] infixr:25 " -∗ " => wand
@[inherit_doc postWand] infixr:25 " -∗+ " => postWand
macro_rules
  | `(iprop(∀ $x:ident, $H)) => `(iforall fun $x => iprop($H))
  | `(iprop(∀ $x:ident : $type, $H)) =>
      `(iforall fun ($x : $type) => iprop($H))
  | `(iprop(∀ ($x:ident : $type), $H)) =>
      `(iforall fun ($x : $type) => iprop($H))

theorem forall_intro {ι : Sort _} {H : IProp} {J : ι → IProp}
    (h : ∀ x, H ⊢ J x) : H ⊢ iforall J :=
  fun heap hH x => h x heap hH

theorem forall_specialize {ι : Sort _} {J : ι → IProp} (x : ι) :
    iforall J ⊢ J x :=
  fun _ hJ => hJ x

/-- The wand is the right adjoint of the separating conjunction. Every other
property of the wand follows from it. -/
theorem wand_equiv (H₀ H₁ H₂ : IProp) :
    (H₀ ⊢ H₁ -∗ H₂) ↔ (H₁ ∗ H₀ ⊢ H₂) := by
  constructor
  · rintro hWand heap ⟨h₁, h₀, hDisjoint, rfl, hH₁, hH₀⟩
    have hApplied :=
      hWand h₀ hH₀ h₁
        (PartialCommMonoid.compatible_comm hDisjoint) hH₁
    rwa [PartialCommMonoid.union_comm_of_compatible
      (PartialCommMonoid.compatible_comm hDisjoint)] at hApplied
  · intro hStar h₀ hH₀ h₁ hDisjoint hH₁
    exact hStar (h₀ ∪ h₁)
      ⟨h₁, h₀, PartialCommMonoid.compatible_comm hDisjoint,
        PartialCommMonoid.union_comm_of_compatible hDisjoint, hH₁, hH₀⟩

/-- Introduction rule for the wand. -/
theorem wand_intro {H₀ H₁ H₂ : IProp} (h : H₁ ∗ H₀ ⊢ H₂) : H₀ ⊢ H₁ -∗ H₂ :=
  (wand_equiv H₀ H₁ H₂).mpr h

/-- Elimination rule for the wand. -/
theorem wand_cancel (H₁ H₂ : IProp) : H₁ ∗ (H₁ -∗ H₂) ⊢ H₂ :=
  (wand_equiv (H₁ -∗ H₂) H₁ H₂).mp (entails_refl _)

theorem wand_mono {H₁ H₁' H₂ H₂' : IProp} (h₁ : H₁' ⊢ H₁) (h₂ : H₂ ⊢ H₂') :
    (H₁ -∗ H₂) ⊢ (H₁' -∗ H₂') :=
  wand_intro (entails_trans (sep_mono h₁ (entails_refl _))
    (entails_trans (wand_cancel H₁ H₂) h₂))

/-- The postcondition wand is right adjoint to postcondition separation. -/
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

/-- Introduction rule for a postcondition wand. -/
theorem postWand_intro {α : Type u} {H : IProp} {Q₁ Q₂ : IPost α}
    (h : Q₁ ∗+ H ⊢+ Q₂) : H ⊢ Q₁ -∗+ Q₂ :=
  (postWand_equiv H Q₁ Q₂).mpr h

/-- Elimination rule for a postcondition wand. -/
theorem postWand_cancel {α : Type u} (Q₁ Q₂ : IPost α) :
    Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  (postWand_equiv (Q₁ -∗+ Q₂) Q₁ Q₂).mp (entails_refl _)

/-- A postcondition wand yields a heap wand at every value. -/
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

/-- A postcondition wand between pure postconditions, owned from `emp`, is
pointwise implication between the underlying propositions. -/
theorem entails_emp_postWand_ipure_iff {α : Type u} (P Q : α → Prop) :
    (emp ⊢ (fun value => ⌜P value⌝) -∗+ fun value => ⌜Q value⌝) ↔
      ∀ value, P value → Q value := by
  rw [postWand_equiv]
  constructor
  · intro h value hP
    exact h value ∅ ((sep_emp_r ⌜P value⌝).mpr ∅ hP)
  · intro h value heap hPre
    exact h value ((sep_emp_r ⌜P value⌝).mp heap hPre)

end Aeneas.SepLogic
