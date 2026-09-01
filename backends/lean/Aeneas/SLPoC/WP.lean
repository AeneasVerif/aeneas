import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Heap
import AeneasMeta.Simp
import Lean.Meta.Tactic.AC

/-!
# Iris-compatible first-order separation logic and weakest preconditions

This is a standalone copy of `Aeneas.SLPoC.WP` whose public vocabulary and
notation follow Iris-Lean. It deliberately does not import Iris-Lean or
instantiate Iris-Lean with Aeneas's model. A client can switch implementations
by changing its import while continuing to use the `IProp`, `Wp`,
`iprop(...)`, `∗`, `-∗`, `⊢`, `⊣⊢`, and `↦` surface.

The logic is *affine*, as Iris's is: an assertion owns the cells it describes
and says nothing about the rest of the heap, so `emp` is the affine top and the
entailment `⊢` weakens — `H ⊢ emp` for every `H`.  Resources may therefore be
discarded anywhere.  Following Iris's `uPred`, affinity is a property of the
*model*:
`IProp` bundles closure under `Heap.Sub`, which is what makes `emp ∗ H ⊣⊢ H`
provable once `emp` holds of every heap.
-/

namespace Aeneas.SLPoC

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
abbrev IPost (α : Type) := α → IProp

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

/-- The points-to assertion of a PCM reference: the heap owns the fragment `x`
of the cell `r` names.  Being affine it says nothing about the rest of that
cell, which other assertions may own fragments of. -/
def Ref.pointsTo {α : Type} {p : PCM α} (r : Ref α p) (x : α) : IProp where
  holds h := Heap.Sub (singleton r x) h
  up_closed := fun hSub hExtend => hSub.trans hExtend

/-- What `↦` means, overloaded: a reference points to a fragment of its own
PCM, a pointer to the value it addresses, and a buffer to the values it
spans. -/
class PointsTo (ρ : Type u) (β : outParam (Type v)) where
  pointsTo : ρ → β → IProp

instance instPointsToRef {α : Type} {p : PCM α} : PointsTo (Ref α p) α :=
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

def postSep {α : Type} (Q : IPost α) (H : IProp) :
    IPost α :=
  fun value => sep (Q value) H

def postEntails {α : Type} (Q₁ Q₂ : IPost α) : Prop :=
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

theorem Ref.pointsTo_holds {α : Type} {p : PCM α} (r : Ref α p) (x : α)
    (h : Heap) : (r ↦ x) h ↔ Heap.Sub (singleton r x) h :=
  Iff.rfl

/-- Points-to is exclusive exactly as far as its PCM is: affinity lets
resources be *dropped*, never duplicated, so two fragments that do not compose
cannot both be owned. -/
theorem Ref.pointsTo_exclusive {α : Type} {p : PCM α} (r : Ref α p) (x y : α)
    (hNotComposable : ¬ p.Composable x y) :
    r ↦ x ∗ r ↦ y ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hSingle₁, hSingle₂⟩
  exact not_composable_incompatible hCompatible hSingle₁ hSingle₂
    hNotComposable

/-- Splitting and joining a cell: owning `p.op x y` is owning `x` and owning
`y` separately.  This is what PCM references are for — one allocation, several
disjoint owners. -/
theorem Ref.pointsTo_op {α : Type} {p : PCM α} (r : Ref α p) (x y : α)
    (hComposable : p.Composable x y) :
    r ↦ p.op x y ⊣⊢ r ↦ x ∗ r ↦ y := by
  have hCompatibleSingle := compatible_singleton_self (r := r) hComposable
  constructor
  · rintro h ⟨rest, hCompatible, rfl⟩
    rw [← singleton_union_singleton hComposable] at hCompatible ⊢
    obtain ⟨hCompatibleRest, hCompatibleRight⟩ :=
      (PartialCommMonoid.compatible_assoc (singleton r x) (singleton r y)
        rest).mp ⟨hCompatibleSingle, hCompatible⟩
    exact ⟨singleton r x, singleton r y ∪ rest, hCompatibleRight,
      PartialCommMonoid.union_assoc hCompatibleSingle hCompatible,
      Heap.Sub.refl _, Heap.Sub.union_left hCompatibleRest⟩
  · rintro h ⟨h₁, h₂, hCompatible, rfl, hSub₁, hSub₂⟩
    show Heap.Sub (singleton r (p.op x y)) (h₁ ∪ h₂)
    rw [← singleton_union_singleton hComposable]
    exact Heap.Sub.union_mono hSub₁ hSub₂ hCompatible

/-- Reading through a points-to assertion sees a value the owned fragment is a
fragment of: Pulse's `read` contract. -/
theorem Ref.compatible_of_pointsTo {α : Type} {p : PCM α} {r : Ref α p} {x : α}
    {h : Heap} (hPointsTo : (r ↦ x) h) : p.Compatible x (h.get r) :=
  compatible_get_of_sub hPointsTo

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
def postWand {α : Type} (Q₁ Q₂ : IPost α) : IProp :=
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
theorem postWand_equiv {α : Type} (H : IProp) (Q₁ Q₂ : IPost α) :
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
theorem postWand_intro {α : Type} {H : IProp} {Q₁ Q₂ : IPost α}
    (h : Q₁ ∗+ H ⊢+ Q₂) : H ⊢ Q₁ -∗+ Q₂ :=
  (postWand_equiv H Q₁ Q₂).mpr h

/-- Elimination rule for a postcondition wand. -/
theorem postWand_cancel {α : Type} (Q₁ Q₂ : IPost α) :
    Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  (postWand_equiv (Q₁ -∗+ Q₂) Q₁ Q₂).mp (entails_refl _)

/-- A postcondition wand yields a heap wand at every value. -/
theorem postWand_specialize {α : Type} {Q₁ Q₂ : IPost α} (value : α) :
    (Q₁ -∗+ Q₂) ⊢ (Q₁ value -∗ Q₂ value) :=
  forall_specialize value

theorem entails_postWand_pure_eq {α : Type} (H : IProp) (value : α) (Q : IPost α) :
    (H ⊢ (fun result => ⌜result = value⌝) -∗+ Q) ↔ (H ⊢ Q value) := by
  rw [postWand_equiv]
  constructor
  · intro h
    exact entails_trans (pure_sep_intro (P := value = value) H rfl) (h value)
  · intro h _
    exact entails_pure_l fun hEq => hEq ▸ h

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  wp : IPost α → IPre
  monotone :
    ∀ {Q₁ Q₂ : IPost α},
      (∀ value, Entails (Q₁ value) (Q₂ value)) →
      Entails (wp Q₁) (wp Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => IPost α → IPre) :=
  ⟨Wp.wp⟩

def pure (value : α) : Wp α :=
  ⟨fun Q => Q value, fun hQ => hQ value⟩

def bind (m : Wp α) (next : α → Wp β) : Wp β :=
  ⟨fun Q => m (fun value => next value Q), fun hQ =>
    m.monotone (fun value => (next value).monotone hQ)⟩

/-- Specification weakening is reverse implication between preconditions. -/
instance : LE (Wp α) where
  le w₁ w₂ := ∀ Q, Entails (w₂ Q) (w₁ Q)

instance : Preorder (Wp α) where
  le_refl w Q h hPre := hPre
  le_trans w₁ w₂ w₃ h₁₂ h₂₃ Q h hPre :=
    h₁₂ Q h (h₂₃ Q h hPre)

/-- Equivalence of specifications induced by the `Wp` preorder. -/
def Equiv (w₁ w₂ : Wp α) : Prop :=
  w₁ ≤ w₂ ∧ w₂ ≤ w₁

instance : Setoid (Wp α) where
  r := Equiv
  iseqv := {
    refl := fun w => ⟨le_refl w, le_refl w⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h₁₂ h₂₃ =>
      ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₂₃.2 h₁₂.2⟩
  }

theorem equiv_iff {w₁ w₂ : Wp α} :
    w₁ ≈ w₂ ↔ w₁ ≤ w₂ ∧ w₂ ≤ w₁ :=
  Iff.rfl

@[refl]
theorem equiv_refl (w : Wp α) : w ≈ w :=
  ⟨le_refl w, le_refl w⟩

theorem bind_mono {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≤ m₂) (hnext : ∀ value, next₁ value ≤ next₂ value) :
    bind m₁ next₁ ≤ bind m₂ next₂ := by
  intro Q h hBind
  apply m₁.monotone (fun value => hnext value Q) h
  exact hm (fun value => next₂ value Q) h hBind

theorem bind_congr {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≈ m₂) (hnext : ∀ value, next₁ value ≈ next₂ value) :
    bind m₁ next₁ ≈ bind m₂ next₂ :=
  ⟨bind_mono hm.1 (fun value => (hnext value).1),
    bind_mono hm.2 (fun value => (hnext value).2)⟩

end Wp

instance : Monad Wp where
  pure := Wp.pure
  bind := Wp.bind

instance : LawfulMonad Wp where
  map_const := by intros; rfl
  id_map := by intros; rfl
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl

instance : Aeneas.OrderedMonad Wp where
  bind_mono := Wp.bind_mono

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer.  The encoding is local: `P` is required to describe only part of
the heap, and the postcondition is handed to the continuation through a wand,
so that the frame is threaded automatically. -/
def pp2wp (P : IPre) (Q : IPost α) : Wp α where
  wp := fun R => P ∗ (Q -∗+ R)
  monotone := by
    intro R₁ R₂ hR
    exact sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (postWand_cancel Q R₁ value) (hR value))

def Wp.exists {ι : Sort _} (f : ι → Wp α) : Wp α where
  wp := fun R => iexists (fun x => f x R)
  monotone := by
    rintro R₁ R₂ hR h ⟨x, hx⟩
    exact ⟨x, (f x).monotone hR h hx⟩

theorem pp2wp_conseq {P : IPre} {Q R : IPost α} (hPost : Q ⊢+ R) :
    P ⊢ pp2wp P Q R :=
  entails_trans (entails_of_eq (sep_emp_r_eq P).symm)
    (sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (entails_of_eq (sep_emp_r_eq (Q value))) (hPost value)))

theorem pp2wp_frame {P : IPre} {Q R : IPost α} (H : IProp) :
    pp2wp P Q R ∗ H ⊢ pp2wp P Q (R ∗+ H) :=
  entails_trans (entails_of_eq (sep_assoc_eq P (Q -∗+ R) H))
    (sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (entails_of_eq (sep_assoc_eq (Q value) (Q -∗+ R) H).symm)
          (sep_mono (postWand_cancel Q R value) (entails_refl H))))

/-- The elimination principle of `pp2wp`: the heap splits into the footprint
described by `P` and a frame, and the continuation accepts any heap the
postcondition describes, put back next to that frame. -/
theorem pp2wp_elim {P : IPre} {Q R : IPost α} {h : Heap}
    (hWp : pp2wp P Q R h) :
    ∃ h₁ h₂,
      PartialCommMonoid.Compatible h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      P h₁ ∧
      ∀ value h', Q value h' →
        PartialCommMonoid.Compatible h' h₂ →
        R value (h' ∪ h₂) := by
  obtain ⟨h₁, h₂, hDisjoint, hEq, hP, hWand⟩ := hWp
  exact ⟨h₁, h₂, hDisjoint, hEq, hP, fun value h' hQ hDisjoint' =>
    postWand_cancel Q R value (h' ∪ h₂) ⟨h', h₂, hDisjoint', rfl, hQ, hWand⟩⟩

theorem Wp.exists_frame {ι : Sort _} {f : ι → Wp α} {Q : IPost α}
    (H : IProp) (hFrame : ∀ x, f x Q ∗ H ⊢ f x (Q ∗+ H)) :
    Wp.exists f Q ∗ H ⊢ Wp.exists f (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hx⟩, hH⟩
  exact ⟨x, hFrame x _ ⟨h₁, h₂, hDisjoint, rfl, hx, hH⟩⟩

end Aeneas.SLPoC

/-!
# Separation-logic tactics

The tactic layer provides `iframe`, `isimpl`, `iintro`, `irewrite`,
`wp_pures`, and `wp_apply`.
-/

namespace Aeneas.SLPoC

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/-! ## The `isimpl` engine

See the `isimpl` documentation below for the phases it goes through. -/

namespace IFrame

/-- The `iris_simps` simp attribute.  `iframe` and `iintro` use it to normalize
separation-logic assertions before extracting/cancelling them: it is where the
lemmas that unfold or fold representation predicates belong (`nodes_cons`,
`nodes_snoc`, …), making their rewriting declarative. -/
initialize irisSimpExt : SimpExtension ←
  registerSimpAttr `iris_simps "\
    The `iris_simps` attribute registers simp lemmas used by `iframe` and \
    `iintro` to normalize separation-logic assertions (typically, lemmas that \
    decompose a representation predicate into the cells it owns)."

private def isConnective (e : Expr) : Bool :=
  let head := e.consumeMData.getAppFn
  head.isConstOf ``sep || head.isConstOf ``ipure ||
    head.isConstOf ``iexists || head.isConstOf `Aeneas.SLPoC.emp ||
    -- `wand` is *defined* as an existential; unfolding it would be a disaster.
    head.isConstOf ``wand || head.isConstOf ``postWand || head.isConstOf ``iforall

/-- Is `e` a magic wand?  Returns whether it is a postcondition wand. -/
private def wand? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``postWand 3 then some true
  else if e.isAppOfArity ``wand 2 then some false
  else none

/-- Expose the head connective (`sep`, `ipure`, `iexists` or `emp`) of a
separation-logic assertion, by unfolding a definition that is a mere wrapper
around one — `wellFormed s l` is `⌜…⌝ ∗ nodes l`, `isList s vs` is `∃ l, …`.

Exactly one unfolding is performed, and only when it does reveal a connective.
Representation predicates that *compute*, such as `nodes`, are deliberately left
alone: decomposing them is the job of the `iris_simps` lemmas, which would
otherwise never get a chance to fire.  Returns `none` when no connective can be
reached, so that callers keep the original assertion. -/
def exposeConnective? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if isConnective e then return some e
  match ← unfoldDefinition? e with
  | some e' => if isConnective e' then return some e' else return none
  | none => return none

@[inherit_doc exposeConnective?]
def exposeConnective (e : Expr) : MetaM Expr :=
  return (← exposeConnective? e).getD e

private def reducePostApplication (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Lean.Core.betaReduce e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postSep && args.size = 4 then
    return mkApp2 (mkConst ``sep) (mkApp args[1]! args[3]!) args[2]!
  return e

private partial def flatten (e : Expr) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return (← flatten args[0]!) ++ (← flatten args[1]!)
  if fn.isConstOf `Aeneas.SLPoC.emp then
    return #[]
  return #[e]

private def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst `Aeneas.SLPoC.emp
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``sep) atom rest

private def removeMatches (available required : Array Expr) :
    MetaM (Option (Array Expr)) := do
  let mut remaining := available
  for expected in required do
    let mut found := none
    for h : i in [:remaining.size] do
      if ← isDefEq expected remaining[i] then
        found := some i
        break
    let some i := found | return none
    remaining :=
      remaining.extract 0 i ++ remaining.extract (i + 1) remaining.size
  return some remaining

/-- Prove `lhs = rhs` when the two sides are the same separating conjunction up
to associativity, commutativity and the `emp` unit. -/
private def proveEqAC (lhs rhs : Expr) : TacticM Expr := do
  let eqType ← mkEq lhs rhs
  let proof ← mkFreshExprSyntheticOpaqueMVar eqType
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create an equality proof goal"
  /- `ac_rfl` normalizes modulo associativity and commutativity but does not
     insert or erase the unit, so strip the `emp`s first when it fails. -/
  let tactic ← `(tactic|
    first
      | rfl
      | ac_rfl
      | (simp only [sep_emp_l_eq, sep_emp_r_eq] <;>
          first | rfl | ac_rfl))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove {eqType}"
  return proof

/-- Discharge a pure side-goal generated by the right-hand side of an
entailment.  This runs last, so the goal mentions no leftover metavariable
coming from a right-hand-side existential.

`grind` alone is not enough: the propositions typically mention the projections
of a representation predicate (`headPtr []`, `lastPtr [c]`, …), which only the
simp set computes.  `discharger` overrides the default chain; a `sym => …`
script driving a `register_sym_simp` variant is a good deterministic
alternative to the backtracking `first` below. -/
private def provePure (discharger : Option Syntax.Tactic) (proposition : Expr) :
    TacticM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar proposition
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create a pure proof goal"
  let tactic ←
    match discharger with
    | some tactic => pure tactic
    | none =>
      `(tactic|
        first
          | grind
          | (simp only [iris_simps, *]; done)
          | (simp only [iris_simps, *]; grind)
          | (simp_all; done)
          | (simp_all; grind))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove pure assertion {proposition}"
  return proof

/-- Is `destination` a frame-inference destination, i.e. of the shape
`Hcallee ∗ ?F` for an unassigned metavariable `?F`?

In that mode neither side of the entailment may be reorganized: anything we
extracted from the left-hand side would be lost from the frame `?F`, and could
not even be mentioned by it, since `?F` was created in an outer context. This
is exactly the limitation that the ramified frame rule works around.

`Hcallee` may itself be an existential, in which case floating that existential
out would turn the destination into `∃ x, Hcallee' x ∗ ?F` and hide the frame:
the decision must therefore be taken *before* any normalization. -/
private def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``sep && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

/-- Is the goal a frame-inference goal?  See `frameMVar?`. -/
private def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return false
  return (← frameMVar? (← reducePostApplication args[1]!)).isSome

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Aeneas.Simp.SimpArgs) : TacticM MVarId := do
  /- Restore the goals we are not working on: `Simp.simpAt` acts on the main
     goal, and dropping the others would silently remove them from the state. -/
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Aeneas.Simp.simpAt simpOnly
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      args (.targets #[] true)
    match ← getGoals with
    | [] => throwError "the entailment was unexpectedly closed while normalizing it"
    | goal :: _ => pure goal
  finally
    setGoals saved

/-- Float the existentials of a separating conjunction to its head, where
`pullLeft` and `instantiateRightExists` can see them.  Only used outside of
frame-inference mode: it can hide the frame metavariable behind an existential
(see `frameMVar?`). -/
private def floatExists (goal : MVarId) : TacticM MVarId :=
  simpEntailment goal true
    { addSimpThms :=
        -- Erase the `emp`s first, so that they do not get pushed under a binder.
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq] }

/-- Decompose the representation predicates of an entailment into the cells they
own, using the `iris_simps` set.  Unlike `floatExists` this is not always
desirable, so `iframe` only resorts to it when the plain cancellation fails. -/
private def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← irisSimpExt.getTheorems] }

/-- Rewrite an assertion into an equivalent one whose connectives are all
visible, by unfolding definitions such as `wellFormed` or `isList` through the
separating conjunctions.  Only delta/beta reduction is involved, so the result is
definitionally equal to the input. -/
private partial def exposeAll (e : Expr) : MetaM Expr := do
  let e ← reducePostApplication e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return mkApp2 (mkConst ``sep) (← exposeAll args[0]!) (← exposeAll args[1]!)
  return e

/-- Put the entailment of `goal` in the exposed form computed by `exposeAll`. -/
private def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let exposed ← mkAppM ``Entails #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

/-- Introduce the existentials of the left-hand side and move its pure facts
into the local context. Returns the residual goal. -/
private partial def pullLeft (goal : MVarId) : TacticM MVarId := do
  /- In frame-inference mode the left-hand side must be preserved verbatim.  The
     decision has to be taken *before* `floatExists`, which could otherwise turn
     `Hcallee ∗ ?F` into `∃ x, Hcallee' x ∗ ?F` and hide the frame. -/
  if ← isFrameInference goal then return goal
  /- Re-expose and re-float at every step: extracting a pure fact or a quantifier
     may reveal a definition (`isList`, …) hiding the next one. -/
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let (sourceFn, sourceArgs) :=
    source.consumeMData.withApp fun fn args => (fn, args)
  if sourceFn.isConstOf ``iexists && sourceArgs.size = 2 then
    let some u := sourceFn.constLevels!.head?
      | throwError "could not determine the universe of {source}"
    let ι := sourceArgs[0]!
    let J := sourceArgs[1]!
    let newType ← withLocalDeclD `x ι fun x => do
      mkForallFVars #[x] (← mkAppM ``Entails #[← Core.betaReduce (mkApp J x), destination])
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``entails_exists_l [u]) #[ι, destination, J, newGoal])
    let (_, next) ← newGoal.mvarId!.intro1P
    return ← pullLeft next
  let atoms ← flatten source
  let some i := atoms.findIdx? fun atom =>
      atom.consumeMData.isAppOfArity ``ipure 1
    | return goal
  let atom := atoms[i]!
  let proposition := atom.consumeMData.appArg!
  let rest := mkStar (atoms.eraseIdx! i)
  let newType ← withLocalDeclD `h proposition fun h => do
    mkForallFVars #[h] (← mkAppM ``Entails #[rest, destination])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  let extract := mkAppN (mkConst ``entails_pure_l)
    #[proposition, rest, destination, newGoal]
  let reordered := mkApp2 (mkConst ``sep) atom rest
  let reorder ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
  goal.assign (← mkAppM ``entails_trans #[reorder, extract])
  let (_, next) ← newGoal.mvarId!.intro1P
  pullLeft next

/-- Replace a right-hand-side `∃ x, J x` by `J ?x` for a fresh metavariable
`?x`, to be determined by the cancellation phase. -/
private partial def instantiateRightExists (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then return goal
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let source := args[0]!
  let destination ← reducePostApplication args[1]!
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``iexists && destArgs.size = 2 do return goal
  let some u := destFn.constLevels!.head?
    | throwError "could not determine the universe of {destination}"
  let ι := destArgs[0]!
  let J := destArgs[1]!
  let witness ← mkFreshExprMVar ι
  let newType ← mkAppM ``Entails #[source, ← Core.betaReduce (mkApp J witness)]
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``entails_exists_r [u]) #[ι, source, J, witness, newGoal])
  instantiateRightExists newGoal.mvarId!

/-- Replace the top-level existentials of the callee precondition of a
frame-inference goal by metavariables, so that the cancellation can pick the
witnesses.  Returns the peeled assertion together with a proof that it entails
the original one.

Unlike `pullLeft`, this is sound in frame-inference mode: it introduces
metavariables, not free variables, so nothing can escape the scope of the frame
metavariable. -/
private partial def peelRequiredExists (required : Expr) :
    MetaM (Expr × Expr × Array MVarId) := do
  let required ← reducePostApplication required
  let (fn, args) := required.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``iexists && args.size = 2 do
    return (required, ← mkAppM ``entails_refl #[required], #[])
  let some u := fn.constLevels!.head?
    | throwError "could not determine the universe of {required}"
  let ι := args[0]!
  let J := args[1]!
  let witness ← mkFreshExprMVar ι
  let body ← Core.betaReduce (mkApp J witness)
  let (peeled, peeledEntailsBody, witnesses) ← peelRequiredExists body
  let bodyEntailsRequired := mkAppN (mkConst ``entails_exists_r [u])
    #[ι, body, J, witness, ← mkAppM ``entails_refl #[body]]
  return (peeled,
    ← mkAppM ``entails_trans #[peeledEntailsBody, bodyEntailsRequired],
    witnesses.push witness.mvarId!)

mutual

/-- Prove `residual ⊢ wand` by the introduction rule of the wand, and hand the
resulting entailment back to `solveGoal`. -/
partial def proveWand (discharger : Option Syntax.Tactic)
    (residual wand : Expr) : TacticM Expr := do
  let some isPostcondition := wand? wand
    | throwError "expected a magic wand, got {wand}"
  let args := wand.consumeMData.getAppArgs
  let (lemmaName, premise) ←
    if isPostcondition then
      pure (``postWand_intro,
        ← mkAppM ``postEntails #[← mkAppM ``postSep #[args[1]!, residual], args[2]!])
    else
      pure (``wand_intro,
        ← mkAppM ``Entails #[mkApp2 (mkConst ``sep) args[0]! residual, args[1]!])
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do
    throwError "expected a separation-logic entailment"
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let sourceAtoms ← flatten source

  if let some frameMVar := ← frameMVar? destination then
    let destArgs := destination.consumeMData.getAppArgs
    let original ← reducePostApplication destArgs[0]!
    /- Cancel `required` against the source and put the leftovers in the frame.
       `weakening` proves `required ⊢ original`, and `witnesses` are the
       metavariables `peelRequiredExists` introduced: the cancellation has to
       determine all of them, otherwise the proof term would be incomplete. -/
    let solveWith (required weakening : Expr) (witnesses : Array MVarId) :
        TacticM Bool := do
      let requiredAtoms ← flatten required
      let some frameAtoms ← removeMatches sourceAtoms requiredAtoms
        | return false
      for witness in witnesses do
        unless ← witness.isAssigned do return false
      let frame := mkStar frameAtoms
      frameMVar.assign frame
      let cancelled := mkApp2 (mkConst ``sep) (← instantiateMVars required) frame
      let reorder ← mkAppM ``entails_of_eq #[← proveEqAC source cancelled]
      let weaken ← mkAppM ``sep_mono
        #[← instantiateMVars weakening, ← mkAppM ``entails_refl #[frame]]
      goal.assign (← mkAppM ``entails_trans #[reorder, weaken])
      return true
    let state ← saveState
    /- First try the callee precondition as it stands: it may well be owned as a
       single opaque assertion (an `isList`, say) by the caller.  Only if that
       fails do we open its existentials. -/
    unless ← solveWith original (← mkAppM ``entails_refl #[original]) #[] do
      state.restore
      let (peeled, weakening, witnesses) ← peelRequiredExists original
      unless ← solveWith peeled weakening witnesses do
        state.restore
        throwError "required spatial assertions are not present in the precondition\
          \nsource: {source}\ndestination: {destination}"
  else
    let destinationAtoms ← flatten destination
    let mut remaining := sourceAtoms
    let mut matched : Array Expr := #[]
    /- Cancellation phase.  A destination atom that cannot be cancelled must be
       pure — we record it and discharge it below, once every metavariable
       introduced for a right-hand-side existential has had a chance to be
       instantiated by unification — or a magic wand, which then absorbs
       everything the cancellation leaves over.  That is what the ramified frame
       rule puts on the right in place of a frame metavariable; there can be only
       one of them. -/
    let mut deferredPure : Array Expr := #[]
    let mut absorbing : Option Expr := none
    for expected in destinationAtoms do
      let mut found := none
      for h : i in [:remaining.size] do
        if ← isDefEq expected remaining[i] then
          found := some i
          break
      if let some i := found then
        matched := matched.push expected
        remaining :=
          remaining.extract 0 i ++ remaining.extract (i + 1) remaining.size
      else if expected.consumeMData.isAppOfArity ``ipure 1 then
        deferredPure := deferredPure.push expected
      else if (wand? expected).isSome then
        /- Note that we get here only when the wand could *not* be cancelled
           against an identical one on the left. -/
        if absorbing.isSome then
          throwError "cannot handle more than one magic wand on the right-hand \
            side\ndestination: {destination}"
        absorbing := some expected
      else
        throwError "required spatial assertions are not present\
          \nsource: {source}\ndestination: {destination}\nmissing: {expected}"
    let mut generatedPure : Array (Expr × Expr) := #[]
    for expected in deferredPure do
      let proposition ← instantiateMVars expected.consumeMData.appArg!
      generatedPure := generatedPure.push (expected, ← provePure discharger proposition)
    let matchedAssertion := mkStar matched
    /- `sourceToMatched : source ⊢ matchedAssertion ∗ absorbed`, where `absorbed`
       is the wand if there is one (which then swallows the residual resources),
       and `emp` otherwise (the residual resources must then be discardable). -/
    let (matchedAssertion, sourceToMatched) ←
      match absorbing with
      | some absorbingAtom =>
        let residual := mkStar remaining
        let reordered := mkApp2 (mkConst ``sep) matchedAssertion residual
        let reorderProof ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
        let residualToAbsorber ← proveWand discharger residual absorbingAtom
        let absorbProof ← mkAppM ``sep_mono
          #[← mkAppM ``entails_refl #[matchedAssertion], residualToAbsorber]
        pure (mkApp2 (mkConst ``sep) matchedAssertion absorbingAtom,
          ← mkAppM ``entails_trans #[reorderProof, absorbProof])
      | none =>
        let discardedAtoms := remaining
        let proof ←
          if discardedAtoms.isEmpty then
            mkAppM ``entails_of_eq #[← proveEqAC source matchedAssertion]
          else
            let discarded := mkStar discardedAtoms
            let reordered := mkApp2 (mkConst ``sep) matchedAssertion discarded
            let reorderProof ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
            /- The logic is affine, so whatever the cancellation leaves over is
               discardable. -/
            let eliminateProof ← mkAppM ``sep_elim_right
              #[matchedAssertion, discarded]
            mkAppM ``entails_trans #[reorderProof, eliminateProof]
        pure (matchedAssertion, proof)
    let mut current := matchedAssertion
    let mut insertionProof ← mkAppM ``entails_refl #[current]
    for (pureAtom, pureProof) in generatedPure do
      let insertProof ← mkAppM ``pure_sep_intro #[current, pureProof]
      insertionProof ← mkAppM ``entails_trans #[insertionProof, insertProof]
      current := mkApp2 (mkConst ``sep) pureAtom current
    let destination ← instantiateMVars destination
    let eqProof ← proveEqAC current destination
    let reorderProof ← mkAppM ``entails_of_eq #[eqProof]
    let matchedToDestination ← mkAppM ``entails_trans #[insertionProof, reorderProof]
    goal.assign (← mkAppM ``entails_trans #[sourceToMatched, matchedToDestination])

partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postEntails && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal discharger nextGoal
  else
    /- Two passes.  The first one only reorganizes the connectives; it is the one
       that succeeds when the assertion to produce is a representation predicate
       applied to a metavariable, which no rewriting could ever match.  The
       second one additionally decomposes the representation predicates with the
       `iris_simps` set, which is what is needed when the two sides of the
       entailment own the same cells but describe them differently. -/
    let pass (decomposing : Bool) : TacticM Unit := do
      let goal ← if decomposing then decompose goal else pure goal
      /- Decide here whether we are inferring a frame: `floatExists` below can
         turn `Hcallee ∗ ?F` into `∃ x, Hcallee' x ∗ ?F` and hide `?F`. -/
      if ← isFrameInference goal then
        /- Expose before decomposing again: `iris_simps` has no lemma for the
           representation predicates themselves (`wellFormed`, `isList`, …), so
           decomposing a folded assertion is a no-op. -/
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
      else
        let goal ← pullLeft goal
        let goal ← instantiateRightExists goal
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
    let state ← saveState
    try pass false
    catch firstError =>
      state.restore
      try pass true
      catch secondError =>
        throwError "iframe failed.\n\
          {firstError.toMessageData}\n\
          and, after decomposing the assertions with `iris_simps`:\n\
          {secondError.toMessageData}"

/-- Pull quantifiers and pure facts from an entailment's left-hand side. -/
partial def pullGoal (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then
    throwError "iintro_entail: this is a frame-inference goal.  Extracting anything \
      from its left-hand side would lose it from the frame, which was created in \
      an outer context; pull at the level of the triple instead, with `iintro`."
  let target ← instantiateMVars (← goal.getType)
  if target.consumeMData.isAppOfArity ``postEntails 3 then
    let (_, next) ← goal.intro1P
    pullLeft next
  else
    pullLeft goal

end

end IFrame

/-- Prove a separation-logic entailment `H₁ ⊢ H₂` (or a postcondition entailment
`Q₁ ⊢+ Q₂`):

1. the existentials of the left-hand side are introduced and its pure facts are
   moved into the local context;
2. the existentials of the right-hand side are replaced by metavariables;
3. the spatial assertions of the right-hand side are cancelled against those of
   the left-hand side, up to associativity/commutativity, which is what
   instantiates the metavariables of step 2;
4. the pure assertions left over on the right-hand side are discharged last —
   after step 3, so that they mention no leftover metavariable.

Unmatched pure assertions of the left-hand side may be discarded; unmatched
spatial assertions are reported as an error.

When the right-hand side is of the shape `H ∗ ?F` for an unassigned
metavariable `?F` (frame inference, as generated by `step`), steps 1 and 2 are
skipped: the residual resources have to end up in the frame rather than in the
local context.

`iframe by tac` uses `tac` instead of the default chain to discharge the pure
side-goals of step 4.  Lean's `sym => …` symbolic-simulation mode is a good
choice when the default chain is too slow or too unpredictable, since it makes
the normalization explicit instead of relying on backtracking:

```
register_sym_simp slPure where
  post := ground >> rewrite [headPtr_nil, lastPtr_nil, headPtr_cons,
    lastPtr_singleton, lastPtr_snoc] with self

example … := by
  iframe by sym => first ((simp slPure); finish) (simp slPure) (finish)
```
-/
syntax (name := iFrame) "iframe" (" by " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| iframe $[by $tac?]?) => Tactic.focus do withMainContext do
  let discharger : Option Syntax.Tactic := tac?.map fun tac => ⟨tac.raw⟩
  let localAsms :=
    (← (← getLCtx).getAssumptions).map LocalDecl.fvarId |>.toArray
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { hypsToUse := localAsms }
    (.targets #[] true)
  if !(← getGoals).isEmpty then
    let goal ← getMainGoal
    IFrame.solveGoal discharger goal
    replaceMainGoal []

/-- Normalize the separating conjunctions of the goal: float the existentials out of them, drop
the `emp`s, and reassociate to the right.

Also collapses a ramified wand whose antecedent is a pure equality
(`entails_postWand_pure_eq`): that is the shape a terminal return leaves behind, and
frame inference cannot cancel it on its own. -/
elab "isimp" : tactic => withMainContext do
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq, ``sep_assoc_eq,
          ``entails_postWand_pure_eq] }
    (.targets #[] true)

/-- One step of `iintro`: peel a quantifier or a pure fact off the precondition
of a triple.  Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective: applying `triple_exists` or `triple_ipure` blindly
would let the unifier see through `sep`/`ipure` down to the raw heap predicate
and peel a quantifier of the *model* instead. -/
elab "iintro_step" : tactic => withMainContext do
  /- Float the existentials out of the separating conjunctions and drop the
     `emp`s left behind by previous steps, so that the head connective of the
     precondition is the one we want to peel. -/
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``sep_exists_l_eq, ``sep_exists_r_eq,
          ``sep_emp_l_eq, ``sep_emp_r_eq] }
    (.targets #[] true)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 do
    throwError "iintro_step: the goal is not a separation-logic triple"
  let precondition ← IFrame.exposeConnective args[1]!
  let head := precondition.consumeMData.getAppFn
  let leadingPure ←
    if precondition.consumeMData.isAppOfArity ``sep 2 then
      pure ((← IFrame.exposeConnective precondition.consumeMData.appFn!.appArg!)
        |>.consumeMData.isAppOfArity ``ipure 1)
    else pure false
  let lemmaName ←
    if head.isConstOf ``iexists then pure `Aeneas.SLPoC.triple_exists
    else if head.isConstOf ``ipure then pure `Aeneas.SLPoC.triple_ipure'
    else if leadingPure then pure `Aeneas.SLPoC.triple_ipure
    else
      throwError "iintro_step: the precondition has no quantifier or pure fact \
        left to extract:\n{precondition}"
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, precondition, args[2]!, args[3]!])
  replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))

/-- Move the existentials and pure facts of a triple's precondition into the
local context.

`iintro` peels as many of them as it can, using inaccessible names.
`iintro p₁ ... pₙ` peels exactly `n` of them, destructuring the `i`-th one with
the `rintro` pattern `pᵢ`, e.g. `iintro l rfl` or `iintro ⟨hhead, htail⟩`.

Pure facts are *removed* from the precondition, which is often not what a
subsequent `step` needs; use `iintro_keep` when only the local hypothesis is
wanted. -/
syntax (name := iIntro) "iintro" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| iintro $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (iintro_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (iintro_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

/-- Whether a quantifier or a pure fact can be peeled off `pre` without unfolding it: an opened
representation predicate is one the frame inference of a later `step` can no longer match. -/
private def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``iexists 2 || pre.isAppOfArity ``ipure 1 then true
  else if pre.isAppOfArity ``sep 2 then
    pre.appFn!.appArg!.consumeMData.isAppOfArity ``ipure 1
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity `Aeneas.SLPoC.triple 4 &&
      isPullable target.getAppArgs[1]! do return goal
  setGoals [goal]
  let state ← saveState
  try
    evalTactic (← `(tactic| iintro_step))
  catch _ =>
    state.restore
    return goal
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

/-- `iintro` restricted to what the precondition exposes without being unfolded; see
`isPullable`. -/
elab "iintro_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

/-- One step of `iintro_keep`: copy the leading pure fact of the precondition of
a triple into the local context, *without* removing it from the precondition.

`iintro_step` consumes the fact, but that is often the wrong thing here: the
assertion has to keep it for the framing of the later
steps (this is why `iintro` before a `step` can turn a working proof into a
failing one).  Copying is always sound, and it is what makes the pointer of a
callee's precondition (`s.head.get!`, say) reducible to the one the assertion
owns.

Fails when the fact is already in the context, so that `repeat` terminates. -/
elab "iintro_keep_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 do
    throwError "iintro_keep_step: the goal is not a separation-logic triple"
  let precondition ← IFrame.exposeConnective args[1]!
  unless precondition.consumeMData.isAppOfArity ``sep 2 do
    throwError "iintro_keep_step: the precondition is not a separating conjunction"
  let leading ← IFrame.exposeConnective precondition.consumeMData.appFn!.appArg!
  unless leading.consumeMData.isAppOfArity ``ipure 1 do
    throwError "iintro_keep_step: the precondition does not start with a pure fact"
  let proposition := leading.consumeMData.appArg!
  if ← (← getLCtx).anyM fun decl =>
      pure !decl.isImplementationDetail <&&> isDefEq decl.type proposition then
    throwError "iintro_keep_step: this pure fact is already in the context"
  let exposed := mkApp2 (mkConst ``sep) leading precondition.consumeMData.appArg!
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, exposed, args[2]!, args[3]!])
  let [next] ← goal.apply
    (← mkConstWithFreshMVarLevels `Aeneas.SLPoC.triple_ipure_keep)
    | throwError "iintro_keep_step: unexpected number of goals"
  let (_, next) ← next.intro1P
  /- Put the precondition back in its original, folded form: only the local
     context should record that the step happened. -/
  replaceMainGoal
    [← next.change
      (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, args[1]!, args[2]!, args[3]!])]

/-- Copy the pure facts of the precondition of a triple into the local context,
leaving the precondition untouched.  See `iintro_keep_step`. -/
macro "iintro_keep" : tactic => `(tactic| repeat (iintro_keep_step; rename_i _))

/-- `iframe` under the name used for entailment simplification. -/
syntax "isimpl" (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| isimpl) => `(tactic| iframe)
  | `(tactic| isimpl by $tac) => `(tactic| iframe by $tac)

/-- On an entailment `H₁ ⊢ H₂` or `Q₁ ⊢+ Q₂`, introduce the existentials of
the left-hand side and move its pure facts into the local context, leaving the
right-hand side alone.

Use it when the witness the right-hand side needs depends on a variable bound on
the left: `isimpl` would otherwise pick the metavariable for the right-hand
side *before* that variable exists. -/
elab "iintro_entail" : tactic => Tactic.focus do withMainContext do
  replaceMainGoal [← IFrame.pullGoal (← getMainGoal)]

/-! ## `irewrite` -/

/-- The rule behind `irewrite`: rewrite a part of the left-hand side of an
entailment with an entailment of its own. -/
theorem entails_rewrite {H₁ H₂ H₃ H₄ : IProp} (hPart : H₁ ⊢ H₂)
    (hRest : H₂ ∗ H₃ ⊢ H₄) : H₁ ∗ H₃ ⊢ H₄ :=
  entails_trans (sep_mono hPart (entails_refl H₃)) hRest

namespace IFrame

/-- Rewrite the assertion `H` (the left-hand side of an entailment, or the
precondition of a triple) using `lemma : A ⊢ B` or `lemma : A = B`, replacing the
atom `A` of `H` by `B`.  Returns the rewritten assertion and a proof of
`H ⊢ rewritten`. -/
def rewriteAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  /- Accept both an entailment and an equality, in either direction for the
     latter. -/
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``Entails 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, ← mkAppM ``entails_of_eq #[rule])
    else
      throwError "irewrite expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let atoms ← flatten assertion
  /- The rewritten part may be a separating conjunction of several atoms, which
     do not have to be adjacent in `assertion`. -/
  let some restAtoms ← removeMatches atoms (← flatten lhs)
    | throwError "irewrite: {lhs}\nis not part of\n{assertion}"
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``sep) (← instantiateMVars lhs) rest
  let reorder ← mkAppM ``entails_of_eq #[← proveEqAC assertion reordered]
  let rewritten := mkApp2 (mkConst ``sep) (← instantiateMVars rhs) rest
  let change ← mkAppM ``sep_mono #[entailment, ← mkAppM ``entails_refl #[rest]]
  return (rewritten, ← mkAppM ``entails_trans #[reorder, change])

end IFrame

/-- Rewrite part of the current resources with an entailment.

`irewrite M`, for `M : A ⊢ B` (or `M : A = B`), replaces the assertion `A` by
`B` in the left-hand side of the entailment, or in the precondition of the
triple, that the goal states.  This is how a representation predicate is opened
or closed when plain cancellation cannot see through it.

Unlike `rw`, `M` need not be an equality and `A` need not occur syntactically:
it only has to be one of the `∗`-separated atoms, up to unification. -/
elab "irewrite" rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``Entails && args.size = 2 then
    let (rewritten, proof) ← IFrame.rewriteAssertion args[0]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Entails #[rewritten, args[1]!])
    goal.assign (← mkAppM ``entails_trans #[proof, next])
    replaceMainGoal [next.mvarId!]
  else if fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 then
    let (rewritten, proof) ← IFrame.rewriteAssertion args[1]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, rewritten, args[2]!, args[3]!])
    let qrefl ← withLocalDeclD `value args[0]! fun value => do
      mkLambdaFVars #[value] (← mkAppM ``entails_refl #[mkApp args[3]! value])
    goal.assign (← mkAppM `Aeneas.SLPoC.triple_conseq #[next, proof, qrefl])
    replaceMainGoal [next.mvarId!]
  else
    throwError "irewrite expects an entailment or a triple, got\n{target}"

end Aeneas.SLPoC
