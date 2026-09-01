import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Heap
import AeneasMeta.Simp
import Lean.Meta.Tactic.AC

/-!
# Separation-logic assertions and the weakest-precondition monad

Heap predicates (`SLProp`) with the usual separation-logic connectives — the
separating conjunction, the points-to assertion `p ↦ value` and the magic wand
included — and the monad `Wp` of monotone predicate transformers they live in.
Nothing here mentions the state monad: its denotation into `Wp` and the Hoare
triples it induces are in `Aeneas.SLPoC.ST`.

The logic is *affine*, as Iris's is: an assertion owns the cells it describes
and says nothing about the rest of the heap, so `emp` is the affine top and the
entailment `⊢` weakens — `H ⊢ emp` for every `H`.  Resources may therefore be
discarded anywhere.  Following Iris's `uPred`, affinity is a property of the
*model*:
`SLProp` bundles closure under `Heap.Sub`, which is what makes `emp ∗ H ⊣⊢ H`
provable once `emp` holds of every heap.
-/

namespace Aeneas.SLPoC

/-- Heap predicates describe heap fragments.  Like Iris's `uPred`, an assertion
is closed under heap extension: it constrains the cells it owns, and says
nothing about the others. -/
structure SLProp where
  holds : Heap → Prop
  up_closed : ∀ {h h' : Heap}, holds h → Heap.Sub h h' → holds h'

instance : CoeFun SLProp (fun _ => Heap → Prop) :=
  ⟨SLProp.holds⟩

@[ext]
theorem SLProp.ext {H₁ H₂ : SLProp} (hIff : ∀ h, H₁ h ↔ H₂ h) : H₁ = H₂ := by
  obtain ⟨holds₁, _⟩ := H₁
  obtain ⟨holds₂, _⟩ := H₂
  have hEq : holds₁ = holds₂ := funext fun h => propext (hIff h)
  subst hEq
  rfl

/- Preconditions are separation-logic propositions. -/
abbrev SLPre := SLProp

/- Postconditions describe both a returned value and a heap fragment. -/
abbrev SLPost (α : Type) := α → SLProp

def himpl (H₁ H₂ : SLProp) : Prop :=
  ∀ h, H₁ h → H₂ h

def hequiv (H₁ H₂ : SLProp) : Prop :=
  ∀ h, H₁ h ↔ H₂ h

/-- The empty assertion owns nothing.  Being affine it holds of *every* heap,
exactly like Iris's `emp`, which coincides with `True` there. -/
def hempty : SLProp where
  holds _ := True
  up_closed := fun _ _ => trivial

/-- A pure fact owns nothing, so — unlike SLF's `\[P]` and like Iris's `⌜P⌝` —
it says nothing about the heap it is asserted of. -/
def hpure (P : Prop) : SLProp where
  holds _ := P
  up_closed := fun hP _ => hP

/-- The points-to assertion: the heap owns the cell `p` points at, and it holds
`value`. -/
def hsingle {α : Type} (r : Ref α) (value : α) : SLProp where
  holds h := Heap.Sub (singleton r value) h
  up_closed := fun hSub hExtend => hSub.trans hExtend

def hstar (H₁ H₂ : SLProp) : SLProp where
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

def hexists {α : Sort _} (J : α → SLProp) : SLProp where
  holds h := ∃ x, J x h
  up_closed := fun ⟨x, hJ⟩ hExtend => ⟨x, (J x).up_closed hJ hExtend⟩

def qstar {α : Type} (Q : SLPost α) (H : SLProp) :
    SLPost α :=
  fun value => hstar (Q value) H

def qimpl {α : Type} (Q₁ Q₂ : SLPost α) : Prop :=
  ∀ value, himpl (Q₁ value) (Q₂ value)

namespace SepLogic

scoped syntax:max "iprop(" term ")" : term
scoped notation "emp" => hempty
scoped syntax "⌜" term "⌝" : term
scoped macro_rules
  | `(⌜$P⌝) => `(hpure $P)
scoped macro_rules
  | `(iprop(∃ $x:ident, $H)) => `(hexists fun $x => iprop($H))
  | `(iprop(∃ $x:ident : $type, $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop(∃ ($x:ident : $type), $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop($H)) => `($H)
scoped infixr:35 " ∗ " => hstar
scoped infixr:40 " ∗+ " => qstar
scoped infix:25 " ⊢ " => himpl
scoped infix:25 " ⊢+ " => qimpl
scoped infix:25 " ⊣⊢ " => hequiv
scoped notation:52 p:53 " ↦ " value:53 => hsingle p value

end SepLogic

open scoped SepLogic

theorem himpl_refl (H : SLProp) : H ⊢ H :=
  fun _ hH => hH

theorem himpl_trans {P Q R : SLProp} (hPQ : P ⊢ Q) (hQR : Q ⊢ R) :
    P ⊢ R :=
  fun h hP => hQR h (hPQ h hP)

theorem himpl_of_eq {P Q : SLProp} (hEq : P = Q) : P ⊢ Q := by
  subst Q
  exact himpl_refl P

theorem hequiv_eq {P Q : SLProp} (hEquiv : P ⊣⊢ Q) : P = Q :=
  SLProp.ext hEquiv

theorem hstar_assoc (H₁ H₂ H₃ : SLProp) :
    (H₁ ∗ H₂) ∗ H₃ ⊣⊢ H₁ ∗ (H₂ ∗ H₃) := by
  intro h
  constructor
  · rintro ⟨h₁₂, h₃, hDisjoint₁₂₃, hEq, hStar₁₂, hH₃⟩
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
  · rintro ⟨h₁, h₂₃, hDisjoint₁₂₃, hEq, hH₁, hStar₂₃⟩
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

theorem hstar_comm (H₁ H₂ : SLProp) :
    H₁ ∗ H₂ ⊣⊢ H₂ ∗ H₁ := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, hH₁, hH₂⟩
    exact ⟨h₂, h₁, PartialCommMonoid.compatible_comm hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₂, hH₁⟩
  · rintro ⟨h₂, h₁, hDisjoint, hEq, hH₂, hH₁⟩
    exact ⟨h₁, h₂, PartialCommMonoid.compatible_comm hDisjoint,
      hEq.trans (PartialCommMonoid.union_comm_of_compatible hDisjoint),
      hH₁, hH₂⟩

theorem hstar_assoc_eq (H₁ H₂ H₃ : SLProp) :
    ((H₁ ∗ H₂) ∗ H₃) = (H₁ ∗ (H₂ ∗ H₃)) :=
  hequiv_eq (hstar_assoc H₁ H₂ H₃)

theorem hstar_comm_eq (H₁ H₂ : SLProp) :
    (H₁ ∗ H₂) = (H₂ ∗ H₁) :=
  hequiv_eq (hstar_comm H₁ H₂)

instance : Std.Associative hstar where
  assoc := hstar_assoc_eq

instance : Std.Commutative hstar where
  comm := hstar_comm_eq

theorem hstar_mono {P₁ P₂ Q₁ Q₂ : SLProp}
    (hP : P₁ ⊢ P₂) (hQ : Q₁ ⊢ Q₂) :
    P₁ ∗ Q₁ ⊢ P₂ ∗ Q₂ := by
  intro h
  rintro ⟨h₁, h₂, hDisjoint, hEq, hP₁, hQ₁⟩
  exact ⟨h₁, h₂, hDisjoint, hEq, hP h₁ hP₁, hQ h₂ hQ₁⟩

theorem hstar_hempty_l (H : SLProp) :
    emp ∗ H ⊣⊢ H := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, rfl, -, hH⟩
    exact H.up_closed hH (Heap.Sub.union_right hDisjoint)
  · intro hH
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, trivial, hH⟩

theorem hstar_hempty_r (H : SLProp) :
    H ∗ emp ⊣⊢ H := by
  intro h
  exact (hstar_comm H emp h).trans (hstar_hempty_l H h)

theorem hstar_hempty_l_eq (H : SLProp) :
    (emp ∗ H) = H :=
  hequiv_eq (hstar_hempty_l H)

theorem hstar_hempty_r_eq (H : SLProp) :
    (H ∗ emp) = H :=
  hequiv_eq (hstar_hempty_r H)

instance : Std.LawfulIdentity hstar hempty where
  left_id := hstar_hempty_l_eq
  right_id := hstar_hempty_r_eq

/-- Affinity: every assertion may be discarded.  This is the rule the exact
logic of SLF lacks, and the reason its affine top is simply `emp` here. -/
theorem himpl_hempty_r (H : SLProp) : H ⊢ emp :=
  fun _ _ => trivial

/-! ### The model, spelled out

`H h` reduces to the right-hand sides below by `rfl`; these lemmas let `simp`
and `rw` see through the `SLProp` structure when a proof does go down to the
heap. -/

@[simp]
theorem hempty_holds (h : Heap) : (emp : SLProp) h ↔ True :=
  Iff.rfl

@[simp]
theorem hpure_holds {P : Prop} (h : Heap) : (⌜P⌝ : SLProp) h ↔ P :=
  Iff.rfl

theorem hsingle_holds {α : Type} (r : Ref α) (value : α) (h : Heap) :
    (r ↦ value) h ↔ Heap.Sub (singleton r value) h :=
  Iff.rfl

/-- Points-to is exclusive: affinity lets resources be *dropped*, never
duplicated, so a cell still cannot be owned twice. -/
theorem hsingle_exclusive {α : Type} (r : Ref α) (value₁ value₂ : α) :
    r ↦ value₁ ∗ r ↦ value₂ ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hDisjoint, -, hSingle₁, hSingle₂⟩
  apply disjoint_contains_false hDisjoint
  · obtain ⟨rest, _, rfl⟩ := hSingle₁
    exact contains_union_left (contains_singleton r value₁)
  · obtain ⟨rest, _, rfl⟩ := hSingle₂
    exact contains_union_left (contains_singleton r value₂)

theorem hstar_holds (H₁ H₂ : SLProp) (h : Heap) :
    (H₁ ∗ H₂) h ↔
      ∃ h₁ h₂, PartialCommMonoid.Compatible h₁ h₂ ∧
        h = h₁ ∪ h₂ ∧ H₁ h₁ ∧ H₂ h₂ :=
  Iff.rfl

theorem hexists_holds {ι : Sort _} (J : ι → SLProp) (h : Heap) :
    hexists J h ↔ ∃ x, J x h :=
  Iff.rfl

theorem hstar_hexists {α : Sort _} (J : α → SLProp) (H : SLProp) :
    iprop(∃ x, J x) ∗ H ⊣⊢ iprop(∃ x, J x ∗ H) := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩
    exact ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
  · rintro ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
    exact ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩

/-- A pure fact on the left of a separating conjunction: since pure facts own
nothing, they can be read off, and put back, without touching the heap. -/
theorem hstar_hpure_l (P : Prop) (H : SLProp) (h : Heap) :
    (⌜P⌝ ∗ H) h ↔ P ∧ H h := by
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, rfl, hP, hH⟩
    exact ⟨hP, H.up_closed hH (Heap.Sub.union_right hDisjoint)⟩
  · rintro ⟨hP, hH⟩
    exact ⟨∅, h, PartialCommMonoid.compatible_empty_left h,
      (PartialCommMonoid.empty_union h).symm, hP, hH⟩

theorem hpure_hstar_intro {P : Prop} (H : SLProp) (hP : P) :
    H ⊢ ⌜P⌝ ∗ H := by
  intro h hH
  exact (hstar_hpure_l P H h).mpr ⟨hP, hH⟩

/-- Extraction of a pure fact from the left-hand side of an entailment.  This is
SLF's `himpl_hstar_hpure_l`, the workhorse of `xpull`. -/
theorem himpl_hpure_l {P : Prop} {H H' : SLProp} (h : P → H ⊢ H') :
    ⌜P⌝ ∗ H ⊢ H' := by
  intro heap hStar
  have ⟨hP, hH⟩ := (hstar_hpure_l P H heap).mp hStar
  exact h hP heap hH

/-- Introduction of an existential quantifier on the left-hand side of an
entailment (SLF's `himpl_hexists_l`). -/
theorem himpl_hexists_l {ι : Sort _} {H : SLProp} {J : ι → SLProp}
    (h : ∀ x, J x ⊢ H) : hexists J ⊢ H :=
  fun heap hJ => h hJ.choose heap hJ.choose_spec

/-- Instantiation of an existential quantifier on the right-hand side of an
entailment (SLF's `himpl_hexists_r`).  `xsimpl` uses it with a metavariable for
`x`, which the cancellation phase then instantiates by unification. -/
theorem himpl_hexists_r {ι : Sort _} {H : SLProp} {J : ι → SLProp} (x : ι)
    (h : H ⊢ J x) : H ⊢ hexists J :=
  fun heap hH => ⟨x, h heap hH⟩

/-- Float an existential out of the left factor of a separating conjunction. -/
theorem hstar_hexists_l_eq {ι : Sort _} (J : ι → SLProp) (H : SLProp) :
    (hexists J ∗ H) = iprop(∃ x, J x ∗ H) :=
  hequiv_eq (hstar_hexists J H)

/-- Float an existential out of the right factor of a separating conjunction. -/
theorem hstar_hexists_r_eq {ι : Sort _} (H : SLProp) (J : ι → SLProp) :
    (H ∗ hexists J) = iprop(∃ x, H ∗ J x) := by
  rw [hstar_comm_eq, hstar_hexists_l_eq]
  exact hequiv_eq fun _ => ⟨fun ⟨x, hx⟩ => ⟨x, (hstar_comm _ _ _).mp hx⟩,
    fun ⟨x, hx⟩ => ⟨x, (hstar_comm _ _ _).mp hx⟩⟩

/-- SLF discards a pure fact by turning it into `emp`; here every assertion can
be, so this is a special case of `himpl_hempty_r`. -/
theorem hpure_elim (P : Prop) :
    ⌜P⌝ ⊢ emp :=
  himpl_hempty_r _

/-- Drop the right factor of a separating conjunction.  SLF requires it to be
discardable (`F ⊢ emp`); affinity makes that hypothesis vacuous. -/
theorem hstar_elim_right (P F : SLProp) :
    P ∗ F ⊢ P :=
  himpl_trans (hstar_mono (himpl_refl P) (himpl_hempty_r F))
    (fun h => (hstar_hempty_r P h).mp)

/-- Drop the left factor of a separating conjunction. -/
theorem hstar_elim_left (P F : SLProp) :
    F ∗ P ⊢ P :=
  himpl_trans (fun h => (hstar_comm F P h).mp) (hstar_elim_right P F)

/-! ## The magic wand

`H₁ -∗ H₂` describes the heap fragments that, extended with a disjoint fragment
satisfying `H₁`, satisfy `H₂`.  In the affine model this Kripke-style reading is
the right adjoint of the separating conjunction, so — unlike in SLF, where the
wand is *encoded* as `∃ H₀, H₀ ∗ ⌜H₁ ∗ H₀ ⊢ H₂⌝` to avoid a semantic definition
— it may be defined directly. -/

/-- Universal quantification over heap predicates. -/
def hforall {ι : Sort _} (J : ι → SLProp) : SLProp where
  holds h := ∀ x, J x h
  up_closed := fun hJ hExtend x => (J x).up_closed (hJ x) hExtend

/-- The magic wand of SLF (`\-*`). -/
def hwand (H₁ H₂ : SLProp) : SLProp where
  holds h :=
    ∀ h', PartialCommMonoid.Compatible h h' → H₁ h' → H₂ (h ∪ h')
  up_closed := by
    intro h hBig hWand hExtend h' hDisjoint hH₁
    have hDisjoint' : PartialCommMonoid.Compatible h h' :=
      Heap.Sub.disjoint_of_sub hExtend hDisjoint
    exact H₂.up_closed (hWand h' hDisjoint' hH₁)
      (Heap.Sub.union_mono_left hExtend hDisjoint)

/-- The magic wand between postconditions (SLF's `\--*`).  Note that it is a
heap predicate, not a postcondition. -/
def qwand {α : Type} (Q₁ Q₂ : SLPost α) : SLProp :=
  hforall fun value => hwand (Q₁ value) (Q₂ value)

namespace SepLogic

@[inherit_doc hwand] scoped infixr:33 " -∗ " => hwand
@[inherit_doc qwand] scoped infixr:33 " -∗+ " => qwand
@[inherit_doc hforall] scoped notation "∀ˢ " x ", " J => hforall (fun x => J)

end SepLogic

theorem hforall_intro {ι : Sort _} {H : SLProp} {J : ι → SLProp}
    (h : ∀ x, H ⊢ J x) : H ⊢ hforall J :=
  fun heap hH x => h x heap hH

theorem hforall_specialize {ι : Sort _} {J : ι → SLProp} (x : ι) :
    hforall J ⊢ J x :=
  fun _ hJ => hJ x

/-- SLF's `hwand_equiv`: the wand is the right adjoint of the separating
conjunction.  Every other property of the wand follows from it. -/
theorem hwand_equiv (H₀ H₁ H₂ : SLProp) :
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

/-- SLF's `himpl_hwand_r`, the introduction rule of the wand. -/
theorem hwand_intro {H₀ H₁ H₂ : SLProp} (h : H₁ ∗ H₀ ⊢ H₂) : H₀ ⊢ H₁ -∗ H₂ :=
  (hwand_equiv H₀ H₁ H₂).mpr h

/-- SLF's `hwand_cancel`, the elimination rule of the wand. -/
theorem hwand_cancel (H₁ H₂ : SLProp) : H₁ ∗ (H₁ -∗ H₂) ⊢ H₂ :=
  (hwand_equiv (H₁ -∗ H₂) H₁ H₂).mp (himpl_refl _)

theorem hwand_mono {H₁ H₁' H₂ H₂' : SLProp} (h₁ : H₁' ⊢ H₁) (h₂ : H₂ ⊢ H₂') :
    (H₁ -∗ H₂) ⊢ (H₁' -∗ H₂') :=
  hwand_intro (himpl_trans (hstar_mono h₁ (himpl_refl _))
    (himpl_trans (hwand_cancel H₁ H₂) h₂))

/-- SLF's `qwand_equiv`. -/
theorem qwand_equiv {α : Type} (H : SLProp) (Q₁ Q₂ : SLPost α) :
    (H ⊢ Q₁ -∗+ Q₂) ↔ (Q₁ ∗+ H ⊢+ Q₂) := by
  constructor
  · intro h value
    exact himpl_trans (hstar_mono (himpl_refl _)
      (himpl_trans h (hforall_specialize value)))
      (hwand_cancel (Q₁ value) (Q₂ value))
  · intro h
    exact hforall_intro fun value =>
      hwand_intro (h value)

/-- SLF's `qwand_intro`. -/
theorem qwand_intro {α : Type} {H : SLProp} {Q₁ Q₂ : SLPost α}
    (h : Q₁ ∗+ H ⊢+ Q₂) : H ⊢ Q₁ -∗+ Q₂ :=
  (qwand_equiv H Q₁ Q₂).mpr h

/-- SLF's `qwand_cancel`. -/
theorem qwand_cancel {α : Type} (Q₁ Q₂ : SLPost α) :
    Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  (qwand_equiv (Q₁ -∗+ Q₂) Q₁ Q₂).mp (himpl_refl _)

/-- SLF's `qwand_specialize`: a postcondition wand yields a heap wand at every
value. -/
theorem qwand_specialize {α : Type} {Q₁ Q₂ : SLPost α} (value : α) :
    (Q₁ -∗+ Q₂) ⊢ (Q₁ value -∗ Q₂ value) :=
  hforall_specialize value

theorem himpl_qwand_hpure_eq {α : Type} (H : SLProp) (value : α) (Q : SLPost α) :
    (H ⊢ (fun result => ⌜result = value⌝) -∗+ Q) ↔ (H ⊢ Q value) := by
  rw [qwand_equiv]
  constructor
  · intro h
    exact himpl_trans (hpure_hstar_intro (P := value = value) H rfl) (h value)
  · intro h _
    exact himpl_hpure_l fun hEq => hEq ▸ h

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  run : SLPost α → SLPre
  monotone :
    ∀ {Q₁ Q₂ : SLPost α},
      (∀ value, himpl (Q₁ value) (Q₂ value)) →
      himpl (run Q₁) (run Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => SLPost α → SLPre) :=
  ⟨Wp.run⟩

def pure (value : α) : Wp α :=
  ⟨fun Q => Q value, fun hQ => hQ value⟩

def bind (m : Wp α) (next : α → Wp β) : Wp β :=
  ⟨fun Q => m (fun value => next value Q), fun hQ =>
    m.monotone (fun value => (next value).monotone hQ)⟩

/-- Specification weakening is reverse implication between preconditions. -/
instance : LE (Wp α) where
  le w₁ w₂ := ∀ Q, himpl (w₂ Q) (w₁ Q)

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

instance : OrderedMonad Wp where
  bind_mono := Wp.bind_mono

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer.  The encoding is local: `P` is required to describe only part of
the heap, and the postcondition is handed to the continuation through a wand,
so that the frame is threaded automatically. -/
def pp2wp (P : SLPre) (Q : SLPost α) : Wp α where
  run := fun R => P ∗ (Q -∗+ R)
  monotone := by
    intro R₁ R₂ hR
    exact hstar_mono (himpl_refl P)
      (qwand_intro fun value =>
        himpl_trans (qwand_cancel Q R₁ value) (hR value))

def Wp.hexists {ι : Sort _} (f : ι → Wp α) : Wp α where
  run := fun R => _root_.Aeneas.SLPoC.hexists (fun x => f x R)
  monotone := by
    rintro R₁ R₂ hR h ⟨x, hx⟩
    exact ⟨x, (f x).monotone hR h hx⟩

theorem pp2wp_conseq {P : SLPre} {Q R : SLPost α} (hPost : Q ⊢+ R) :
    P ⊢ pp2wp P Q R :=
  himpl_trans (himpl_of_eq (hstar_hempty_r_eq P).symm)
    (hstar_mono (himpl_refl P)
      (qwand_intro fun value =>
        himpl_trans (himpl_of_eq (hstar_hempty_r_eq (Q value))) (hPost value)))

theorem pp2wp_frame {P : SLPre} {Q R : SLPost α} (H : SLProp) :
    pp2wp P Q R ∗ H ⊢ pp2wp P Q (R ∗+ H) :=
  himpl_trans (himpl_of_eq (hstar_assoc_eq P (Q -∗+ R) H))
    (hstar_mono (himpl_refl P)
      (qwand_intro fun value =>
        himpl_trans (himpl_of_eq (hstar_assoc_eq (Q value) (Q -∗+ R) H).symm)
          (hstar_mono (qwand_cancel Q R value) (himpl_refl H))))

/-- The elimination principle of `pp2wp`: the heap splits into the footprint
described by `P` and a frame, and the continuation accepts any heap the
postcondition describes, put back next to that frame. -/
theorem pp2wp_elim {P : SLPre} {Q R : SLPost α} {h : Heap}
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
    qwand_cancel Q R value (h' ∪ h₂) ⟨h', h₂, hDisjoint', rfl, hQ, hWand⟩⟩

theorem Wp.hexists_frame {ι : Sort _} {f : ι → Wp α} {Q : SLPost α}
    (H : SLProp) (hFrame : ∀ x, f x Q ∗ H ⊢ f x (Q ∗+ H)) :
    Wp.hexists f Q ∗ H ⊢ Wp.hexists f (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hx⟩, hH⟩
  exact ⟨x, hFrame x _ ⟨h₁, h₂, hDisjoint, rfl, hx, hH⟩⟩

end Aeneas.SLPoC

/-!
# Separation-logic tactics

A port of the tactic automation of *Software Foundations, Volume 6: Separation
Logic Foundations* (`https://softwarefoundations.cis.upenn.edu/slf-current/`).

| SLF | Here |
|---|---|
| `\-*` / `\--*` | `-∗` (`hwand`) / `-∗+` (`qwand`) |
| `triple_ramified_frame` | `triple_ramified_frame` |
| `xsimpl` | `sl_simpl` (also available as `sl_frame`) |
| `xpull` | `sl_pull_entail` on an entailment, `sl_pull` on a triple |
| `xchange` | `sl_change` |
| `xval` | `sl_val` |
| `xapp` | `sl_app`, and the `step`/`step*` tactics |

The book's `xwp`/`wpgen`/`xlet`/`xseq`/`xif`/`xfun` have no counterpart: they
build a characteristic formula out of a deeply embedded program, whereas here the
programs are shallowly embedded monadic terms and `step` walks them directly.
-/

namespace Aeneas.SLPoC

open Lean Elab Meta Tactic
open scoped SepLogic

/-! ## The `xsimpl` engine

`sl_simpl` is a port of SLF's `xsimpl`; see its documentation below for the
phases it goes through. -/

namespace SLFrame

/-- The `sl_simps` simp attribute.  `sl_frame` and `sl_pull` use it to normalize
separation-logic assertions before extracting/cancelling them: it is where the
lemmas that unfold or fold representation predicates belong (`nodes_cons`,
`nodes_snoc`, …).  This plays the role of SLF's `xchange`, except that the
rewriting is declarative instead of being spelled out at every call site. -/
initialize slSimpExt : SimpExtension ←
  registerSimpAttr `sl_simps "\
    The `sl_simps` attribute registers simp lemmas used by `sl_frame` and \
    `sl_pull` to normalize separation-logic assertions (typically, lemmas that \
    decompose a representation predicate into the cells it owns)."

private def isConnective (e : Expr) : Bool :=
  let head := e.consumeMData.getAppFn
  head.isConstOf ``hstar || head.isConstOf ``hpure ||
    head.isConstOf ``hexists || head.isConstOf ``hempty ||
    -- `hwand` is *defined* as an existential; unfolding it would be a disaster.
    head.isConstOf ``hwand || head.isConstOf ``qwand || head.isConstOf ``hforall

/-- Is `e` a magic wand?  Returns whether it is a postcondition wand. -/
private def wand? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``qwand 3 then some true
  else if e.isAppOfArity ``hwand 2 then some false
  else none

/-- Expose the head connective (`hstar`, `hpure`, `hexists` or `hempty`) of a
separation-logic assertion, by unfolding a definition that is a mere wrapper
around one — `wellFormed s l` is `⌜…⌝ ∗ nodes l`, `isList s vs` is `∃ l, …`.

Exactly one unfolding is performed, and only when it does reveal a connective.
Representation predicates that *compute*, such as `nodes`, are deliberately left
alone: decomposing them is the job of the `sl_simps` lemmas, which would
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
  if fn.isConstOf ``qstar && args.size = 4 then
    return mkApp2 (mkConst ``hstar) (mkApp args[1]! args[3]!) args[2]!
  return e

private partial def flatten (e : Expr) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``hstar && args.size = 2 then
    return (← flatten args[0]!) ++ (← flatten args[1]!)
  if fn.isConstOf ``hempty then
    return #[]
  return #[e]

private def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst ``hempty
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``hstar) atom rest

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
      | (simp only [hstar_hempty_l_eq, hstar_hempty_r_eq] <;>
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
          | (simp only [sl_simps, *]; done)
          | (simp only [sl_simps, *]; grind)
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
not even be mentioned by it, since `?F` was created in an outer context.  This
is exactly the limitation of the plain frame rule that SLF's ramified frame rule
works around.

`Hcallee` may itself be an existential, in which case floating that existential
out would turn the destination into `∃ x, Hcallee' x ∗ ?F` and hide the frame:
the decision must therefore be taken *before* any normalization. -/
private def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``hstar && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

/-- Is the goal a frame-inference goal?  See `frameMVar?`. -/
private def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return false
  return (← frameMVar? (← reducePostApplication args[1]!)).isSome

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Simp.SimpArgs) : TacticM MVarId := do
  /- Restore the goals we are not working on: `Simp.simpAt` acts on the main
     goal, and dropping the others would silently remove them from the state. -/
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Simp.simpAt simpOnly
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
        #[``hstar_hempty_l_eq, ``hstar_hempty_r_eq,
          ``hstar_hexists_l_eq, ``hstar_hexists_r_eq] }

/-- Decompose the representation predicates of an entailment into the cells they
own, using the `sl_simps` set.  Unlike `floatExists` this is not always
desirable, so `sl_frame` only resorts to it when the plain cancellation fails. -/
private def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← slSimpExt.getTheorems] }

/-- Rewrite an assertion into an equivalent one whose connectives are all
visible, by unfolding definitions such as `wellFormed` or `isList` through the
separating conjunctions.  Only delta/beta reduction is involved, so the result is
definitionally equal to the input. -/
private partial def exposeAll (e : Expr) : MetaM Expr := do
  let e ← reducePostApplication e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``hstar && args.size = 2 then
    return mkApp2 (mkConst ``hstar) (← exposeAll args[0]!) (← exposeAll args[1]!)
  return e

/-- Put the entailment of `goal` in the exposed form computed by `exposeAll`. -/
private def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let exposed ← mkAppM ``himpl #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

/-- SLF's `xpull`: introduce the existentials of the left-hand side and move its
pure facts into the local context.  Returns the residual goal. -/
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
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let (sourceFn, sourceArgs) :=
    source.consumeMData.withApp fun fn args => (fn, args)
  if sourceFn.isConstOf ``hexists && sourceArgs.size = 2 then
    let some u := sourceFn.constLevels!.head?
      | throwError "could not determine the universe of {source}"
    let ι := sourceArgs[0]!
    let J := sourceArgs[1]!
    let newType ← withLocalDeclD `x ι fun x => do
      mkForallFVars #[x] (← mkAppM ``himpl #[← Core.betaReduce (mkApp J x), destination])
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``himpl_hexists_l [u]) #[ι, destination, J, newGoal])
    let (_, next) ← newGoal.mvarId!.intro1P
    return ← pullLeft next
  let atoms ← flatten source
  let some i := atoms.findIdx? fun atom =>
      atom.consumeMData.isAppOfArity ``hpure 1
    | return goal
  let atom := atoms[i]!
  let proposition := atom.consumeMData.appArg!
  let rest := mkStar (atoms.eraseIdx! i)
  let newType ← withLocalDeclD `h proposition fun h => do
    mkForallFVars #[h] (← mkAppM ``himpl #[rest, destination])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  let extract := mkAppN (mkConst ``himpl_hpure_l)
    #[proposition, rest, destination, newGoal]
  let reordered := mkApp2 (mkConst ``hstar) atom rest
  let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
  goal.assign (← mkAppM ``himpl_trans #[reorder, extract])
  let (_, next) ← newGoal.mvarId!.intro1P
  pullLeft next

/-- SLF's right-hand-side existential instantiation: replace `∃ x, J x` by
`J ?x` for a fresh metavariable `?x`, to be determined by the cancellation
phase. -/
private partial def instantiateRightExists (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then return goal
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let source := args[0]!
  let destination ← reducePostApplication args[1]!
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``hexists && destArgs.size = 2 do return goal
  let some u := destFn.constLevels!.head?
    | throwError "could not determine the universe of {destination}"
  let ι := destArgs[0]!
  let J := destArgs[1]!
  let witness ← mkFreshExprMVar ι
  let newType ← mkAppM ``himpl #[source, ← Core.betaReduce (mkApp J witness)]
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``himpl_hexists_r [u]) #[ι, source, J, witness, newGoal])
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
  unless fn.isConstOf ``hexists && args.size = 2 do
    return (required, ← mkAppM ``himpl_refl #[required], #[])
  let some u := fn.constLevels!.head?
    | throwError "could not determine the universe of {required}"
  let ι := args[0]!
  let J := args[1]!
  let witness ← mkFreshExprMVar ι
  let body ← Core.betaReduce (mkApp J witness)
  let (peeled, peeledEntailsBody, witnesses) ← peelRequiredExists body
  let bodyEntailsRequired := mkAppN (mkConst ``himpl_hexists_r [u])
    #[ι, body, J, witness, ← mkAppM ``himpl_refl #[body]]
  return (peeled,
    ← mkAppM ``himpl_trans #[peeledEntailsBody, bodyEntailsRequired],
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
      pure (``qwand_intro,
        ← mkAppM ``qimpl #[← mkAppM ``qstar #[args[1]!, residual], args[2]!])
    else
      pure (``hwand_intro,
        ← mkAppM ``himpl #[mkApp2 (mkConst ``hstar) args[0]! residual, args[1]!])
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do
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
      let cancelled := mkApp2 (mkConst ``hstar) (← instantiateMVars required) frame
      let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC source cancelled]
      let weaken ← mkAppM ``hstar_mono
        #[← instantiateMVars weakening, ← mkAppM ``himpl_refl #[frame]]
      goal.assign (← mkAppM ``himpl_trans #[reorder, weaken])
      return true
    let state ← saveState
    /- First try the callee precondition as it stands: it may well be owned as a
       single opaque assertion (an `isList`, say) by the caller.  Only if that
       fails do we open its existentials. -/
    unless ← solveWith original (← mkAppM ``himpl_refl #[original]) #[] do
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
      else if expected.consumeMData.isAppOfArity ``hpure 1 then
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
        let reordered := mkApp2 (mkConst ``hstar) matchedAssertion residual
        let reorderProof ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
        let residualToAbsorber ← proveWand discharger residual absorbingAtom
        let absorbProof ← mkAppM ``hstar_mono
          #[← mkAppM ``himpl_refl #[matchedAssertion], residualToAbsorber]
        pure (mkApp2 (mkConst ``hstar) matchedAssertion absorbingAtom,
          ← mkAppM ``himpl_trans #[reorderProof, absorbProof])
      | none =>
        let discardedAtoms := remaining
        let proof ←
          if discardedAtoms.isEmpty then
            mkAppM ``himpl_of_eq #[← proveEqAC source matchedAssertion]
          else
            let discarded := mkStar discardedAtoms
            let reordered := mkApp2 (mkConst ``hstar) matchedAssertion discarded
            let reorderProof ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
            /- The logic is affine, so whatever the cancellation leaves over is
               discardable — unlike in SLF, where only the pure atoms are. -/
            let eliminateProof ← mkAppM ``hstar_elim_right
              #[matchedAssertion, discarded]
            mkAppM ``himpl_trans #[reorderProof, eliminateProof]
        pure (matchedAssertion, proof)
    let mut current := matchedAssertion
    let mut insertionProof ← mkAppM ``himpl_refl #[current]
    for (pureAtom, pureProof) in generatedPure do
      let insertProof ← mkAppM ``hpure_hstar_intro #[current, pureProof]
      insertionProof ← mkAppM ``himpl_trans #[insertionProof, insertProof]
      current := mkApp2 (mkConst ``hstar) pureAtom current
    let destination ← instantiateMVars destination
    let eqProof ← proveEqAC current destination
    let reorderProof ← mkAppM ``himpl_of_eq #[eqProof]
    let matchedToDestination ← mkAppM ``himpl_trans #[insertionProof, reorderProof]
    goal.assign (← mkAppM ``himpl_trans #[sourceToMatched, matchedToDestination])

partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``qimpl && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal discharger nextGoal
  else
    /- Two passes.  The first one only reorganizes the connectives; it is the one
       that succeeds when the assertion to produce is a representation predicate
       applied to a metavariable, which no rewriting could ever match.  The
       second one additionally decomposes the representation predicates with the
       `sl_simps` set, which is what is needed when the two sides of the
       entailment own the same cells but describe them differently. -/
    let pass (decomposing : Bool) : TacticM Unit := do
      let goal ← if decomposing then decompose goal else pure goal
      /- Decide here whether we are inferring a frame: `floatExists` below can
         turn `Hcallee ∗ ?F` into `∃ x, Hcallee' x ∗ ?F` and hide `?F`. -/
      if ← isFrameInference goal then
        /- Expose before decomposing again: `sl_simps` has no lemma for the
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
        throwError "sl_frame failed.\n\
          {firstError.toMessageData}\n\
          and, after decomposing the assertions with `sl_simps`:\n\
          {secondError.toMessageData}"

/-- SLF's `xpull`, on an entailment: only the left-hand side is touched. -/
partial def pullGoal (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then
    throwError "sl_pull_entail: this is a frame-inference goal.  Extracting anything \
      from its left-hand side would lose it from the frame, which was created in \
      an outer context; pull at the level of the triple instead, with `sl_pull`."
  let target ← instantiateMVars (← goal.getType)
  if target.consumeMData.isAppOfArity ``qimpl 3 then
    let (_, next) ← goal.intro1P
    pullLeft next
  else
    pullLeft goal

end

end SLFrame

/-- Prove a separation-logic entailment `H₁ ⊢ H₂` (or a postcondition entailment
`Q₁ ⊢+ Q₂`), in the style of SLF's `xsimpl`:

1. the existentials of the left-hand side are introduced and its pure facts are
   moved into the local context (SLF's `xpull`);
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

`sl_frame by tac` uses `tac` instead of the default chain to discharge the pure
side-goals of step 4.  Lean's `sym => …` symbolic-simulation mode is a good
choice when the default chain is too slow or too unpredictable, since it makes
the normalization explicit instead of relying on backtracking:

```
register_sym_simp slPure where
  post := ground >> rewrite [headPtr_nil, lastPtr_nil, headPtr_cons,
    lastPtr_singleton, lastPtr_snoc] with self

example … := by
  sl_frame by sym => first ((simp slPure); finish) (simp slPure) (finish)
```
-/
syntax (name := slFrame) "sl_frame" (" by " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| sl_frame $[by $tac?]?) => Tactic.focus do withMainContext do
  let discharger : Option Syntax.Tactic := tac?.map fun tac => ⟨tac.raw⟩
  let localAsms :=
    (← (← getLCtx).getAssumptions).map LocalDecl.fvarId |>.toArray
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { hypsToUse := localAsms }
    (.targets #[] true)
  if !(← getGoals).isEmpty then
    let goal ← getMainGoal
    SLFrame.solveGoal discharger goal
    replaceMainGoal []

/-- Normalize the separating conjunctions of the goal: float the existentials out of them, drop
the `emp`s, and reassociate to the right.

Also collapses a ramified wand whose antecedent is a pure equality
(`himpl_qwand_hpure_eq`): that is the shape a terminal return leaves behind, and
frame inference cannot cancel it on its own. -/
elab "sl_norm" : tactic => withMainContext do
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``hstar_hempty_l_eq, ``hstar_hempty_r_eq,
          ``hstar_hexists_l_eq, ``hstar_hexists_r_eq, ``hstar_assoc_eq,
          ``himpl_qwand_hpure_eq] }
    (.targets #[] true)

/-- One step of `sl_pull`: peel a quantifier or a pure fact off the precondition
of a triple.  Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective: applying `triple_hexists` or `triple_hpure` blindly
would let the unifier see through `hstar`/`hpure` down to the raw heap predicate
and peel a quantifier of the *model* instead. -/
elab "sl_pull_step" : tactic => withMainContext do
  /- Float the existentials out of the separating conjunctions and drop the
     `emp`s left behind by previous steps, so that the head connective of the
     precondition is the one we want to peel. -/
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``hstar_hexists_l_eq, ``hstar_hexists_r_eq,
          ``hstar_hempty_l_eq, ``hstar_hempty_r_eq] }
    (.targets #[] true)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 do
    throwError "sl_pull_step: the goal is not a separation-logic triple"
  let precondition ← SLFrame.exposeConnective args[1]!
  let head := precondition.consumeMData.getAppFn
  let leadingPure ←
    if precondition.consumeMData.isAppOfArity ``hstar 2 then
      pure ((← SLFrame.exposeConnective precondition.consumeMData.appFn!.appArg!)
        |>.consumeMData.isAppOfArity ``hpure 1)
    else pure false
  let lemmaName ←
    if head.isConstOf ``hexists then pure `Aeneas.SLPoC.triple_hexists
    else if head.isConstOf ``hpure then pure `Aeneas.SLPoC.triple_hpure'
    else if leadingPure then pure `Aeneas.SLPoC.triple_hpure
    else
      throwError "sl_pull_step: the precondition has no quantifier or pure fact \
        left to extract:\n{precondition}"
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, precondition, args[2]!, args[3]!])
  replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))

/-- SLF's `xpull`, for triples: move the existentials and the pure facts of the
precondition into the local context.

`sl_pull` peels as many of them as it can, using inaccessible names.
`sl_pull p₁ ... pₙ` peels exactly `n` of them, destructuring the `i`-th one with
the `rintro` pattern `pᵢ`, e.g. `sl_pull l rfl` or `sl_pull ⟨hhead, htail⟩`.

Pure facts are *removed* from the precondition, which is often not what a
subsequent `step` needs; use `sl_pull_keep` when only the local hypothesis is
wanted. -/
syntax (name := slPull) "sl_pull" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| sl_pull $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (sl_pull_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (sl_pull_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

/-- Whether a quantifier or a pure fact can be peeled off `pre` without unfolding it: an opened
representation predicate is one the frame inference of a later `step` can no longer match. -/
private def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``hexists 2 || pre.isAppOfArity ``hpure 1 then true
  else if pre.isAppOfArity ``hstar 2 then
    pre.appFn!.appArg!.consumeMData.isAppOfArity ``hpure 1
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity `Aeneas.SLPoC.triple 4 &&
      isPullable target.getAppArgs[1]! do return goal
  setGoals [goal]
  let state ← saveState
  try
    evalTactic (← `(tactic| sl_pull_step))
  catch _ =>
    state.restore
    return goal
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

/-- `sl_pull` restricted to what the precondition exposes without being unfolded; see
`isPullable`. -/
elab "sl_pull_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

/-- One step of `sl_pull_keep`: copy the leading pure fact of the precondition of
a triple into the local context, *without* removing it from the precondition.

`sl_pull_step` consumes the fact, which is what SLF's `xpull` does but is often
the wrong thing here: the assertion has to keep it for the framing of the later
steps (this is why `sl_pull` before a `step` can turn a working proof into a
failing one).  Copying is always sound, and it is what makes the pointer of a
callee's precondition (`s.head.get!`, say) reducible to the one the assertion
owns.

Fails when the fact is already in the context, so that `repeat` terminates. -/
elab "sl_pull_keep_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 do
    throwError "sl_pull_keep_step: the goal is not a separation-logic triple"
  let precondition ← SLFrame.exposeConnective args[1]!
  unless precondition.consumeMData.isAppOfArity ``hstar 2 do
    throwError "sl_pull_keep_step: the precondition is not a separating conjunction"
  let leading ← SLFrame.exposeConnective precondition.consumeMData.appFn!.appArg!
  unless leading.consumeMData.isAppOfArity ``hpure 1 do
    throwError "sl_pull_keep_step: the precondition does not start with a pure fact"
  let proposition := leading.consumeMData.appArg!
  if ← (← getLCtx).anyM fun decl =>
      pure !decl.isImplementationDetail <&&> isDefEq decl.type proposition then
    throwError "sl_pull_keep_step: this pure fact is already in the context"
  let exposed := mkApp2 (mkConst ``hstar) leading precondition.consumeMData.appArg!
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, exposed, args[2]!, args[3]!])
  let [next] ← goal.apply
    (← mkConstWithFreshMVarLevels `Aeneas.SLPoC.triple_hpure_keep)
    | throwError "sl_pull_keep_step: unexpected number of goals"
  let (_, next) ← next.intro1P
  /- Put the precondition back in its original, folded form: only the local
     context should record that the step happened. -/
  replaceMainGoal
    [← next.change
      (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, args[1]!, args[2]!, args[3]!])]

/-- Copy the pure facts of the precondition of a triple into the local context,
leaving the precondition untouched.  See `sl_pull_keep_step`. -/
macro "sl_pull_keep" : tactic => `(tactic| repeat (sl_pull_keep_step; rename_i _))

/-- SLF's `xsimpl`.  `sl_frame` is the same tactic under the name that describes
what `step` uses it for. -/
syntax "sl_simpl" (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| sl_simpl) => `(tactic| sl_frame)
  | `(tactic| sl_simpl by $tac) => `(tactic| sl_frame by $tac)

/-- SLF's `xpull`, on an entailment `H₁ ⊢ H₂` or `Q₁ ⊢+ Q₂`: introduce the
existentials of the left-hand side and move its pure facts into the local
context, leaving the right-hand side alone.

Use it when the witness the right-hand side needs depends on a variable bound on
the left: `sl_simpl` would otherwise pick the metavariable for the right-hand
side *before* that variable exists.  This is SLF's canonical
`(∃ n, p ↦ n) ⊢ (∃ m, p ↦ (m + 1))` example. -/
elab "sl_pull_entail" : tactic => Tactic.focus do withMainContext do
  replaceMainGoal [← SLFrame.pullGoal (← getMainGoal)]

/-! ## `xchange` -/

/-- The rule behind `sl_change`: rewrite a part of the left-hand side of an
entailment with an entailment of its own. -/
theorem himpl_xchange {H₁ H₂ H₃ H₄ : SLProp} (hPart : H₁ ⊢ H₂)
    (hRest : H₂ ∗ H₃ ⊢ H₄) : H₁ ∗ H₃ ⊢ H₄ :=
  himpl_trans (hstar_mono hPart (himpl_refl H₃)) hRest

namespace SLFrame

/-- Rewrite the assertion `H` (the left-hand side of an entailment, or the
precondition of a triple) using `lemma : A ⊢ B` or `lemma : A = B`, replacing the
atom `A` of `H` by `B`.  Returns the rewritten assertion and a proof of
`H ⊢ rewritten`. -/
def xchangeAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  /- Accept both an entailment and an equality, in either direction for the
     latter (SLF's `xchange` does the same). -/
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``himpl 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, ← mkAppM ``himpl_of_eq #[rule])
    else
      throwError "sl_change expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let atoms ← flatten assertion
  /- The rewritten part may be a separating conjunction of several atoms, which
     do not have to be adjacent in `assertion`. -/
  let some restAtoms ← removeMatches atoms (← flatten lhs)
    | throwError "sl_change: {lhs}\nis not part of\n{assertion}"
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``hstar) (← instantiateMVars lhs) rest
  let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC assertion reordered]
  let rewritten := mkApp2 (mkConst ``hstar) (← instantiateMVars rhs) rest
  let change ← mkAppM ``hstar_mono #[entailment, ← mkAppM ``himpl_refl #[rest]]
  return (rewritten, ← mkAppM ``himpl_trans #[reorder, change])

end SLFrame

/-- SLF's `xchange`: rewrite part of the current resources with an entailment.

`sl_change M`, for `M : A ⊢ B` (or `M : A = B`), replaces the assertion `A` by
`B` in the left-hand side of the entailment, or in the precondition of the
triple, that the goal states.  This is how a representation predicate is opened
or closed when plain cancellation cannot see through it.

Unlike `rw`, `M` need not be an equality and `A` need not occur syntactically:
it only has to be one of the `∗`-separated atoms, up to unification. -/
elab "sl_change" rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``himpl && args.size = 2 then
    let (rewritten, proof) ← SLFrame.xchangeAssertion args[0]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``himpl #[rewritten, args[1]!])
    goal.assign (← mkAppM ``himpl_trans #[proof, next])
    replaceMainGoal [next.mvarId!]
  else if fn.isConstOf `Aeneas.SLPoC.triple && args.size = 4 then
    let (rewritten, proof) ← SLFrame.xchangeAssertion args[1]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppOptM `Aeneas.SLPoC.triple #[args[0]!, rewritten, args[2]!, args[3]!])
    let qrefl ← withLocalDeclD `value args[0]! fun value => do
      mkLambdaFVars #[value] (← mkAppM ``himpl_refl #[mkApp args[3]! value])
    goal.assign (← mkAppM `Aeneas.SLPoC.triple_conseq #[next, proof, qrefl])
    replaceMainGoal [next.mvarId!]
  else
    throwError "sl_change expects an entailment or a triple, got\n{target}"

/-! ## `xval` and `xapp` -/

/-- SLF's `xval`: reduce a triple about a terminal `pure v` to the entailment
`P ⊢ Q v`. -/
macro "sl_val" : tactic => `(tactic| apply triple_pure)

/-- SLF's `xapp`: apply a specification to the goal, framing the resources it
does not need through the ramified frame rule, and discharge the resulting
entailment with `sl_simpl`.

`sl_app thm` handles a terminal call; use `step with thm` for a call followed by
a continuation. -/
syntax "sl_app" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| sl_app $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine triple_ramified_frame $thm ?_)
      | none => `(tactic| refine triple_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; sl_simpl))
    | some tac => `(tactic| ($apply; sl_simpl by $tac))

/-- Re-state an already-proved triple under a weaker (usually more abstract)
postcondition: `sl_conseq thm` keeps the precondition as is and discharges the
new postcondition with `sl_frame` for every result value. -/
macro "sl_conseq " thm:term : tactic =>
  `(tactic| (apply triple_conseq $thm (himpl_refl _) <;> (intro _ <;> sl_frame)))

end Aeneas.SLPoC
