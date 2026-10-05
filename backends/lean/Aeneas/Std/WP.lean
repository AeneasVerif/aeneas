module
public import Aeneas.Std.Primitives
public import Aeneas.Std.Delab
public meta import AeneasMeta.Simp
public import Aeneas.Tactic.Solver.Grind.Init
public import Aeneas.Tactic.Step.DspecInduction
public meta import Aeneas.Std.Spec
public meta import Aeneas.Std.Delab
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public import Aeneas.Data.Coinductive.ITreeWP
public import Aeneas.SepLogic
import all Init.Internal.Order.Basic
public section

namespace Aeneas.Std.WP

open Std Result
open Aeneas.Data.Coinductive
open Lean.Order
open Aeneas.SepLogic

@[expose] def Post α := (α -> Prop)
@[expose] def Pre := Prop

@[expose] def Wp α := Post α → Pre

@[expose] def wp_return (x:α) : Wp α := fun p => p x

section ResultImplementation

unseal Result

@[expose] section

@[reducible]
def effectWP : EffectWP RustEffect where
  State := Heap
  wp effect C h :=
    match effect with
    | .guardedModify _ pre modify =>
        ∃ hPre : pre h, C (.up (modify h hPre).1) (modify h hPre).2
    | .fail _ => False

instance : EffectWP.Monotone effectWP where
  wp_mono {effect} _ _ hC _ hEvent := by
    cases effect with
    | guardedModify => exact hEvent.imp fun _ hNext => hC _ _ hNext
    | fail => exact hEvent.elim

instance : EffectWP.Conjunctive effectWP where
  wp_conj {effect} _ Demands := by
    rintro ⟨C₀, hC₀⟩ hAll
    cases effect with
    | guardedModify => exact ⟨(hAll C₀ hC₀).1, fun C hC => (hAll C hC).2⟩
    | fail => exact (hAll C₀ hC₀).elim

instance : EffectWP.NoMiracle effectWP where
  wp_noMiracle effect _ hWp := by
    cases effect with
    | guardedModify => exact hWp.2
    | fail => exact hWp

abbrev rawIwp (total:Bool) (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  if total then DWP effectWP m (fun value h' => Q value h') h
  else DWLP effectWP m (fun value h' => Q value h') h

def iwp (total:Bool) (m : Result α) (Q : IPost α) : IProp where
  holds owned :=
    ∀ F h, (owns owned ∗ F) h → rawIwp total m (Q ∗+ F) h
  up_closed hWp hSub F h hPre :=
    hWp F h (sep_mono
      (fun _ hOwns => hSub.trans hOwns)
      (entails_refl F) h hPre)

/-- Total-correctness separation-logic specification -/
def ispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  P ⊢ iwp true m Q

/-- Partial-correctness separation-logic specification -/
def dispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  P ⊢ iwp false m Q

/-- Total-correctness pure specification -/
def spec (m : Result α) (p : Post α) : Prop :=
  ispec emp m (fun value => ⌜p value⌝)

/-- Partial-correctness pure specification -/
def dspec (m : Result α) (p : Post α) : Prop :=
  dispec emp m (fun value => ⌜p value⌝)

theorem ispec_iff {P : IPre} {m : Result α} {Q : IPost α} :
    ispec P m Q ↔
      ∀ F h, (P ∗ F) h → DWP effectWP m (fun value h' => (Q ∗+ F) value h') h := by
  constructor
  · rintro hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, hP, hF⟩
    exact hSpec h₁ hP F _ ⟨h₁, h₂, hDisjoint, rfl, Heap.Sub.refl _, hF⟩
  · intro hSpec owned hP F _
    rintro ⟨h₁, h₂, hDisjoint, rfl, hOwned, hF⟩
    exact hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, P.up_closed hP hOwned, hF⟩

theorem dispec_iff {P : IPre} {m : Result α} {Q : IPost α} :
    dispec P m Q ↔
      ∀ F h, (P ∗ F) h → DWLP effectWP m (fun value h' => (Q ∗+ F) value h') h := by
  constructor
  · rintro hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, hP, hF⟩
    exact hSpec h₁ hP F _ ⟨h₁, h₂, hDisjoint, rfl, Heap.Sub.refl _, hF⟩
  · intro hSpec owned hP F _
    rintro ⟨h₁, h₂, hDisjoint, rfl, hOwned, hF⟩
    exact hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, P.up_closed hP hOwned, hF⟩

theorem ispec_dispec {α : Type u} {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) : dispec P m Q := by
  rw [ispec_iff] at hTriple
  rw [dispec_iff]
  intro F h hPre
  exact (hTriple F h hPre).toPartial

theorem spec_ispec (m : Result α) (Q : Post α) : spec m Q → ispec emp m (fun value => ⌜Q value⌝) := id

theorem dspec_dispec (m : Result α) (Q : Post α) : dspec m Q → dispec emp m (fun value => ⌜Q value⌝) := id

theorem spec_dspec (α) (x : Result α) (p: Post α) : spec x p → dspec x p := ispec_dispec

theorem spec_dispec (m : Result α) (Q : Post α) : spec m Q → dispec emp m (fun value => ⌜Q value⌝) :=
  ispec_dispec

theorem ispec_spec (m : Result α) (Q : Post α) :
    ispec emp m (fun value => ⌜Q value⌝) → spec m Q := id

theorem ispec_dspec (m : Result α) (Q : Post α) :
    ispec emp m (fun value => ⌜Q value⌝) → dspec m Q := ispec_dispec

theorem dispec_dspec (m : Result α) (Q : Post α) :
    dispec emp m (fun value => ⌜Q value⌝) → dspec m Q := id

private theorem rawIwp_admissible (Q : IPost α) (h : Heap) :
    admissible (fun m : Result α => rawIwp false m Q h) :=
  DWLP.admissible effectWP _ h

theorem dispec_admissible {α : Type u} (P : IPre) (Q : IPost α) :
    admissible (fun m : Result α => dispec P m Q) := by
  simp only [dispec_iff]
  intro c hc hAll F h hPre
  exact rawIwp_admissible (Q ∗+ F) h c hc fun x hx => hAll x hx F h hPre

@[dspec_admissible]
theorem dispec_func_admissible {ι : Sort v} {α : Type u} (arg : ι) (P : IPre) (Q : IPost α) :
    admissible (fun f : ι → Result α => dispec P (f arg) Q) :=
  admissible_apply (fun _ m => dispec P m Q) arg (dispec_admissible P Q)

theorem dspec_admissible {α} (p : Post α) :
    admissible (fun x => dspec x p) :=
  dispec_admissible emp (fun value => ⌜p value⌝)

end

/-- The shape the `dspec_induction` tactic needs to discharge the admissibility
side-goal it generates for a partial specification about a recursive function. -/
@[dspec_admissible]
theorem dspec_func_admissible {α : Sort v} {β} (arg : α) (p : Post β) :
    admissible (fun f : α → Result β => dspec (f arg) p) :=
  admissible_apply (fun _ m => dspec m p) arg (dspec_admissible p)

/-- Variant of `uncurry` used to decompose tuples in post-conditions.

Similar to `uncurry` but delaborated differently:
`uncurry'` is delaborated as `x y => ...` (separate binders), while
`uncurry` is delaborated as `(x, y) => ...` (tuple binder).
We use this in the Hoare triple notation `⦃ ⦄`.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to
`spec (f 0) (uncurry' fun x => uncurry' fun y z => ...)`.
-/

@[expose]
def uncurry' {α β γ : Type _} (p : α → β → γ) : α × β → γ :=
  fun (x, y) => p x y

@[simp] theorem uncurry'_pair x y (p : α → β → γ) : uncurry' p (x, y) = p x y := by simp [uncurry']
@[defeq] theorem uncurry'_eq x (p : α → β → γ) : uncurry' p x = p x.fst x.snd := by simp [uncurry']

@[simp, grind =, agrind =]
theorem ispec_ok (x : α) : ispec P (ok x) Q ↔ P ⊢ Q x := by
  constructor
  · intro hTriple h hP
    rw [ispec_iff] at hTriple
    have hPost := DWP.ret_iff.mp (hTriple emp h ((sep_emp_r P).mpr h hP))
    exact (sep_emp_r (Q x)).mp h hPost
  · intro hPost
    rw [ispec_iff]
    intro F h hPre
    exact DWP.ret_iff.mpr (sep_mono hPost (entails_refl F) h hPre)

/-- A guarded modification is correct iff it is local: the guard holds and every frame is kept. -/
theorem ispec_guardedModify {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {P : IPre} {Q : IPost α}
    (hLocal : ∀ h, P h → ∀ frame, PartialCommMonoid.Compatible h frame →
      ∃ hPre : pre (h ∪ frame), ∃ h',
        PartialCommMonoid.Compatible h' frame ∧
        (modify (h ∪ frame) hPre).2 = h' ∪ frame ∧
        Q (modify (h ∪ frame) hPre).1 h') :
    ispec P (Result.guardedModify pre modify) Q := by
  rw [ispec_iff]
  rintro F h ⟨owned, framed, hDisjoint, rfl, hP, hF⟩
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hLocal owned hP framed hDisjoint
  refine DWP.vis (θ := effectWP)
    (effect := RustEffect.Input.guardedModify _ pre modify) ⟨hPre, ?_⟩
  rw [hModify]
  exact DWP.ret_iff.mpr ⟨h', framed, hDisjoint', rfl, hPost, hF⟩

@[simp, grind =, agrind =]
theorem ispec_fail (e : Error) : ispec P (fail e) Q ↔ P ⊢ ⌜False⌝ := by
  constructor
  · intro hTriple h hP
    rw [ispec_iff] at hTriple
    exact (hTriple emp h ((sep_emp_r P).mpr h hP)).vis_view
  · intro hFalse h hP
    exact (hFalse h hP).elim

@[simp, grind =, agrind =]
theorem ispec_div :
    ispec P (div : Result α) Q ↔ P ⊢ ⌜False⌝ := by
  constructor
  · intro hTriple h hP
    rw [ispec_iff] at hTriple
    exact (hTriple emp h ((sep_emp_r P).mpr h hP)).div_false
  · intro hFalse h hP
    exact (hFalse h hP).elim

theorem ispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (P ∗ H) m (Q ∗+ H) := by
  rw [ispec_iff] at hTriple ⊢
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

theorem ispec_frame_left {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (H ∗ P) m (fun value => H ∗ Q value) := by
  rw [ispec_iff] at hTriple ⊢
  intro F h hPre
  have hSwapped : (P ∗ (H ∗ F)) h :=
    (sep_assoc P H F).mp h
      ((sep_mono (sep_comm H P).mp (entails_refl F)) h hPre)
  refine (hTriple (H ∗ F) h hSwapped).mono fun value heap hPost => ?_
  exact (sep_mono (sep_comm (Q value) H).mp (entails_refl F)) heap
    ((sep_assoc (Q value) H F).mpr heap hPost)

/-- Mono rule used by `step`. -/
theorem ispec_mono {α : Type u} {P Pm : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : ispec Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    ispec P m Q := by
  have hFramed := ispec_frame hStep (Qm -∗+ Q)
  rw [ispec_iff] at hFramed ⊢
  intro F h hPre
  have hSpec := hFramed F h (sep_mono hRamified (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (postWand_cancel Qm Q value) (entails_refl F)

theorem ispec_and {α : Type u} {P : IPre} {m : Result α} {Q₁ Q₂ : IPost α}
    (h₁ : ispec P m Q₁) (h₂ : ispec P m Q₂) :
    ispec P m (fun value => iprop(Q₁ value ∧ Q₂ value)) := by
  rw [ispec_iff] at h₁ h₂ ⊢
  rintro F _ ⟨owned, framed, hCompatible, rfl, hP, hF⟩
  have hPre : (P ∗ owns framed) (owned ∪ framed) :=
    ⟨owned, framed, hCompatible, rfl, hP, Heap.Sub.refl framed⟩
  have hBoth := DWP.and_iff.mpr
    ⟨h₁ (owns framed) _ hPre, h₂ (owns framed) _ hPre⟩
  refine hBoth.mono fun value heap hPost => ?_
  exact (sep_mono (entails_refl _) (fun _ hSub => F.up_closed hF hSub)) heap
    ((sep_iand_owns (Q₁ value) (Q₂ value) framed).mpr heap hPost)

/-- Bind rule used by `step`. -/
theorem ispec_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β} {m : Result α} {Qm : IPost α}
    (hStep : ispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, ispec (Qm value ∗ F) (next value) Q) :
    ispec P (Aeneas.Std.bind m next) Q := by
  have hFirst : ispec P m (Qm ∗+ F) :=
    ispec_mono (ispec_frame hStep F)
      (entails_trans hPre (entails_sep_postWand _ (fun _ => entails_refl _)))
  simp only [ispec_iff] at hFirst hNext ⊢
  intro frame h hP
  apply (hFirst frame h hP).bind
  intro value h' hPost
  exact hNext value frame h' hPost

theorem ispec_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    ispec (⌜P⌝ ∗ H) m Q ↔ (P → ispec H m Q) := by
  constructor
  · intro hTriple hP
    exact ispec_mono hTriple (entails_trans (pure_sep_intro H hP)
      (entails_sep_postWand _ (fun _ => entails_refl _)))
  · intro hTriple
    simp only [ispec_iff] at hTriple ⊢
    intro F h hPre
    have ⟨hP, hHF⟩ :=
      (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
    exact hTriple hP F h hHF

theorem ispec_ipure_iff {P : Prop} {m : Result α} {Q : IPost α} :
    ispec ⌜P⌝ m Q ↔ (P → ispec emp m Q) := by
  rw [← sep_emp_r_eq ⌜P⌝]
  exact ispec_ipure

/-- Copy a pure fact of the precondition into the context without consuming it. -/
theorem ispec_ipure_keep {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    ispec (⌜P⌝ ∗ H) m Q ↔ (P → ispec (⌜P⌝ ∗ H) m Q) :=
  ⟨fun hTriple _ => hTriple,
   fun hTriple => ispec_ipure.mpr fun hP => ispec_ipure.mp (hTriple hP) hP⟩

theorem ispec_exists {ι : Sort _} {J : ι → IPre} {m : Result α} {Q : IPost α} :
    ispec iprop(∃ x, J x) m Q ↔ ∀ x, ispec (J x) m Q := by
  constructor
  · intro hTriple x
    exact fun h hJ => hTriple h ⟨x, hJ⟩
  · intro hTriple
    simp only [ispec_iff] at hTriple ⊢
    intro F h hPre
    obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
    exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

private theorem dispec_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) {h : Heap} (hPre : P h) :
    rawIwp false m Q h := by
  rw [dispec_iff] at hTriple
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact hSpec.mono fun value => sep_elim_right (Q value) emp

@[simp, grind =, agrind =]
theorem dispec_ok {α : Type u} {P : IPre} {Q : IPost α} (x : α) :
    dispec P (ok x) Q ↔ P ⊢ Q x := by
  constructor
  · intro hTriple h hP
    rw [dispec_iff] at hTriple
    have hPost := DWLP.ret_iff.mp (hTriple emp h ((sep_emp_r P).mpr h hP))
    exact (sep_emp_r (Q x)).mp h hPost
  · intro hPost
    rw [dispec_iff]
    intro F h hPre
    exact DWLP.ret_iff.mpr (sep_mono hPost (entails_refl F) h hPre)

theorem dispec_div {P : IPre} {Q : IPost α} :
    dispec P (div : Result α) Q := by
  rw [dispec_iff]
  intro _ _ _
  exact DWLP.div

theorem dispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) (H : IProp) : dispec (P ∗ H) m (Q ∗+ H) := by
  rw [dispec_iff] at hTriple ⊢
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

theorem dispec_mono {α : Type u} {P Pm : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : dispec Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dispec P m Q := by
  have hFramed := dispec_frame hStep (Qm -∗+ Q)
  rw [dispec_iff] at hFramed ⊢
  intro F h hPre
  have hSpec := hFramed F h (sep_mono hRamified (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (postWand_cancel Qm Q value) (entails_refl F)

theorem dispec_and {α : Type u} {P : IPre} {m : Result α} {Q₁ Q₂ : IPost α}
    (h₁ : dispec P m Q₁) (h₂ : dispec P m Q₂) :
    dispec P m (fun value => iprop(Q₁ value ∧ Q₂ value)) := by
  rw [dispec_iff] at h₁ h₂ ⊢
  rintro F _ ⟨owned, framed, hCompatible, rfl, hP, hF⟩
  have hPre : (P ∗ owns framed) (owned ∪ framed) :=
    ⟨owned, framed, hCompatible, rfl, hP, Heap.Sub.refl framed⟩
  have hBoth := DWLP.and_iff.mpr
    ⟨h₁ (owns framed) _ hPre, h₂ (owns framed) _ hPre⟩
  refine hBoth.mono fun value heap hPost => ?_
  exact (sep_mono (entails_refl _) (fun _ hSub => F.up_closed hF hSub)) heap
    ((sep_iand_owns (Q₁ value) (Q₂ value) framed).mpr heap hPost)

theorem dispec_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β} {m : Result α} {Qm : IPost α}
    (hStep : dispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, dispec (Qm value ∗ F) (next value) Q) :
    dispec P (Aeneas.Std.bind m next) Q := by
  have hFirst : dispec P m (Qm ∗+ F) :=
    dispec_mono (dispec_frame hStep F)
      (entails_trans hPre (entails_sep_postWand _ (fun _ => entails_refl _)))
  simp only [dispec_iff] at hFirst hNext ⊢
  intro frame h hP
  apply (hFirst frame h hP).bind
  intro value h' hPost
  exact hNext value frame h' hPost

theorem dispec_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    dispec (⌜P⌝ ∗ H) m Q ↔ (P → dispec H m Q) := by
  constructor
  · intro hTriple hP
    exact dispec_mono hTriple (entails_trans (pure_sep_intro H hP)
      (entails_sep_postWand _ (fun _ => entails_refl _)))
  · intro hTriple
    simp only [dispec_iff] at hTriple ⊢
    intro F h hPre
    have ⟨hP, hHF⟩ := (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
    exact hTriple hP F h hHF

theorem dispec_ipure_iff {P : Prop} {m : Result α} {Q : IPost α} :
    dispec ⌜P⌝ m Q ↔ (P → dispec emp m Q) := by
  rw [← sep_emp_r_eq ⌜P⌝]
  exact dispec_ipure

theorem dispec_ipure_keep {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    dispec (⌜P⌝ ∗ H) m Q ↔ (P → dispec (⌜P⌝ ∗ H) m Q) :=
  ⟨fun hTriple _ => hTriple,
   fun hTriple => dispec_ipure.mpr fun hP => dispec_ipure.mp (hTriple hP) hP⟩

theorem dispec_exists {ι : Sort _} {J : ι → IPre} {m : Result α} {Q : IPost α} :
    dispec iprop(∃ x, J x) m Q ↔ ∀ x, dispec (J x) m Q := by
  constructor
  · intro hTriple x
    exact fun h hJ => hTriple h ⟨x, hJ⟩
  · intro hTriple
    simp only [dispec_iff] at hTriple ⊢
    intro F h hPre
    obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
    exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩


theorem dispec_admissible_pi {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible
      (fun f : ι → Result α => ∀ x, dispec (P x) (f x) (Q x)) :=
  Lean.Order.admissible_pi_apply (fun x m => dispec (P x) m (Q x))
    fun x => dispec_admissible (P x) (Q x)

theorem dispec_admissible_forall {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible (fun m : Result α => ∀ x, dispec (P x) m (Q x)) :=
  Lean.Order.admissible_pi _ fun x => dispec_admissible (P x) (Q x)

attribute [simp] entails_emp_ipure_iff

@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x :=
  (ispec_ok x).trans (entails_emp_ipure_iff (p x))

@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False :=
  (ispec_fail e).trans (entails_emp_ipure_iff False)

@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False :=
  ispec_div.trans (entails_emp_ipure_iff False)

/-! ### `spec_*` for tuple posts

Needed now with the new `uncurry`-based pattern matching. -/

@[simp, grind =, agrind =]
theorem spec_ok_pair {α β} (a : α) (b : β) (f : α → β → Prop) :
    spec (ok (a, b)) (uncurry f) ↔ f a b := by
  simp [spec_ok]

@[simp, grind =, agrind =]
theorem spec_fail_pair (e : Error) (f : α → β → Prop) :
    spec (fail e) (uncurry f) ↔ False := by simp

@[simp, grind =, agrind =]
theorem spec_div_pair (f : α → β → Prop) :
    spec div (uncurry f) ↔ False := by simp

/-- Mono rule used by `step`. -/
theorem spec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
    (∀ x, P₀ x → P₁ x) → spec m P₁ :=
  fun hMonPost => ispec_mono h (entails_sep_postWand _ (fun value _ => hMonPost value))

theorem spec_and {m : Result α} {p q : Post α} (h₁ : spec m p) (h₂ : spec m q) :
    spec m (fun value => p value ∧ q value) :=
  ispec_and h₁ h₂

/-- Bind rule used by `step`. It is stated on `Std.bind` rather than on `>>=`, which is
what a translated program binds with. -/
theorem spec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    spec m Pₘ →
    (∀ x, Pₘ x → spec (k x) Pₖ) →
    spec (Std.bind m k) Pₖ :=
  fun hm hk =>
    ispec_bind hm (sep_emp_r emp).mpr fun value =>
      ispec_mono (ispec_ipure_iff.mpr (hk value)) (entails_trans (sep_emp_r _).mp
        (entails_sep_postWand _ (fun _ => entails_refl _)))

theorem spec_exists {m : Result α} {p : Post α} (h : spec m p) : ∃ value, p value := by
  have hEmp : ((emp : IPre) ∗ emp) (∅ : Heap) := (sep_emp_r emp).mpr ∅ trivial
  obtain ⟨value, heap, hPost⟩ := DWP.exists (ispec_iff.mp h emp ∅ hEmp)
  exact ⟨value, (pure_holds heap).mp ((sep_emp_r _).mp heap hPost)⟩

-- `dspec` theorems
@[simp, grind =, agrind =]
theorem dspec_ok (x : α) : dspec (ok x) p ↔ p x :=
  (dispec_ok x).trans (entails_emp_ipure_iff (p x))

@[simp, grind =, agrind =]
theorem dspec_fail (e : Error) : dspec (fail e) p ↔ False :=
  iff_false_intro fun hSpec => (dispec_apply hSpec (h := ∅) trivial).vis_view

@[simp, grind =, agrind =]
theorem dspec_div : dspec (div : Result α) p ↔ True :=
  iff_true_intro dispec_div

theorem dspec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : dspec m P₀):
    (∀ x, P₀ x → P₁ x) → dspec m P₁ :=
  fun hMonPost => dispec_mono h (entails_sep_postWand _ (fun value _ => hMonPost value))

theorem dspec_and {m : Result α} {p q : Post α} (h₁ : dspec m p) (h₂ : dspec m q) :
    dspec m (fun value => p value ∧ q value) :=
  dispec_and h₁ h₂

theorem dspec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    dspec m Pₘ →
    (∀ x, Pₘ x → dspec (k x) Pₖ) →
    dspec (Std.bind m k) Pₖ :=
  fun hm hk =>
    dispec_bind hm (sep_emp_r emp).mpr fun value =>
      dispec_mono (dispec_ipure_iff.mpr (hk value)) (entails_trans (sep_emp_r _).mp
        (entails_sep_postWand _ (fun _ => entails_refl _)))

attribute [irreducible] dispec

end ResultImplementation

end Aeneas.Std.WP

/-
We want the notations to live in the namespace `Aeneas`, not `Aeneas.Std.WP`
TODO: use https://github.com/leanprover/lean4/pull/11355
-/
namespace Aeneas

open Std WP Result

/-!
# Hoare triple notation and elaboration
-/


syntax:lead (name := specSyntax)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term+ " => " term " ⦄" : term
syntax:lead (name := specSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄" : term
syntax:lead (name := slSpecSyntax)
  "⦃ " term " ⦄" ppLine term:lead ppLine
  "⦃" "⇓" ppSpace term+ " => " term " ⦄" : term
syntax:lead (name := slSpecSyntaxPred)
  "⦃ " term " ⦄" ppLine term:lead ppLine "⦃" "⇓" ppSpace term " ⦄" : term

open Lean PrettyPrinter

/-- Build a `Std.uncurry` chain wrapping a curried lambda over `xs`.

Given `x0`, ..., `xn` and `body`, generates the (syntactic) term `fun (x0, ..., xn) => body`.
-/
private meta partial def buildPostUncurryLamWith (uncurryName : Name)
    (xs : List Term) (body : Term) : MacroM Term := do
  let uncurryIdent := mkIdent uncurryName
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildPostUncurryLamWith uncurryName rest body
    `($uncurryIdent (fun $a => $inner))

/-- Helper to elaborate `binder => body` when binder is a tuple - this supports nested tuples. -/
private meta partial def mkPostBinderFunWith (uncurryName : Name) (depth : Nat)
    (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        -- Fresh identifier from depth + index
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkPostBinderFunWith uncurryName (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildPostUncurryLamWith uncurryName leafIdents wrappedBody
  | _ => `(fun $binder => $body)

private meta partial def mkPostSyntaxWith (curryName uncurryName : Name)
    (body : Term) (depth : Nat) (binders : List Term) : MacroM Term := do
  match binders with
  | [] => pure body
  | [x] => mkPostBinderFunWith uncurryName depth x body
  | x :: rest =>
    let rest ← mkPostSyntaxWith curryName uncurryName body (depth + 1) rest
    let inner ← mkPostBinderFunWith uncurryName depth x rest
    let curryIdent := mkIdent curryName
    `($curryIdent $inner)

/-- If `stx` is a bare identifier or a juxtaposition (application) of bare
identifiers — i.e. a binder group like `a b c` — return the identifiers in
order.  Otherwise return `none`, so anonymous constructors `⟨a, b⟩`, tuple
patterns, and other structured terms are left untouched. -/
private meta partial def binderGroupIdents? (stx : Syntax) : Option (Array Term) :=
  if stx.isIdent then some #[⟨stx⟩]
  else if stx.getKind == ``Lean.Parser.Term.app || stx.getKind == Lean.nullKind then
    stx.getArgs.foldlM (init := (#[] : Array Term)) fun acc s =>
      (binderGroupIdents? s).map (acc ++ ·)
  else none

/-- Expand a binder that shares one type ascription across several names —
`(a b c : T)` — into the list of single binders `[(a : T), (b : T), (c : T)]`,
so each name becomes its own product component (exactly as if written
separately).  Tuple/pattern binders `(a, b)`, `(⟨a, b⟩ : T)`, single binders
`(a : T)`, and bare identifiers are returned unchanged. -/
private meta def expandGroupedBinder (binder : Term) : MacroM (List Term) := do
  match binder with
  | `(($e : $t)) =>
    match binderGroupIdents? e.raw with
    | some ids =>
      if ids.size ≤ 1 then pure [binder]
      else ids.toList.mapM fun id => `(($id : $t))
    | none => pure [binder]
  | _ => pure [binder]

/-- Flatten grouped binders across the whole binder list. -/
private meta def expandBinders (xs : List Term) : MacroM (List Term) := do
  let mut out : Array Term := #[]
  for x in xs do
    out := out ++ (← expandGroupedBinder x).toArray
  pure out.toList

/-- Build the postcondition term for `⦃ xs => p ⦄`, expanding grouped binders
into one component per name first. -/
private meta def mkPostWith (curryName uncurryName : Name)
    (binders : Array Term) (body : Term) : MacroM Term := do
  mkPostSyntaxWith curryName uncurryName body 0 (← expandBinders binders.toList)

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] Q
      `(spec $m $post)
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄) => do
      let post ←
        mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] (← `(iprop($Q)))
      `(ispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $result $results:term* => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) Q
      `(spec $m $post)
  | `(⦃$P⦄ $m ⦃⇓ $result $results:term* => $Q⦄) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) (← `(iprop($Q)))
      `(ispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(spec $m (fun _ => $Q))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄) =>
      `(ispec iprop($P) $m (fun _ => iprop($Q)))

syntax:lead (name := dspecSyntax)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term+ " => " term " ⦄div" : term
syntax:lead (name := dspecSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄div" : term
syntax:lead (name := slDspecSyntax)
  "⦃ " term " ⦄" ppLine term:lead ppLine
  "⦃" "⇓" ppSpace term+ " => " term " ⦄div" : term
syntax:lead (name := slDspecSyntaxPred)
  "⦃ " term " ⦄" ppLine term:lead ppLine "⦃" "⇓" ppSpace term " ⦄div" : term

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] Q
      `(dspec $m $post)
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄div) => do
      let post ←
        mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry #[result] (← `(iprop($Q)))
      `(dispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $result $results:term* => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) Q
      `(dspec $m $post)
  | `(⦃$P⦄ $m ⦃⇓ $result $results:term* => $Q⦄div) => do
      let post ← mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry
        (#[result] ++ results) (← `(iprop($Q)))
      `(dispec iprop($P) $m $post)

macro_rules
  | `(($m) ⦃⇓ $Q:term⦄div) =>
      `(dspec $m (fun _ => $Q))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄div) =>
      `(dispec iprop($P) $m (fun _ => iprop($Q)))

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 (name := pureSpecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 (name := pureSpecPred)
  term:55 " ⦃ " term " ⦄" : term

-- for dspec
scoped syntax:54 (name := pureDspecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄div" : term
scoped syntax:54 (name := pureDspecPred)
  term:55 " ⦃ " term " ⦄div" : term

private meta def mkPurePost (binders : Array Term) (p : Term) : MacroM Term := do
  mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry binders p

/-- Macro expansion for a single element (may expand to several via a grouped binder) -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x => $p ⦄) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.Std.WP.spec $m $post)

/-- Macro expansion for multiple elements -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.Std.WP.spec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x => $p ⦄div) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.Std.WP.dspec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.Std.WP.dspec $m $post)

/-- Macro expansion for predicate with no arrow -/
scoped macro_rules (kind := pureSpecPred)
  | `($m ⦃ $p ⦄) => `(Aeneas.Std.WP.spec $m $p)

scoped macro_rules (kind := pureDspecPred)
  | `($m ⦃ $p ⦄div) => `(Aeneas.Std.WP.dspec $m $p)

/-!
# Pretty-printing

The `⦃ ⦄` macro produces postconditions using three wrappers:
- `uncurry' (fun x => ...)` — separate binders, printed as `x y z => ...`
- `uncurry (fun a b => ...)` — tuple binder, printed as `(a, b) => ...`
- Plain `fun x => ...` — scalar binder

`uncurry'` is never nested: it only appears at the outermost level to separate
top-level product components. `uncurry` can be nested inside `uncurry'` or other
`uncurry` applications (for sub-tuples like `((a, b), c)`).

**Examples of elaborated postconditions:**

| Source | Elaborated form |
|---|---|
| `⦃ r => body ⦄` | `fun r => body` |
| `⦃ (a, b) => body ⦄` | `uncurry (fun a b => body)` |
| `⦃ x y z => body ⦄` | `uncurry' (fun x => uncurry' (fun y z => body))` |
| `⦃ (a, b) c => body ⦄` | `uncurry' (uncurry (fun a b => fun c => body))` |
| `⦃ a (b, c) => body ⦄` | `uncurry' (fun a => uncurry (fun b c => body))` |
| `⦃ ((a,b), c) => body ⦄` | `uncurry (fun _p c => (uncurry (fun a b => body)) _p)` |
| `⦃ ((a,b), (c,d)) => body ⦄` | `uncurry (fun _p₀ _p₁ => (uncurry (fun a b => (uncurry (fun c d => body)) _p₁)) _p₀)` |

The delaborator reverses this: given a `spec e post` expression, it peels the
wrapper layers to recover the binder patterns and body, producing `⦃ ... => ... ⦄`.

The `uncurry`/lambda machinery (`enterLams`, `delabBinders`)
is reused from `Do.Delab` (which handles the same `uncurry` chains in `do`-notation).
The only WP-specific logic is the `uncurry'`-peeling loop on top.
-/

open Lean PrettyPrinter
open Delaborator SubExpr
open Std.Delab (enterLams delabBinders buildTupleTerm delabUncurryAsTuple)

/-- Enter exactly the binders of a single `uncurry` level (up to 2).
Unlike `enterUncurryChain` (which flattens everything), this stops after 2 binders
so the continuation lambdas are left untouched.

Example: on `fun a b => fun c => body`, collects `[a, b]` and leaves the reader
at `fun c => body`. -/
private meta partial def enterUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterUncurryOnce acc' k
      else enterUncurryOnce acc' k
  | _ => k acc

/-- Is the expression an `uncurry'` or `uncurry` wrapper? -/
private meta def isPostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | uncurry' _ _ _ _ => true
  | uncurry _ _ _ _ => true
  | _ => false

/-- Walk the postcondition expression, peeling `uncurry'`/`uncurry`/lambda layers.
Returns `(binders, bodyTerm)` where each binder is a `Term` (either a plain
name like `x` or a (potentially nested) tuple pattern like `(a, b)`).
-/
private meta partial def delabPostBinders : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | uncurry' _ _ _ _ =>
    /- `uncurry' f`: dive into `f` (arg 3) and peel one binder.
       If `f = uncurry g`, the binder is a tuple `(a, b)`.
       If `f = fun x => rest`, the binder is scalar `x`. -/
    withNaryArg 3 do
      match_expr (← getExpr).consumeMData with
      | uncurry _ _ _ _ =>
        -- Tuple binder: peel one uncurry level, then recurse for more binders
        withAppArg <| enterUncurryOnce #[] fun tupleBinders => do
          let (pats, (moreBinders, body)) ← delabBinders tupleBinders.toList delabPostBinders
          let tupleTerm ← buildTupleTerm pats
          return (#[tupleTerm] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | uncurry _ _ _ _ =>
    /- Single tuple binder `(a, b) => body` (no `uncurry'` wrapper). -/
    let tuplePos ← getPos
    withAppArg do
      let (tupleTerm, body) ← delabUncurryAsTuple delab
      let tupleTerm : Term := annotatePos tuplePos tupleTerm
      addTermInfo tuplePos tupleTerm.raw (← getExpr) (isBinder := true)
      return (#[tupleTerm], body)
  | _ => delabLamsThenRecurse
where
  /-- Peel plain lambda binders, then either recurse or terminate.

  This is used in two situations:
  - Inside `uncurry'`, when the argument is a plain lambda (not `uncurry`):
    e.g., `uncurry' (fun x => uncurry' (fun y z => body))` — after entering
    `fun x =>`, the body starts with another `uncurry'`, so we recurse.
  - At the top level, when the postcondition is a plain lambda without any
    `uncurry'`/`uncurry` wrapper: e.g., `fun r => body`.

  The key logic: if `enterLams` peels exactly one lambda and the body is a
  wrapper (`uncurry'` or `uncurry`), this lambda is a scalar binder in a
  multi-binder postcondition — recurse via `delabPostBinders` to peel more.
  Otherwise these are terminal binders (e.g., `fun y z => body` at the last
  `uncurry'` level) — delab the body directly. -/
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    if (← getExpr).consumeMData.isLambda then
      enterLams #[] fun binders => do
        if binders.size == 1 && isPostBinderWrapper (← getExpr) then
          let (pats, (moreBinders, body)) ← delabBinders binders.toList delabPostBinders
          return (pats ++ moreBinders, body)
        else
          let (pats, body) ← delabBinders binders.toList delab
          return (pats, body)
    else
      return (#[], ← delab)

private meta partial def delabSLPost : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | uncurry' _ _ _ _ =>
    withAppArg do
      match_expr (← getExpr).consumeMData with
      | Std.uncurry _ _ _ _ =>
        withAppArg <| enterUncurryOnce #[] fun tupleBinders => do
          let (patterns, (moreBinders, body)) ←
            delabBinders tupleBinders.toList delabSLPost
          return (#[← buildTupleTerm patterns] ++ moreBinders, body)
      | _ =>
        match (← getExpr).consumeMData with
        | .lam _ _ _ _ =>
          withBindingBodyUnusedName fun binder => do
            let (moreBinders, body) ← delabSLPost
            return (#[⟨binder⟩] ++ moreBinders, body)
        | _ => failure
  | Std.uncurry _ _ _ _ =>
    withAppArg do
      let (binder, body) ← delabUncurryAsTuple delab
      return (#[binder], body)
  | _ =>
    if (← getExpr).consumeMData.isLambda then
      withBindingBodyUnusedName fun binder => do
        return (#[⟨binder⟩], ← delab)
    else
      return (#[], ← delab)

private meta def delabSLISpecPost (pre monadExpr : Term) (isPartial : Bool) :
    DelabM Term := do
  let (binders, body) ← delabSLPost
  if h : binders.size > 0 then
    if isPartial then
      `(⦃$pre⦄ $monadExpr ⦃⇓ $(binders[0]) $(binders.drop 1)* => $body⦄div)
    else
      `(⦃$pre⦄ $monadExpr ⦃⇓ $(binders[0]) $(binders.drop 1)* => $body⦄)
  else if isPartial then
    `(⦃$pre⦄ $monadExpr ⦃⇓ $body⦄div)
  else
    `(⦃$pre⦄ $monadExpr ⦃⇓ $body⦄)

private meta def delabSLISpecCore (ispecName : Name) (isPartial : Bool) : Delab := do
  guard ((← getExpr).isAppOfArity ispecName 4)
  let monadExpr ← withNaryArg 2 delab
  let pre ← withNaryArg 1 delab
  withNaryArg 3 <| delabSLISpecPost pre monadExpr isPartial

@[app_delab Aeneas.Std.WP.ispec]
meta def delabSLISpec : Delab :=
  delabSLISpecCore ``Aeneas.Std.WP.ispec false

@[app_delab Aeneas.Std.WP.dispec]
meta def delabSLDispec : Delab :=
  delabSLISpecCore ``Aeneas.Std.WP.dispec true

/-- Delaborator for `WP.spec e post` → `e ⦃ binders => body ⦄`. -/
@[scoped delab app.Aeneas.Std.WP.spec]
meta def delabSpec : Delab := do
  guard $ (← getExpr).isAppOfArity' ``spec 3
  let monadExpr ← withNaryArg 1 delab
  let (binders, bodyTerm) ← withNaryArg 2 delabPostBinders
  if binders.size == 0 then
    `($monadExpr ⦃ $bodyTerm ⦄)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $bodyTerm ⦄)

/-- Delaborator for `WP.dspec e post` → `e ⦃ binders => body ⦄div`. -/
@[scoped delab app.Aeneas.Std.WP.dspec]
meta def delabDSpec : Delab := do
  guard $ (← getExpr).isAppOfArity' ``dspec 3
  let monadExpr ← withNaryArg 1 delab
  let (binders, bodyTerm) ← withNaryArg 2 delabPostBinders
  if binders.size == 0 then
    `($monadExpr ⦃ $bodyTerm ⦄div)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $bodyTerm ⦄div)

/-!
# Tests
-/

/-- error: unsolved goals
⊢ ok 0 ⦃ r => r = 0 ⦄ -/
#guard_msgs in example : ok 0 ⦃ r => r = 0 ⦄ := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : spec (ok 0) fun _ => True := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : ok 0 ⦃ _ => True ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x✝ =>
    match x✝ with
    | (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : spec (ok (0, 1)) fun (x, y) => x = 0 ∧ y = 1 := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = true ⦄ -/
#guard_msgs in example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z ⦄ := by done
/-- error: unsolved goals
⊢ let P := fun x => x = 0;
  ok 0 ⦃ P ⦄ -/
#guard_msgs in example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by done

/-! ### Mixed tuple / scalar binders -/

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Tuple followed by scalar
example : ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Scalar followed by tuple
example : ok (0, (1, 2)) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok (0, (1, 2)) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two tuples in sequence
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- A single nested tuple
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two nested tuples
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), 3, 4, 5) ⦃ a (b, c) (d, (e, f)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ -/
#guard_msgs in -- Scalar, tuple, nested tuple
example : ok (0, (1, 2), (3, (4, 5))) ⦃ a (b, c) (d, (e, f)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1, 2, 3), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄ -/
#guard_msgs in -- More nesting
example : ok ((0, (1, (2, 3))), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄
  := by done

/-! ### Pretty-printing round-trip checks -/

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in example : ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), (3, 4, 5), 6) ⦃ a (b, c) ((d, e, f), g) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ -/
#guard_msgs in example : ok (0, (1, 2), ((3, 4, 5), 6)) ⦃ a (b, c) ((d, e, f), g) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ := by done
end Aeneas

namespace Aeneas.Std.WP

open Std Result
open Aeneas.Data.Coinductive
open Lean.Order
open Aeneas.SepLogic

open Lean Elab Meta Tactic

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

namespace Intro

meta partial def isOutputLike (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isFVar || e.isLit || e.isSort then return true
  if e.isProj then return ← isOutputLike e.projExpr!
  if ← isConstructorApp e then
    return (← e.getAppArgs.allM (fun arg => isOutputLike arg))
  let f := e.getAppFn.consumeMData
  if f.isFVar then return true
  if let .const name _ := f then
    if let some info ← getProjectionFnInfo? name then
      let args := e.getAppArgs
      if h : info.numParams < args.size then
        return ← isOutputLike args[info.numParams]
  return false

meta def reduceMarker? (markers : Array Name) (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let .const name _ := e.getAppFn | return none
  unless markers.contains name do return none
  let some unfolded ← unfoldDefinition? e | return none
  let some matcher ← matchMatcherApp? unfolded | return none
  unless matcher.alts.size == 1 do return none
  for discr in matcher.discrs do
    unless ← isOutputLike discr do return none
  match ← Lean.Meta.reduceMatcher? unfolded with
  | .reduced reduced => return some reduced
  | _ => return none

meta partial def reduceMarkers (markers : Array Name) (e : Expr) (fuel : Nat := 20) :
    MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    match ← reduceMarker? markers e with
    | some e' => reduceMarkers markers e' fuel
    | none => return e

meta def slMarkers : Array Name := #[``Aeneas.Std.WP.uncurry', ``Aeneas.Std.uncurry]

meta def localHypotheses : TacticM (Std.HashSet FVarId) := do
  (← getMainGoal).withContext do
    pure <| (← getLCtx).foldl (init := ∅) fun acc decl => acc.insert decl.fvarId

private meta partial def normalizeAssertion (e : Expr) : MetaM Expr := do
  let e ← reduceMarkers slMarkers e
  if e.isAppOfArity ``sep 2 then
    let left ← normalizeAssertion e.appFn!.appArg!
    let right ← normalizeAssertion e.appArg!
    return mkApp2 (mkConst ``sep) left right
  if e.isAppOfArity ``ipure 1 then
    return mkApp (mkConst ``ipure) (← reduceMarkers slMarkers e.appArg!)
  return e

private meta def normalizePost (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let .forallE name domain _ binfo := ← whnf (← inferType e) | return e
  withLocalDecl name binfo domain fun value => do
    mkLambdaFVars #[value] (← normalizeAssertion (mkApp e value))

private meta partial def normalizeRamified (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  if e.isAppOfArity ``postWand 3 then
    return mkApp3 e.getAppFn args[0]! (← normalizePost args[1]!) (← normalizePost args[2]!)
  if e.isAppOfArity ``sep 2 then
    return mkApp2 e.getAppFn args[0]! (← normalizeRamified args[1]!)
  return e

private meta def normalizeGoal : TacticM Unit := do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  let newTarget ←
    if target.isAppOfArity ``ispec 4 || target.isAppOfArity ``dispec 4 then
      pure (mkAppN target.getAppFn (args.set! 1 (← normalizeAssertion args[1]!)))
    else if target.isAppOfArity ``Entails 2 then
      pure (mkApp2 target.getAppFn args[0]! (← normalizeRamified args[1]!))
    else pure target
  if newTarget != target then
    replaceMainGoal [← goal.change newTarget]

private meta def simplifySpatialGoal : TacticM Unit := do
  unless (← getUnsolvedGoals).isEmpty do
    discard <| commitWhen do
      evalTactic (← `(tactic| isimp only))
      let goals ← getUnsolvedGoals
      return !(goals.length > 1 || (← goals.anyM fun goal =>
        goal.withContext do return !(← isProp (← goal.getType))))

end Intro

/-- The tactic `step` runs on the goals it prepares for `ispec` and `dispec`. -/
meta def introIspec : TacticM Unit := do
  withMainContext do
    replaceMainGoal [(← (← getMainGoal).intros).2]
    withMainContext do
    Intro.normalizeGoal
    evalTactic (← `(tactic| iintro_shallow_post))
    unless (← getUnsolvedGoals).isEmpty do
      withMainContext do
      let _ ← Aeneas.Simp.simpAt true
        { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
        { addSimpThms :=
            #[``sep_emp_l_eq, ``sep_emp_r_eq,
              ``sep_ipure_true_l_eq, ``sep_ipure_true_r_eq,
              ``entails_emp_postWand_ipure_iff, ``entails_emp_ipure_iff, ``entails_refl,
              ``ispec_ipure_iff, ``dispec_ipure_iff, ``uncurry'_pair,
              ``and_imp, ``exists_imp, ``forall_unit, ``true_imp_iff] }
        (.targets #[] true)
    Intro.simplifySpatialGoal

elab (name := intro_ispec) "intro_ispec" : tactic => introIspec

/-- Reduce an `ispec` about `pure v` to the entailment `P ⊢ Q v`. -/
macro "wp_pures" : tactic => `(tactic| apply (ispec_ok _).mpr)

/-- Apply a specification, frame unused resources, and discharge the entailment with `isimpl`. -/
syntax "wp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| wp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine ispec_mono $thm ?_)
      | none => `(tactic| refine ispec_mono (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state a proved `ispec` under a weaker postcondition. -/
macro "wp_mono " thm:term : tactic =>
  `(tactic| (refine ispec_mono $thm ?_ <;> iframe))

/-- `wp_pures` for `dispec`. -/
macro "dwp_pures" : tactic => `(tactic| apply (dispec_ok _).mpr)

/-- `wp_apply` for `dispec`. -/
syntax "dwp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| dwp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine dispec_mono $thm ?_)
      | none => `(tactic| refine dispec_mono (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- `wp_mono` for `dispec`. -/
macro "dwp_mono " thm:term : tactic =>
  `(tactic| (refine dispec_mono $thm ?_ <;> iframe))

theorem ret.spec (value : α) :
    ⦃ emp ⦄ Result.ok value ⦃⇓ result => ⌜result = value⌝⦄ :=
  (ispec_ok value).mpr fun _ _ => rfl

theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : Result α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ret.spec value

/-- Keeps pure returns in the pure judgment, so `step` introduces no spatial entailment for them. -/
theorem ok_spec (value : α) :
    spec (Result.ok value) (fun result => result = value) :=
  ret.spec value

theorem pure_spec (value : α) :
    spec (Pure.pure value : Result α) (fun result => result = value) :=
  ok_spec value

end Aeneas.Std.WP

namespace Aeneas.Std

/-!
# Loops
-/

/-- General spec for loops with a termination measure.

It is meant to derive lemmas to reason about loops: in most situations, one shouldn't
have to use it directly when verifying programs.
-/
theorem loop.spec {α : Type u} {β : Type v} {γ : Type w}
  (measure : α → γ)
  [wf : WellFoundedRelation γ]
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ wf.rel (measure x') (measure x) ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  suffices ∀ x' x, measure x = x' → inv x → loop body x ⦃ post ⦄
    by apply this <;> first | rfl | assumption
  apply @wf.wf.fix γ (fun x' =>
    ∀ x, measure x = x' →
    inv x → loop body x ⦃ post ⦄)
  intro y ih x eq ix
  subst eq
  unfold loop
  apply WP.spec_bind (hBody x ix)
  intro r hr
  cases r with
  | done z => simpa using hr
  | cont x' => exact ih (measure x') hr.2 x' rfl hr.1

theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  have := loop.spec measure inv post body x hBody hInv
  apply this

end Aeneas.Std

namespace Aeneas.Std.WP

section
  variable (U32 : Type _) [HAdd U32 U32 (Result U32)]
  variable (x y : U32)

  #elab x + y ⦃ _ => True ⦄
  #elab True → x + y ⦃ _ => True ⦄
  #elab True ∧ x + y ⦃ _ => True ⦄

  -- Checking what happpens if we put post-conditions inside post-conditions
  example (f : Nat → Result (Nat × (Nat → Result Nat)))
          (_ : ∀ x, f x ⦃ (y, g) => y > 0 ∧ ∀ x, g x ⦃ z => z > y ⦄ ⦄ ∧ True)
   : True := by simp only
end

def add1 (x : Nat) := Result.ok (x + 1)
theorem  add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ :=
  by simp [add1]

/-- Example with a single output. -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro y h
    -- step as ⟨ y1, z1⟩
    apply spec_mono (add1_spec _)
    intro y' h
    --
    grind

def add2 (x : Nat) := Result.ok (x + 1, x + 2)

theorem  add2_spec (x : Nat) : add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- Example with a tuple output. -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ (y, _) => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec
    simp only [Prod.forall, uncurry_apply_pair, and_imp]
    intro y z h0 h1
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec
    simp only [Prod.forall, uncurry_apply_pair, and_imp]
    intro y1 z1 h2 h3
    grind

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- The same with separate binders: the post-condition is wrapped in the `uncurry'` marker,
which is reduced when rewriting the goal with separate output quantifiers. -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ y _ => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec'
    simp only [Prod.forall, uncurry'_pair, and_imp]
    intro y z h0 h1
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec'
    simp only [Prod.forall, uncurry'_pair, and_imp]
    intro y1 z1 h2 h3
    grind

private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  grind [massert]

/-- Example with a function outputting `()` (we need to eliminate the quantifier) -/
example :
  (do
    massert (0 < 1);
    massert (1 < 2)
    ) ⦃ _ => True ⦄
  := by
  --
  apply spec_bind
  · apply massert_spec'; decide
  simp only [forall_const]
  --
  apply spec_mono
  · apply massert_spec'; decide
  simp only [forall_const]

/- Example with a post-condition manipulating an ∃ -/
example (zero : List Nat → Result (List Nat))
    (zero_spec : ∀ s, zero s ⦃ s' =>
      ∃ (h : s'.length = s.length),
      (∀ i, (_ : i < s.length) → s'[i]'(by grind) = 0) ⦄)
    (s : List Nat) :
    (do
      let _ ← zero s
      pure ()) ⦃ _ => True ⦄ := by
  apply spec_bind
  · apply zero_spec
  rintro _ ⟨_, _⟩
  --
  simp only [pure, spec_ok]


end Aeneas.Std.WP

/- TODO: restore the mvcgen bridge (`spec_to_mvcgen`, `dspec_to_mvcgen`): the `WP` instance
must model `guardedModify` rather than send it to `False`. -/
