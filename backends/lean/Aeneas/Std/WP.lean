import Aeneas.Std.Primitives
import Aeneas.Std.Delab
import AeneasMeta.Simp
import Aeneas.Tactic.Solver.Grind.Init
import Aeneas.Std.Spec
import Aeneas.Tactic.Step.Intro
import Aeneas.Tactic.Step.DspecInduction
import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect
import Aeneas.Data.Coinductive.Spec
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic.Intro
import Aeneas.Tactic.SepLogic.Rewrite

namespace Aeneas.Std.WP

open Std Result
open Aeneas.Data.Coinductive
open Lean.Order
open Aeneas.SepLogic

def Post α := (α -> Prop)
def Pre := Prop

def Wp α := Post α → Pre

def wp_return (x:α) : Wp α := fun p => p x

section ResultImplementation

unseal Result

@[reducible]
def handler : Handler RustEffect where
  State := Heap
  handle
    | .guardedModify _ pre modify, h, C =>
        ∃ hPre : pre h, C (.up (modify h hPre).1) (modify h hPre).2
    | .fail _, _, _ => False
  handle_mono := by
    intro event h C C' hC hEvent
    cases event with
    | guardedModify => exact hEvent.imp fun _ hNext => hC _ _ hNext
    | fail => exact hEvent.elim

theorem handler_conjunctive : handler.Conjunctive := by
  intro event h Demands ⟨C₀, hC₀⟩ hAll
  cases event with
  | guardedModify EventResult pre modify =>
      exact ⟨(hAll C₀ hC₀).1, fun C hC => (hAll C hC).2⟩
  | fail error => exact (hAll C₀ hC₀).elim

private abbrev rawIwp (total:Bool) (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  (if total then TotalSpec else PartialSpec) handler (fun value h' => Q value h') m h

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
      ∀ F h, (P ∗ F) h → TotalSpec handler (fun value h' => (Q ∗+ F) value h') m h := by
  constructor
  · rintro hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, hP, hF⟩
    exact hSpec h₁ hP F _ ⟨h₁, h₂, hDisjoint, rfl, Heap.Sub.refl _, hF⟩
  · intro hSpec owned hP F _
    rintro ⟨h₁, h₂, hDisjoint, rfl, hOwned, hF⟩
    exact hSpec F _ ⟨h₁, h₂, hDisjoint, rfl, P.up_closed hP hOwned, hF⟩

theorem dispec_iff {P : IPre} {m : Result α} {Q : IPost α} :
    dispec P m Q ↔
      ∀ F h, (P ∗ F) h → PartialSpec handler (fun value h' => (Q ∗+ F) value h') m h := by
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
  PartialSpec.admissible handler_conjunctive _ h

theorem dispec_admissible {α : Type u} (P : IPre) (Q : IPost α) :
    admissible (fun m : Result α => dispec P m Q) := by
  simp only [dispec_iff]
  intro c hc hAll F h hPre
  exact rawIwp_admissible (Q ∗+ F) h c hc fun x hx => hAll x hx F h hPre

/-- The shape the `dspec_induction` tactic needs to discharge the admissibility
side-goal it generates for a separation-logic partial specification. -/
@[dspec_admissible]
theorem dispec_func_admissible {ι : Sort v} {α : Type u} (arg : ι) (P : IPre) (Q : IPost α) :
    admissible (fun f : ι → Result α => dispec P (f arg) Q) :=
  admissible_apply (fun _ m => dispec P m Q) arg (dispec_admissible P Q)

theorem dspec_admissible {α} (p : Post α) :
    admissible (fun x => dspec x p) :=
  dispec_admissible emp (fun value => ⌜p value⌝)

/-- The same as `dispec_func_admissible`, for the pure partial specification. -/
@[dspec_admissible]
theorem dspec_func_admissible {ι : Sort v} {α} (arg : ι) (p : Post α) :
    admissible (fun f : ι → Result α => dspec (f arg) p) :=
  admissible_apply (fun _ m => dspec m p) arg (dspec_admissible p)

/-- Variant of `uncurry` used to decompose tuples in post-conditions.

Similar to `uncurry` but delaborated differently:
`uncurry'` is delaborated as `x y => ...` (separate binders), while
`uncurry` is delaborated as `(x, y) => ...` (tuple binder).
We use this in the Hoare triple notation `⦃ ⦄`.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to
`spec (f 0) (uncurry' fun x => uncurry' fun y z => ...)`.
-/
def uncurry' {α β γ : Type _} (p : α → β → γ) : α × β → γ :=
  fun (x, y) => p x y

@[simp] theorem uncurry'_pair x y (p : α → β → γ) : uncurry' p (x, y) = p x y := by simp [uncurry']
@[defeq] theorem uncurry'_eq x (p : α → β → γ) : uncurry' p x = p x.fst x.snd := by simp [uncurry']

/-! ### `ispec` theorems -/
@[simp, grind =, agrind =]
theorem ispec_ok (x : α) : ispec P (ok x) Q ↔ P ⊢ Q x := by
  constructor
  · intro hTriple h hP
    rw [ispec_iff] at hTriple
    have hPost := (hTriple emp h ((sep_emp_r P).mpr h hP)).ret_post
    exact (sep_emp_r (Q x)).mp h hPost
  · intro hPost
    rw [ispec_iff]
    intro F h hPre
    exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- A guarded modification is correct exactly when it is *local* at every heap `P`
describes: for every disjoint frame, the guard holds and the output splits into an
owned result and the unchanged frame.  Quantifying over frames here is what
validates the frame rule — the frame an `ispec` carries is already one of them. -/
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
  refine TotalSpec.vis (H := handler)
    (event := RustEffect.Input.guardedModify _ pre modify) ⟨hPre, ?_⟩
  rw [hModify]
  exact .ret ⟨h', framed, hDisjoint', rfl, hPost, hF⟩

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

/-- The frame rule, framing on the left. -/
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

/-- Mono rule used by `step` -/
theorem ispec_mono {α : Type u} {P Pm : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : ispec Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    ispec P m Q := by
  have hFramed := ispec_frame hStep (Qm -∗+ Q)
  rw [ispec_iff] at hFramed ⊢
  intro F h hPre
  have hSpec := hFramed F h (sep_mono hRamified (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (postWand_cancel Qm Q value) (entails_refl F)

/-- Rule of consequence: strengthen the precondition and weaken the postcondition.
The special case of `ispec_mono` in which no resource is transferred. -/
theorem ispec_conseq {P' P : IPre} {m : Result α} {Q' Q : IPost α}
    (hTriple : ispec P' m Q') (hP : P ⊢ P') (hQ : Q' ⊢+ Q) :
    ispec P m Q := by
  rw [ispec_iff] at hTriple ⊢
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (hQ value) (entails_refl F)

/-- Bind rule used by `step`. It is stated on `Aeneas.Std.bind` rather than on `>>=` -/
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

/-- Copy a pure fact of the precondition into the local context *without*
consuming it: the precondition is unchanged, so the fact stays available to the
framing of the later steps.  This is `ispec_ipure` used in both directions. -/
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

/-! ### `dispec` theorems -/
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
    have hPost := (hTriple emp h ((sep_emp_r P).mpr h hP)).ret_post
    exact (sep_emp_r (Q x)).mp h hPost
  · intro hPost
    rw [dispec_iff]
    intro F h hPre
    exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- Divergence satisfies every partial ispec: nothing is claimed of a run that
does not stop, not even that it owns anything. -/
theorem dispec_div {P : IPre} {Q : IPost α} :
    dispec P (div : Result α) Q := by
  rw [dispec_iff]
  intro _ _ _
  exact PartialSpec.div

theorem dispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) (H : IProp) : dispec (P ∗ H) m (Q ∗+ H) := by
  rw [dispec_iff] at hTriple ⊢
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

/-- Mono rule used by `step` on a partial goal.  See `ispec_mono`. -/
theorem dispec_mono {α : Type u} {P Pm : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : dispec Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dispec P m Q := by
  have hFramed := dispec_frame hStep (Qm -∗+ Q)
  rw [dispec_iff] at hFramed ⊢
  intro F h hPre
  have hSpec := hFramed F h (sep_mono hRamified (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (postWand_cancel Qm Q value) (entails_refl F)

/-- Bind rule used by `step` on a partial goal.  See `ispec_bind`. -/
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

/-- Partial counterpart of `ispec_ipure`. -/
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

/-- Partial counterpart of `ispec_ipure_iff`. -/
theorem dispec_ipure_iff {P : Prop} {m : Result α} {Q : IPost α} :
    dispec ⌜P⌝ m Q ↔ (P → dispec emp m Q) := by
  rw [← sep_emp_r_eq ⌜P⌝]
  exact dispec_ipure

/-- Partial counterpart of `ispec_ipure_keep`. -/
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

/-! ## Reasoning about loops

The rules a partial specification is for: an invariant that the body re-establishes
proves the loop, with no measure and no termination argument. A recursion in
`Result` is proved with `dispec_admissible` and the `fixpoint_induct` principle
`partial_fixpoint` attaches to it, and anything else by
`PartialSpec.coinduction` itself. -/


/-- The same for a family of ispecs about a recursive *function*, which is the
shape `fixpoint_induct` expects. -/
theorem dispec_admissible_pi {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible
      (fun f : ι → Result α => ∀ x, dispec (P x) (f x) (Q x)) :=
  Lean.Order.admissible_pi_apply (fun x m => dispec (P x) m (Q x))
    fun x => dispec_admissible (P x) (Q x)

/-- And the same for a specification that quantifies over parameters of its own
— a ghost value, an old contents — which is the shape `fixpoint_induct` takes
when the argument of the recursion does not change. -/
theorem dispec_admissible_forall {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible (fun m : Result α => ∀ x, dispec (P x) m (Q x)) :=
  Lean.Order.admissible_pi _ fun x => dispec_admissible (P x) (Q x)

/- `sep_ipure_true_r_eq`, `entails_emp_ipure_iff` and `entails_refl` are registered
with `@[step_simps]` in `Aeneas.Tactic.Step.Step`: that attribute is declared in
`Aeneas.Tactic.Step.Init`, which imports this file. -/
attribute [simp] entails_emp_ipure_iff

/-! ### `spec` theorems

`spec` and `dspec` are named judgments with ordinary `α → Prop` postconditions,
defined as the SL judgments at `emp` with a pure postcondition, so each rule
below reads the corresponding `ispec`/`dispec` one.

Each judgment has its own `step` registration. Pure specifications lift to SL
specifications for framing; SL specifications lift back only when their
precondition is `emp`. Total specifications also lift to partial ones, never
conversely. -/
@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x :=
  (ispec_ok x).trans (entails_emp_ipure_iff (p x))

/-- Failure has no total pure specification. -/
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

/-- Bind rule used by `step`. It is stated on `Aeneas.Std.bind` rather than on `>>=`, which is
what a translated program binds with. -/
theorem spec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    spec m Pₘ →
    (∀ x, Pₘ x → spec (k x) Pₖ) →
    spec (Std.bind m k) Pₖ :=
  fun hm hk =>
    ispec_bind hm (sep_emp_r emp).mpr fun value =>
      ispec_mono (ispec_ipure_iff.mpr (hk value)) (entails_trans (sep_emp_r _).mp
        (entails_sep_postWand _ (fun _ => entails_refl _)))

theorem exists_imp_spec {m:Result α} {P:Post α} :
    (∃ y, m = ok y ∧ P y) → spec m P := by
  rintro ⟨y, rfl, hP⟩
  exact (spec_ok y).mpr hP

/-- A total specification no longer proves that a computation *returns* -- an
event that only extends the heap satisfies `spec` too, see the section note
above -- so that has to be supplied separately. -/
theorem spec_imp_exists {m : Result α} {P : Post α} (h : spec m P)
    (hok : ∃ y, m = ok y) : ∃ y, m = ok y ∧ P y := by
  obtain ⟨y, rfl⟩ := hok
  exact ⟨y, rfl, (spec_ok y).mp h⟩

/-- A total specification pins down the value a computation returns, even
without knowing that it does. -/
theorem spec_imp_forall {m : Result α} {P : Post α} :
    spec m P → (∀ y, m = ok y → P y) := by
  grind only [= spec_ok]

/-- The machine of `Result` is feasible -- no heap event is a miracle -- and it
answers each event in exactly one way, so two total specifications of the same
computation are witnessed by the *same* run. -/
private theorem totalSpec_exists_and {Q₁ Q₂ : HPost handler α} {m : Result α} {h : Heap}
    (h₁ : TotalSpec handler Q₁ m h) (h₂ : TotalSpec handler Q₂ m h) :
    ∃ value heap, Q₁ value heap ∧ Q₂ value heap := by
  refine TotalSpec.induction
    (P := fun m h => TotalSpec handler Q₂ m h → ∃ value heap, Q₁ value heap ∧ Q₂ value heap)
    (fun value s hPost hOther => ⟨value, s, hPost, hOther.ret_post⟩)
    (fun event k s hHandle hOther => ?_) h₁ h₂
  have hOther' : handler.handle event s fun answer s' => TotalSpec handler Q₂ (k answer) s' := by
    simpa only [SpecF.vis] using hOther.step
  cases event with
  | guardedModify _ pre modify => exact hHandle.2 hOther'.2
  | fail _ => exact hHandle.elim

/-- A computation meeting two total specifications evaluates to one value meeting
both.  This is the semantic replacement for `spec_imp_exists`: that lemma could
*name* the returned value only because the former judgment ruled out every event,
and `m = ok y` is a claim about the shape of `m`, not about what it evaluates to. -/
theorem spec_exists_and {m : Result α} {p q : Post α} (h₁ : spec m p) (h₂ : spec m q) :
    ∃ value, p value ∧ q value := by
  have hEmp : ((emp : IPre) ∗ emp) (∅ : Heap) := (sep_emp_r emp).mpr ∅ trivial
  obtain ⟨value, heap, hp, hq⟩ :=
    totalSpec_exists_and (ispec_iff.mp h₁ emp ∅ hEmp) (ispec_iff.mp h₂ emp ∅ hEmp)
  exact ⟨value,
    (pure_holds heap).mp ((sep_emp_r _).mp heap hp),
    (pure_holds heap).mp ((sep_emp_r _).mp heap hq)⟩

/-- A total specification is inhabited: the computation evaluates to some value
satisfying it, even when nothing says it is syntactically an `ok`. -/
theorem spec_exists {m : Result α} {p : Post α} (h : spec m p) : ∃ value, p value :=
  (spec_exists_and h h).imp fun _ hp => hp.1


/-! ### `dspec` theorems -/
@[simp, grind =, agrind =]
theorem dspec_ok (x : α) : dspec (ok x) p ↔ p x :=
  (dispec_ok x).trans (entails_emp_ipure_iff (p x))

/-- Failure has no partial pure specification: divergence is permitted, not
stuckness. -/
@[simp, grind =, agrind =]
theorem dspec_fail (e : Error) : dspec (fail e) p ↔ False :=
  iff_false_intro fun hSpec => (dispec_apply hSpec (h := ∅) trivial).vis_view

@[simp, grind =, agrind =]
theorem dspec_div : dspec (div : Result α) p ↔ True :=
  iff_true_intro dispec_div

theorem dspec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : dspec m P₀):
    (∀ x, P₀ x → P₁ x) → dspec m P₁ :=
  fun hMonPost => dispec_mono h (entails_sep_postWand _ (fun value _ => hMonPost value))

theorem dspec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    dspec m Pₘ →
    (∀ x, Pₘ x → dspec (k x) Pₖ) →
    dspec (Std.bind m k) Pₖ :=
  fun hm hk =>
    dispec_bind hm (sep_emp_r emp).mpr fun value =>
      dispec_mono (dispec_ipure_iff.mpr (hk value)) (entails_trans (sep_emp_r _).mp
        (entails_sep_postWand _ (fun _ => entails_refl _)))

theorem dspec_imp_forall {m:Result α} {P:Post α} :
    dspec m P → (∀ y, m = ok y → P y) := by
  grind only [= dspec_ok]

/- `dispec` unfolds to a nested `∀`, and the `admissible` search behind
`dspec_func_admissible` otherwise walks straight past the judgment into its
denotation.  The old `spec` was an opaque `TotalSpec` application and did not
have this problem. -/
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


/- The `⇓` is inside `atomic` so that the parser backtracks when it is absent:
`(m) ⦃ value => p ⦄`, the pure-computation notation of `Aeneas.Std.WP`,
starts with exactly the same tokens and must stay parseable. -/
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

/-- Build a marker chain for the leaves of a possibly nested tuple pattern. -/
private partial def buildPostUncurryLamWith (uncurryName : Name)
    (xs : List Term) (body : Term) : MacroM Term := do
  let uncurryIdent := mkIdent uncurryName
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildPostUncurryLamWith uncurryName rest body
    `($uncurryIdent (fun $a => $inner))

/-- Elaborate one possibly nested tuple binder without generating a matcher
function, so `step` and the delaborator can recover its structure. -/
private partial def mkPostBinderFunWith (uncurryName : Name) (depth : Nat)
    (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkPostBinderFunWith uncurryName (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildPostUncurryLamWith uncurryName leafIdents wrappedBody
  | _ => `(fun $binder => $body)

/-- Preserve boundaries between separate binders with `curryName`, while using
`uncurryName` inside each explicit tuple binder. -/
private partial def mkPostSyntaxWith (curryName uncurryName : Name)
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
private partial def binderGroupIdents? (stx : Syntax) : Option (Array Term) :=
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
private def expandGroupedBinder (binder : Term) : MacroM (List Term) := do
  match binder with
  | `(($e : $t)) =>
    match binderGroupIdents? e.raw with
    | some ids =>
      if ids.size ≤ 1 then pure [binder]
      else ids.toList.mapM fun id => `(($id : $t))
    | none => pure [binder]
  | _ => pure [binder]

/-- Flatten grouped binders across the whole binder list. -/
private def expandBinders (xs : List Term) : MacroM (List Term) := do
  let mut out : Array Term := #[]
  for x in xs do
    out := out ++ (← expandGroupedBinder x).toArray
  pure out.toList

/-- Build a marked postcondition from the parsed binder array, expanding grouped
binders into one component per name first. -/
private def mkPostWith (curryName uncurryName : Name)
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

/-!
# Pure specification notation

`⦃ ⦄` writes a pure specification the way a Rust programmer reads a return
value: `f x ⦃ y => y > 0 ⦄` is the `ispec` that owns nothing,
`ispec emp (f x) (fun y => ⌜y > 0⌝)`, and several binders destructure a
returned tuple, so `f x ⦃ y z => ... ⦄` names the two components of a pair
without a pattern match of its own.

The notation expands to the named judgments `spec` and `dspec`, whose
definitions are the separation-logic ispecs at `emp` with a pure postcondition:

```
m ⦃ x => p ⦄      is      ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄
m ⦃ x => p ⦄div   is      ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄div
```

The two forms remain definitionally equal. Their separate registrations and
liftings let `step` use pure rules for pure calls and spatial rules for heap calls.

The syntax is `scoped` in `Aeneas.Std.WP`: a file enables it by opening that
namespace.
-/

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can write expressions like `x + y ⦃ z => ... ⦄` without having to put
parentheses around `x + y`. -/
scoped syntax:54 (name := pureSpecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 (name := pureSpecPred)
  term:55 " ⦃ " term " ⦄" : term

-- for partial correctness
scoped syntax:54 (name := pureDspecBinders)
  term:55 " ⦃ " term+ " => " term " ⦄div" : term
scoped syntax:54 (name := pureDspecPred)
  term:55 " ⦃ " term " ⦄div" : term

/-- The predicate a pure postcondition denotes. Transparent marker functions
record whether each product came from separate binders or an explicit tuple
pattern, allowing the delaborator to reproduce the original surface syntax. -/
private def mkPurePost (binders : Array Term) (p : Term) : MacroM Term := do
  mkPostWith ``Aeneas.Std.WP.uncurry' ``Aeneas.Std.uncurry binders p

/-- Macro expansion for a single binder. -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x => $p ⦄) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.Std.WP.spec $m $post)

/-- Macro expansion for several binders. -/
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

/-- Macro expansion for a postcondition given as a predicate. -/
scoped macro_rules (kind := pureSpecPred)
  | `($m ⦃ $p ⦄) => `(Aeneas.Std.WP.spec $m $p)

scoped macro_rules (kind := pureDspecPred)
  | `($m ⦃ $p ⦄div) => `(Aeneas.Std.WP.dspec $m $p)

/-!
# Pretty-printing

The named pure judgments print their predicate postconditions directly.
SL ispecs always use the separating notation, including ispecs at `emp`
with pure postconditions.
-/

open Lean PrettyPrinter
open Delaborator SubExpr
open Std.Delab (enterLams delabBinders buildTupleTerm delabUncurryAsTuple)

/-- Enter exactly the binders of a single `uncurry` level (up to 2).
Unlike `enterUncurryChain` (which flattens everything), this stops after 2 binders
so the continuation lambdas are left untouched.

Example: on `fun a b => fun c => body`, collects `[a, b]` and leaves the reader
at `fun c => body`. -/
private partial def enterUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterUncurryOnce acc' k
      else
        enterUncurryOnce acc' k
  | _ => k acc

private def isPostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | uncurry' _ _ _ _ => true
  | uncurry _ _ _ _ => true
  | _ => false

/-- Recover separate binders, explicit tuple binders, and the final pure body
from the transparent marker chain produced by `mkPurePost`. -/
private partial def delabPurePost : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | uncurry' _ _ _ _ =>
    withAppArg do
      match_expr (← getExpr).consumeMData with
      | Std.uncurry _ _ _ _ =>
        withAppArg <| enterUncurryOnce #[] fun tupleBinders => do
          let (patterns, (moreBinders, body)) ←
            delabBinders tupleBinders.toList delabPurePost
          return (#[← buildTupleTerm patterns] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | Std.uncurry _ _ _ _ =>
    withAppArg do
      let (tupleBinder, body) ← delabUncurryAsTuple delab
      return (#[tupleBinder], body)
  | _ => delabLamsThenRecurse
where
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    if (← getExpr).consumeMData.isLambda then
      enterLams #[] fun binders => do
        if binders.size == 1 && isPostBinderWrapper (← getExpr) then
          let (patterns, (moreBinders, body)) ←
            delabBinders binders.toList delabPurePost
          return (patterns ++ moreBinders, body)
        else
          delabBinders binders.toList delab
    else
      return (#[], ← delab)

/-- Recover separate binders, explicit tuple binders, and the final spatial
postcondition from the marker chain produced by `mkPostSyntaxWith`. -/
private partial def delabSLPost : DelabM (Array Term × Term) := do
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

/-- Print an arbitrary separation-logic postcondition using binder syntax when
it is a lambda and predicate syntax otherwise. -/
private def delabSLISpecPost (pre monadExpr : Term) (isPartial : Bool) :
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

/-- Print an arbitrary ispec using the general separation-logic notation. -/
private def delabSLISpecCore (ispecName : Name) (isPartial : Bool) : Delab := do
  guard ((← getExpr).isAppOfArity ispecName 4)
  let monadExpr ← withNaryArg 2 delab
  let pre ← withNaryArg 1 delab
  withNaryArg 3 <| delabSLISpecPost pre monadExpr isPartial

/-- Delaborator for total separation-logic ispecs. -/
@[app_delab Aeneas.Std.WP.ispec]
def delabSLISpec : Delab :=
  delabSLISpecCore ``Aeneas.Std.WP.ispec false

/-- Delaborator for partial separation-logic ispecs. -/
@[app_delab Aeneas.Std.WP.dispec]
def delabSLDispec : Delab :=
  delabSLISpecCore ``Aeneas.Std.WP.dispec true

private def delabPureSpecCore (specName : Name) (isPartial : Bool) : Delab := do
  guard ((← getExpr).isAppOfArity specName 3)
  let monadExpr ← withNaryArg 1 delab
  let (binders, body) ← withNaryArg 2 delabPurePost
  if h : binders.size > 0 then
    if isPartial then
      `($monadExpr ⦃ $(binders[0]) $(binders.drop 1)* => $body ⦄div)
    else
      `($monadExpr ⦃ $(binders[0]) $(binders.drop 1)* => $body ⦄)
  else if isPartial then
    `($monadExpr ⦃ $body ⦄div)
  else
    `($monadExpr ⦃ $body ⦄)

@[scoped delab app.Aeneas.Std.WP.spec]
def delabPureSpec : Delab :=
  delabPureSpecCore ``Aeneas.Std.WP.spec false

@[scoped delab app.Aeneas.Std.WP.dspec]
def delabPureDspec : Delab :=
  delabPureSpecCore ``Aeneas.Std.WP.dspec true

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

/-! ### The introduction tactic of the separation-logic judgments

`step` leaves two shapes behind, and `intro_ispec` turns both of them into the
`∀ outputs, facts → …` form the tactic introduces the outputs from:

* a continuation `∀ value, ispec (Qm value ∗ F) (next value) Q`, whose pure
  facts and existentials become hypotheses;
* a ramified entailment `P ⊢ Pm ∗ (Qm -∗+ Q)`, which collapses to a pointwise
  implication when both postconditions are pure.

The facts of a pure judgment are the binders of the premise, and `Step.Intro`
handles them; here they have to be extracted from an assertion first, which is
what this section adds. The postcondition of a callee reaches the goal wrapped
in the markers of the `⦃⇓ x y => … ⦄` notation, and `Step.Intro.reduceMarkers`
reduces those *definitionally*, which is why no rewriting lemma about them is
needed. -/

namespace Intro

open Aeneas.Step.Intro (reduceMarkers)

/-- Expose the structure of an assertion by reducing the markers it holds: those
of the separating conjunctions it is built from, and those of the propositions
they hold. -/
private partial def normalizeAssertion (e : Expr) : MetaM Expr := do
  let e ← reduceMarkers e
  if e.isAppOfArity ``sep 2 then
    let left ← normalizeAssertion e.appFn!.appArg!
    let right ← normalizeAssertion e.appArg!
    return mkApp2 (mkConst ``sep) left right
  if e.isAppOfArity ``ipure 1 then
    return mkApp (mkConst ``ipure) (← reduceMarkers e.appArg!)
  return e

/-- Expose the assertion a postcondition maps its result to.  The notation
builds a postcondition as a marker applied to a function, so eta-expanding it is
what lets that marker reduce. -/
private def normalizePost (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let .forallE name domain _ binfo := ← whnf (← inferType e) | return e
  withLocalDecl name binfo domain fun value => do
    mkLambdaFVars #[value] (← normalizeAssertion (mkApp e value))

/-- Expose the postconditions of the ramified wand of an entailment's
destination, which `step` builds as `Pm ∗ (Qm -∗+ Q)`. -/
private partial def normalizeRamified (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  if e.isAppOfArity ``postWand 3 then
    return mkApp3 e.getAppFn args[0]! (← normalizePost args[1]!) (← normalizePost args[2]!)
  if e.isAppOfArity ``sep 2 then
    return mkApp2 e.getAppFn args[0]! (← normalizeRamified args[1]!)
  return e

/-- Normalize the goal `step` prepared: the precondition of a continuation, and
the two postconditions a ramified entailment relates.  The postcondition of the
triple being proved is deliberately left alone — it is the goal the user
stated. -/
private def normalizeGoal : TacticM Unit := do
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

end Intro

/-- The tactic `step` runs on the goals it prepares for `ispec` and `dispec`.
A no-op on a goal which is neither.

See the section above for the shapes it normalizes, and for why it needs no
lemma about the markers of the postcondition notation. -/
elab (name := intro_ispec) "intro_ispec" : tactic => withMainContext do
  let before ← Aeneas.Step.Intro.localHypotheses
  replaceMainGoal [(← (← getMainGoal).intros).2]
  withMainContext do
  Intro.normalizeGoal
  evalTactic (← `(tactic| iintro_shallow_post))
  unless (← getUnsolvedGoals).isEmpty do
    withMainContext do
    Aeneas.Step.Intro.splitNewHypotheses before
    withMainContext do
    /- Collapse what is left of a ramified entailment between pure
       postconditions, and of a triple with a pure precondition.  The pure facts
       of a collapsed entailment are still in the goal, hence `and_imp` and
       `exists_imp`: the ones extracted into the context were split above. -/
    let _ ← Aeneas.Simp.simpAt true
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      { addSimpThms :=
          #[``sep_emp_l_eq, ``sep_emp_r_eq,
            ``sep_ipure_true_l_eq, ``sep_ipure_true_r_eq,
            ``entails_emp_postWand_ipure_iff, ``entails_emp_ipure_iff, ``entails_refl,
            ``ispec_ipure_iff, ``dispec_ipure_iff,
            ``and_imp, ``exists_imp, ``forall_unit, ``true_imp_iff] }
      (.targets #[] true)

/-- Normalize after output destructuring. -/
elab (name := intro_step_post) "intro_step_post" : tactic => do
  let _ ← Aeneas.Simp.simpAt true
    { maxDischargeDepth := 1, failIfUnchanged := false, iota := false }
    { addSimpThms :=
        #[``Aeneas.Std.uncurry_apply_pair,
          ``Aeneas.Std.uncurry_eq_prop, ``Aeneas.Std.uncurry_eq_prop_arrow,
          ``Aeneas.Std.WP.uncurry'_pair, ``Aeneas.Std.WP.uncurry'_eq,
          ``and_imp, ``exists_imp, ``Aeneas.Step.Intro.forall_unit, ``true_imp_iff] }
    (.targets #[] true)

#register_spec_info {
    spec_name := ``ispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``ispec_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``ispec_bind
    mk_spec_bind_skip_args := 7
    intro_tactic := some ``intro_ispec
    post_intro_tactic := some ``intro_step_post
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[
      { from_statement := ``spec
        conversion_thm := ``spec_ispec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``dispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``dispec_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``dispec_bind
    mk_spec_bind_skip_args := 7
    intro_tactic := some ``intro_ispec
    post_intro_tactic := some ``intro_step_post
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[
      { from_statement := ``ispec
        conversion_thm := ``ispec_dispec
        conversion_thm_inferred_args := 4 },
      { from_statement := ``spec
        conversion_thm := ``spec_dispec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``dspec
        conversion_thm := ``dspec_dispec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``spec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``spec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``spec_bind
    mk_spec_bind_skip_args := 4
    intro_tactic := some ``Aeneas.Step.Intro.introSplit
    post_intro_tactic := some ``intro_step_post
    to_mvcgen := none
    liftings := #[
      { from_statement := ``ispec
        conversion_thm := ``ispec_spec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``dspec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``dspec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``dspec_bind
    mk_spec_bind_skip_args := 4
    intro_tactic := some ``Aeneas.Step.Intro.introSplit
    post_intro_tactic := some ``intro_step_post
    to_mvcgen := none
    liftings := #[
      { from_statement := ``spec
        conversion_thm := ``spec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``ispec
        conversion_thm := ``ispec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``dispec
        conversion_thm := ``dispec_dspec
        conversion_thm_inferred_args := 3 }
    ]
  }

/-! ## Weakest-precondition tactics -/

/-- Reduce an `ispec` about a terminal `pure v` to the entailment `P ⊢ Q v`. -/
macro "wp_pures" : tactic => `(tactic| apply (ispec_ok _).mpr)

/-- Apply a specification to the goal, frame the resources it does not need,
and discharge the resulting entailment with `isimpl`. -/
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

/-- Re-state an already-proved ispec under a weaker postcondition. -/
macro "wp_mono " thm:term : tactic =>
  `(tactic| (refine ispec_mono $thm ?_ <;> iframe))

/-- Reduce a partial ispec about a terminal `pure v` to the entailment
`P ⊢ Q v`. -/
macro "dwp_pures" : tactic => `(tactic| apply (dispec_ok _).mpr)

/-- Apply a partial specification to the goal, frame the resources it does not
need, and discharge the resulting entailment with `isimpl`. -/
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

/-- Re-state an already-proved partial ispec under a weaker postcondition. -/
macro "dwp_mono " thm:term : tactic =>
  `(tactic| (refine dispec_mono $thm ?_ <;> iframe))

/- The four rules below are registered with `@[step]` in `Aeneas.Tactic.Step.Step`:
that attribute is declared in `Aeneas.Tactic.Step.Init`, which imports this file. -/

theorem ret.spec (value : α) :
    ⦃ emp ⦄ Result.ok value ⦃⇓ result => ⌜result = value⌝⦄ :=
  (ispec_ok value).mpr fun _ _ => rfl

theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : Result α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ret.spec value

/-- Pure returns stay in the pure judgment, allowing `step` to infer ordinary
predicate postconditions without introducing spatial entailments. -/
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
  variable (U32 : Type) [HAdd U32 U32 (Result U32)]
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

/-- Example with a tuple output. -/
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

/-- The same, with the tactic `step` registers to introduce the outputs and the facts of
their premises. -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro_split
    -- step as ⟨ y1, z1⟩
    apply spec_mono (add1_spec _)
    intro_split
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
    rintro ⟨y, z⟩ h
    simp at h
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec
    rintro ⟨y1, z1⟩ h
    simp at h
    grind

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- The same with separate binders: `intro_split` reduces the `uncurry'` marker of the
post-condition, and splits the conjunction it holds into two facts. `step` additionally
destructures the output itself, which is why it can name the two components. -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ y _ => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec'
    intro_split
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec'
    intro_split
    /- The marker of the *enclosing* post-condition is left alone: `step` reduces it by
       destructuring the output. -/
    simp only [uncurry'_eq]
    grind

private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  grind [massert]

/-- Example with a function outputting `()`: the quantifier is over `Unit`, and the fact it
carries says nothing, so `intro_split` drops it. `step` additionally instantiates the `Unit`
binder rather than introducing a useless output. -/
example :
  (do
    massert (0 < 1);
    massert (1 < 2)
    ) ⦃ _ => True ⦄
  := by
  --
  apply spec_bind
  · apply massert_spec'; omega
  intro_split
  --
  apply spec_mono
  · apply massert_spec'; omega
  intro_split
  trivial

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
  /- `intro_split` peels the existential of the post-condition, and splits the conjunction
     under it. -/
  intro_split
  --
  simp only [pure, spec_ok]


end Aeneas.Std.WP

/- TODO: mvcgen support is dropped for now.

`import Std.Do` went with it; it is needed again to restore the bridge.

`WP.lean` carried a bridge to `Std.Do`: a `WP`/`WPMonad` instance for `Result`
plus `spec_to_mvcgen`/`dspec_to_mvcgen`, which let `@[step]` theorems generate
companion `@[spec]` lemmas (see `info.to_mvcgen` in `Aeneas.Tactic.Step.Init`).

Both lifts are *false* under this handler.  The instance sent every effect other
than `fail` to `False`, so a `Triple` rules out `guardedModify`; `spec`/`dspec`
do not, because an event that only extends the heap preserves every frame it is
asked to.  The `vis` case of the old proofs is exactly the gap.

Restoring the bridge means teaching the `WP` instance to *model* `guardedModify`
rather than discard it.  Until then every `#register_spec_info` above keeps
`to_mvcgen := none`, and `Aeneas/Tactic/Step/Tests/MvcgenSpec.lean` -- the only
file in the repo that calls `mvcgen` -- has to be dropped or reworked when this
file replaces `WP.lean`.

Its `Triple` notation also collides with the separation-logic `⦃P⦄ m ⦃⇓ x => Q⦄`
declared here, as does `Std.Do`'s `⌜⌝` with `SepLogic.ipure`; any future mvcgen
code in this file must apply `Triple`/`SPred.pure`/`PostCond.noThrow` directly. -/
