import Aeneas.Std.Delab
import Aeneas.Std.WP
import Aeneas.SLPoC.StateMachine
import Aeneas.Std.Primitives
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

namespace Aeneas.SepLogic

open Aeneas.Data
open Aeneas.Data.Coinductive
open Aeneas.Std (Error Heap Result RustEffect)
open Aeneas.Std.WP (Post)

universe u v

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

abbrev iwp (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  TotalSpec handler (fun value h' => Q value h') m h

abbrev diwp (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  PartialSpec handler (fun value h' => Q value h') m h

/-- Total-correctness separation-logic specification -/
def ispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  ∀ F h, (P ∗ F) h → iwp m (Q ∗+ F) h

/-- Partial-correctness separation-logic specification -/
def dispec (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  ∀ F h, (P ∗ F) h → diwp m (Q ∗+ F) h

/-- Total-correctness pure specification -/
def spec (m : Result α) (Q : Post α) : Prop :=
  ispec emp m (fun value => ⌜Q value⌝)

/-- Partial-correctness pure specification -/
def dspec (m : Result α) (Q : Post α) : Prop :=
  dispec emp m (fun value => ⌜Q value⌝)

theorem ispec_dispec {α : Type u} {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) : dispec P m Q :=
  fun F h hPre => (hTriple F h hPre).toPartial

theorem spec_ispec (m : Result α) (Q : Post α) : spec m Q → ispec emp m (fun value => ⌜Q value⌝) := id

theorem dspec_dispec (m : Result α) (Q : Post α) : dspec m Q → dispec emp m (fun value => ⌜Q value⌝) := id

theorem spec_dspec (m : Result α) (Q : Post α) : spec m Q → dspec m Q := ispec_dispec

theorem spec_dispec (m : Result α) (Q : Post α) : spec m Q → dispec emp m (fun value => ⌜Q value⌝) :=
  ispec_dispec

theorem ispec_spec (m : Result α) (Q : Post α) :
    ispec emp m (fun value => ⌜Q value⌝) → spec m Q := id

theorem ispec_dspec (m : Result α) (Q : Post α) :
    ispec emp m (fun value => ⌜Q value⌝) → dspec m Q := ispec_dispec

theorem dispec_dspec (m : Result α) (Q : Post α) :
    dispec emp m (fun value => ⌜Q value⌝) → dspec m Q := id

private theorem diwp_admissible (Q : IPost α) (h : Heap) :
    Lean.Order.admissible (fun m : Result α => diwp m Q h) :=
  PartialSpec.admissible handler_conjunctive _ h

theorem dispec_admissible {α : Type u} (P : IPre) (Q : IPost α) :
    Lean.Order.admissible (fun m : Result α => dispec P m Q) := by
  intro c hc hAll F h hPre
  exact diwp_admissible (Q ∗+ F) h c hc fun x hx => hAll x hx F h hPre

theorem dspec_admissible {α : Type u} (Q : α → Prop) :
    Lean.Order.admissible (fun m : Result α => dspec m Q) :=
  dispec_admissible emp (fun value => ⌜Q value⌝)

/-- Split separate postcondition binders before `step` introduces the
result and its postcondition hypotheses. -/
theorem forall_ispec_uncurry' {α β γ : Type _}
    (P : α → β → IProp) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, ispec (Std.WP.uncurry' P value ∗ F) (next value) Q) ↔
      ∀ first second, ispec (P first second ∗ F) (next (first, second)) Q := by
  constructor
  · intro h first second
    exact h (first, second)
  · intro h ⟨first, second⟩
    exact h first second

/-- Partial-ispec counterpart of `forall_ispec_uncurry'`. -/
theorem forall_dispec_uncurry' {α β γ : Type _}
    (P : α → β → IProp) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, dispec (Std.WP.uncurry' P value ∗ F) (next value) Q) ↔
      ∀ first second, dispec (P first second ∗ F) (next (first, second)) Q := by
  constructor
  · intro h first second
    exact h (first, second)
  · intro h ⟨first, second⟩
    exact h first second

/-- Split an uncurried postcondition before `step` introduces the
result and its postcondition hypotheses. -/
theorem forall_ispec_uncurry {α β γ : Type _}
    (P : α → β → IProp) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, ispec (Std.uncurry P value ∗ F) (next value) Q) ↔
      ∀ first second, ispec (P first second ∗ F) (next (first, second)) Q := by
  constructor
  · intro h first second
    exact h (first, second)
  · intro h ⟨first, second⟩
    exact h first second

/-- Partial-ispec counterpart of `forall_ispec_uncurry`. -/
theorem forall_dispec_uncurry {α β γ : Type _}
    (P : α → β → IProp) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, dispec (Std.uncurry P value ∗ F) (next value) Q) ↔
      ∀ first second, dispec (P first second ∗ F) (next (first, second)) Q := by
  constructor
  · intro h first second
    exact h (first, second)
  · intro h ⟨first, second⟩
    exact h first second

theorem uncurry_apply {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    Std.uncurry f p = f p.1 p.2 := by
  cases p
  rfl

theorem uncurry_eq {α β γ : Type _} (f : α → β → γ) :
    Std.uncurry f = fun p => f p.1 p.2 := by
  funext p
  exact uncurry_apply f p

theorem uncurry'_eq {α β γ : Type _} (f : α → β → γ) :
    Std.WP.uncurry' f = fun p => f p.1 p.2 := by
  funext p
  exact Std.WP.uncurry'_eq p f

/- The `⇓` is inside `atomic` so that the parser backtracks when it is absent:
`(m) ⦃ value => p ⦄`, the pure-computation notation of `Aeneas.SepLogic.WP`,
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

/-- Build a marked postcondition from the parsed binder array. -/
private def mkPostWith (curryName uncurryName : Name)
    (binders : Array Term) (body : Term) : MacroM Term :=
  mkPostSyntaxWith curryName uncurryName body 0 binders.toList

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


/-! ### `ispec` rules -/

private theorem ispec_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) {h : Heap} (hPre : P h) :
    TotalSpec handler (fun value h' => Q value h') m h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact hSpec.mono fun value => sep_elim_right (Q value) emp

/-- Failure has no total pure specification. -/
@[simp]
theorem spec_fail (error : Error) (Q : α → Prop) :
    ¬ spec (Result.fail error) Q :=
  fun hSpec => (ispec_apply hSpec (h := ∅) trivial).vis_view

theorem ispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

/-- The frame rule, framing on the left.  `ispec_frame` adds its resource on
the right; a program that walks a data structure usually has to keep what it is
already past on the left. -/
theorem ispec_frame_left {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (H ∗ P) m (fun value => H ∗ Q value) := by
  intro F h hPre
  have hSwapped : (P ∗ (H ∗ F)) h :=
    (sep_assoc P H F).mp h
      ((sep_mono (sep_comm H P).mp (entails_refl F)) h hPre)
  refine (hTriple (H ∗ F) h hSwapped).mono fun value heap hPost => ?_
  exact (sep_mono (sep_comm (Q value) H).mp (entails_refl F)) heap
    ((sep_assoc (Q value) H F).mpr heap hPost)

theorem ispec_conseq {P' P : IPre} {m : Result α}
    {Q' Q : IPost α}
    (hTriple : ispec P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    ispec P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (hQ value) (entails_refl F)

/-- An arbitrary postcondition resource may be discarded.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem ispec_hany_post {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m (Q ∗+ H)) :
    ispec P m Q :=
  ispec_conseq hTriple (entails_refl P)
    (fun value => sep_elim_right (Q value) H)

/-- An arbitrary precondition resource may be discarded. -/
theorem ispec_hany_pre {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) :
    ispec (P ∗ H) m Q :=
  ispec_hany_post (ispec_frame hTriple H)

theorem ispec_ipure {P : Prop} {H : IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : P → ispec H m Q) :
    ispec (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, hHF⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hHF

/-- Extract a pure fact from an arbitrary position in a separating
precondition. `iintro_shallow` supplies the rearrangement equality without
unfolding representation predicates. -/
theorem ispec_ipure_anywhere (P : Prop) (H' : IPre) {H : IPre}
    {m : Result α} {Q : IPost α}
    (hExtract : H = iprop(⌜P⌝ ∗ H'))
    (hTriple : P → ispec H' m Q) :
    ispec H m Q := by
  rw [hExtract]
  exact ispec_ipure hTriple

/-- Protect the frame while `step` extracts facts from a callee postcondition. -/
theorem ispec_introFrame (Qm F : IPre) {m : Result α} {Q : IPost α}
    (hTriple : ispec (Qm ∗ introFrame F) m Q) :
    ispec (Qm ∗ F) m Q := by
  simpa only [introFrame_eq] using hTriple

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `ispec_ipure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem ispec_ipure_keep {P : Prop} {H : IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : P → ispec (⌜P⌝ ∗ H) m Q) :
    ispec (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, _⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hPre

theorem ispec_exists {ι : Sort _} {J : ι → IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : ∀ x, ispec (J x) m Q) :
    ispec iprop(∃ x, J x) m Q := by
  intro F h hPre
  obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
  exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

theorem ispec_conseq_frame {H₂ : IProp} {H₁ H : IPre}
    {Q₁ Q : IPost α}
    {m : Result α}
    (hTriple : ispec H₁ m Q₁)
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    ispec H m Q :=
  ispec_conseq (ispec_frame hTriple H₂) hPre hPost

theorem ispec_ipure' {P : Prop} {m : Result α} {Q : IPost α}
    (hTriple : P → ispec emp m Q) :
    ispec ⌜P⌝ m Q := by
  intro F h hPre
  have ⟨hP, hF⟩ := (sep_pure_l P F h).mp hPre
  exact hTriple hP F h ((sep_emp_l F).mpr h hF)

/-- A ispec with a pure precondition and postcondition is a pure implication
whose conclusion owns nothing. -/
theorem ispec_ipure_iff {P : Prop} {m : Result α} {Q : α → Prop} :
    ispec ⌜P⌝ m (fun value => ⌜Q value⌝) ↔
      (P → ispec emp m (fun value => ⌜Q value⌝)) := by
  constructor
  · intro hTriple hP
    exact ispec_conseq hTriple ((entails_emp_ipure_iff P).2 hP)
      (fun _ => entails_refl _)
  · exact ispec_ipure'

theorem ispec_pure {P : IPre} {Q : IPost α} {value : α}
    (hPost : P ⊢ Q value) :
    ispec P (pure value : Result α) Q := by
  intro F h hPre
  exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- A guarded modification is local at `h` when, for every frame disjoint from
`h`, its guard holds and its output splits into an owned result and the
unchanged frame. Quantifying over frames here is what makes `guardedModifyWp`
upward-closed and validates the frame rule, for an arbitrary guard and
modification.

This is the raw form, on plain heap predicates rather than assertions. -/
def guardedModifyLocal {EventResult : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → EventResult × Heap)
    (Q : EventResult → Heap → Prop) (h : Heap) : Prop :=
  ∀ frame, PartialCommMonoid.Compatible h frame →
    ∃ hPre : pre (h ∪ frame), ∃ h',
      PartialCommMonoid.Compatible h' frame ∧
      (modify (h ∪ frame) hPre).2 = h' ∪ frame ∧
      Q (modify (h ∪ frame) hPre).1 h'

theorem guardedModifyLocal.mono {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {Q Q' : EventResult → Heap → Prop}
    (hQ : ∀ value h', Q value h' → Q' value h') {h : Heap}
    (hWp : guardedModifyLocal pre modify Q h) : guardedModifyLocal pre modify Q' h := by
  intro frame hDisjoint
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp frame hDisjoint
  exact ⟨hPre, h', hDisjoint', hModify, hQ _ h' hPost⟩

theorem guardedModifyLocal.up_closed {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {Q : EventResult → Heap → Prop}
    (hQ : ∀ value h h', Q value h → Heap.Sub h h' → Q value h')
    {h hBig : Heap} (hWp : guardedModifyLocal pre modify Q h) (hSub : Heap.Sub h hBig) :
    guardedModifyLocal pre modify Q hBig := by
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSub
  intro frame hDisjointFrame
  obtain ⟨hDisjointRestFrame, hDisjointCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hDisjointRest, hDisjointFrame⟩
  have hWp' := hWp (rest ∪ frame) hDisjointCombined
  rw [← PartialCommMonoid.union_assoc hDisjointRest hDisjointFrame] at hWp'
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp'
  obtain ⟨hDisjoint'Rest, hDisjoint'Frame⟩ :=
    (PartialCommMonoid.compatible_assoc h' rest frame).mpr
      ⟨hDisjointRestFrame, hDisjoint'⟩
  refine ⟨hPre, h' ∪ rest, hDisjoint'Frame, ?_, ?_⟩
  · simpa only [PartialCommMonoid.union_assoc
      hDisjoint'Rest hDisjoint'Frame] using hModify
  · exact hQ _ h' _ hPost (Heap.Sub.union_left hDisjoint'Rest)

/-- The weakest precondition of a guarded modification: the assertion holding of
exactly the heaps at which the modification is local with respect to `Q`. -/
def guardedModifyWp {EventResult : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → EventResult × Heap) : Wp EventResult where
  wp Q := {
    holds := guardedModifyLocal pre modify fun value => (Q value).holds
    up_closed := fun hWp hSub =>
      guardedModifyLocal.up_closed
        (fun value _ _ hQ hSub' => (Q value).up_closed hQ hSub') hWp hSub }
  monotone hQ _ hWp := guardedModifyLocal.mono (fun value h' => hQ value h') hWp

/-- The frame rule for one event: the frame an `ispec` carries is absorbed into
the frame the denotation already quantifies over. -/
theorem guardedModifyWp_frame {EventResult : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → EventResult × Heap) (Q : IPost EventResult) (H : IProp) :
    guardedModifyWp pre modify Q ∗ H ⊢ guardedModifyWp pre modify (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, hWp, hH⟩
  intro frame hDisjointFrame
  obtain ⟨hDisjoint₂Frame, hDisjointCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ frame).mp
      ⟨hDisjoint, hDisjointFrame⟩
  have hWp' := hWp (h₂ ∪ frame) hDisjointCombined
  rw [← PartialCommMonoid.union_assoc hDisjoint hDisjointFrame] at hWp'
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp'
  obtain ⟨hDisjoint'H₂, hDisjoint'Frame⟩ :=
    (PartialCommMonoid.compatible_assoc h' h₂ frame).mpr
      ⟨hDisjoint₂Frame, hDisjoint'⟩
  refine ⟨hPre, h' ∪ h₂, hDisjoint'Frame, ?_, ?_⟩
  · simpa only [PartialCommMonoid.union_assoc
      hDisjoint'H₂ hDisjoint'Frame] using hModify
  · exact ⟨h', h₂, hDisjoint'H₂, rfl, hPost, hH⟩

/-- The weakest precondition is sound for total correctness: run the event on
exactly the heap it owns, taking the frame to be empty.  This is the only place
`guardedModifyWp` meets `TotalSpec`, and the only place a guarded modification
is proved correct: `TotalSpec.vis` hands the event to the handler, whose
`guardedModify` case demands the guard and the postcondition of what the
modification returns. -/
private theorem guardedModifyWp_spec {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {Q : IPost α} {h : Heap}
    (hWp : guardedModifyWp pre modify Q h) :
    TotalSpec handler (fun value h' => Q value h')
      (Result.guardedModify pre modify) h := by
  have hWp' := hWp Heap.empty (PartialCommMonoid.compatible_comm
    (PartialCommMonoid.compatible_empty_left h))
  simp only [Heap.union_empty] at hWp'
  obtain ⟨hPre, h', -, hModify, hPost⟩ := hWp'
  subst h'
  refine TotalSpec.vis (H := handler)
    (event := RustEffect.Input.guardedModify _ pre modify) ?_
  exact ⟨hPre, .ret hPost⟩

/-- The specification of a guarded modification is what its weakest precondition
says: absorb the ispec's frame into the one `guardedModifyWp` quantifies over,
then read off total correctness. -/
theorem ispec_guardedModify {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {P : IPre} {Q : IPost α}
    (hWp : P ⊢ guardedModifyWp pre modify Q) :
    ispec P (Result.guardedModify pre modify) Q := fun F h hPre =>
  guardedModifyWp_spec
    (guardedModifyWp_frame pre modify Q F h
      (sep_mono hWp (entails_refl F) h hPre))

theorem ispec_bind {α β : Type u} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β}
    (hFirst : ispec P m Q₁)
    (hNext : ∀ value, ispec (Q₁ value) (next value) Q) :
    ispec P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

/-- `ispec_bind` on `Aeneas.Std.bind` rather than on `>>=`.

The `Bind` class puts the two value types in the *same* universe, which a call
in a translated Rust program need not: a function returning a `Type u` may be
followed by a continuation returning a `Type v`.  `Aeneas.Std.bind` is the
two-universe bind `Result` is really given, so the rule `step` uses is this one.
-/
theorem ispec_bind' {α : Type u} {β : Type v} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β}
    (hFirst : ispec P m Q₁)
    (hNext : ∀ value, ispec (Q₁ value) (next value) Q) :
    ispec P (Aeneas.Std.bind m next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem ispec_seq {α β : Type u} {P H : IPre} {Q : IPost β}
    {m₁ : Result α} {m₂ : Result β}
    (hFirst : ispec P m₁ (fun _ => H))
    (hSecond : ispec H m₂ Q) :
    ispec P (m₁ >>= fun _ => m₂) Q :=
  ispec_bind hFirst (fun _ => hSecond)

/-! ### `dispec` rules -/

private theorem dispec_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) {h : Heap} (hPre : P h) :
    PartialSpec handler (fun value h' => Q value h') m h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact hSpec.mono fun value => sep_elim_right (Q value) emp

/-- Failure has no partial pure specification: divergence is permitted, not
stuckness. -/
@[simp]
theorem dspec_fail (error : Error) (Q : α → Prop) :
    ¬ dspec (Result.fail error) Q :=
  fun hSpec => (dispec_apply hSpec (h := ∅) trivial).vis_view

theorem dispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) (H : IProp) : dispec (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

theorem dispec_conseq {P' P : IPre} {m : Result α} {Q' Q : IPost α}
    (hTriple : dispec P' m Q') (hP : P ⊢ P') (hQ : Q' ⊢+ Q) : dispec P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (hQ value) (entails_refl F)

theorem dispec_hany_post {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m (Q ∗+ H)) : dispec P m Q :=
  dispec_conseq hTriple (entails_refl P) (fun value => sep_elim_right (Q value) H)

theorem dispec_hany_pre {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) : dispec (P ∗ H) m Q :=
  dispec_hany_post (dispec_frame hTriple H)

theorem dispec_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : P → dispec H m Q) : dispec (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, hHF⟩ := (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hHF

/-- Partial-ispec counterpart of `ispec_ipure_anywhere`. -/
theorem dispec_ipure_anywhere (P : Prop) (H' : IPre) {H : IPre}
    {m : Result α} {Q : IPost α}
    (hExtract : H = iprop(⌜P⌝ ∗ H'))
    (hTriple : P → dispec H' m Q) :
    dispec H m Q := by
  rw [hExtract]
  exact dispec_ipure hTriple

/-- Partial-ispec counterpart of `ispec_introFrame`. -/
theorem dispec_introFrame (Qm F : IPre) {m : Result α} {Q : IPost α}
    (hTriple : dispec (Qm ∗ introFrame F) m Q) :
    dispec (Qm ∗ F) m Q := by
  simpa only [introFrame_eq] using hTriple

/-- Copy a pure fact of the precondition into the local context without
consuming it. -/
theorem dispec_ipure_keep {P : Prop} {H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : P → dispec (⌜P⌝ ∗ H) m Q) : dispec (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, _⟩ := (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hPre

theorem dispec_ipure' {P : Prop} {m : Result α} {Q : IPost α}
    (hTriple : P → dispec emp m Q) : dispec ⌜P⌝ m Q := by
  intro F h hPre
  have ⟨hP, hF⟩ := (sep_pure_l P F h).mp hPre
  exact hTriple hP F h ((sep_emp_l F).mpr h hF)

/-- A partial ispec with a pure precondition and postcondition is a pure
implication whose conclusion owns nothing. -/
theorem dispec_ipure_iff {P : Prop} {m : Result α} {Q : α → Prop} :
    dispec ⌜P⌝ m (fun value => ⌜Q value⌝) ↔
      (P → dispec emp m (fun value => ⌜Q value⌝)) := by
  constructor
  · intro hTriple hP
    exact dispec_conseq hTriple ((entails_emp_ipure_iff P).2 hP)
      (fun _ => entails_refl _)
  · exact dispec_ipure'

theorem dispec_exists {ι : Sort _} {J : ι → IPre} {m : Result α} {Q : IPost α}
    (hTriple : ∀ x, dispec (J x) m Q) : dispec iprop(∃ x, J x) m Q := by
  intro F h hPre
  obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
  exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

theorem dispec_conseq_frame {H₂ : IProp} {H₁ H : IPre} {Q₁ Q : IPost α}
    {m : Result α} (hTriple : dispec H₁ m Q₁) (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) : dispec H m Q :=
  dispec_conseq (dispec_frame hTriple H₂) hPre hPost

theorem dispec_pure {P : IPre} {Q : IPost α} {value : α} (hPost : P ⊢ Q value) :
    dispec P (pure value : Result α) Q := by
  intro F h hPre
  exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- Divergence satisfies every partial ispec: nothing is claimed of a run that
does not stop, not even that it owns anything. -/
theorem dispec_div {P : IPre} {Q : IPost α} :
    dispec P (ITree.div : Result α) Q :=
  fun _ _ _ => PartialSpec.div

theorem dispec_bind {α β : Type u} {P : IPre} {Q₁ : IPost α} {Q : IPost β} {m : Result α}
    {next : α → Result β} (hFirst : dispec P m Q₁)
    (hNext : ∀ value, dispec (Q₁ value) (next value) Q) :
    dispec P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

/-- `dispec_bind` on `Aeneas.Std.bind`, the two-universe bind.  See
`ispec_bind'`. -/
theorem dispec_bind' {α : Type u} {β : Type v} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β} (hFirst : dispec P m Q₁)
    (hNext : ∀ value, dispec (Q₁ value) (next value) Q) :
    dispec P (Aeneas.Std.bind m next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem dispec_seq {α β : Type u} {P H : IPre} {Q : IPost β} {m₁ : Result α} {m₂ : Result β}
    (hFirst : dispec P m₁ (fun _ => H)) (hSecond : dispec H m₂ Q) :
    dispec P (m₁ >>= fun _ => m₂) Q :=
  dispec_bind hFirst (fun _ => hSecond)

/-! ## Ramified rules -/

/-- The ramified frame rule. The wand's conclusion is affine, so `Q` alone is
enough to permit leftover resources to be discarded. -/
theorem ispec_ramified_frame {α : Type u} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : ispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    ispec P m Q :=
  ispec_conseq_frame hStep hPre (postWand_cancel Qm Q)

/-- The ramified frame rule for a call followed by a continuation. -/
theorem ispec_ramified_bind {α β : Type u} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : ispec Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, ispec (Qm value ∗ F) (next value) Q) :
    ispec P (m >>= next) Q :=
  ispec_bind (ispec_conseq (ispec_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- The ramified frame rule for a call followed by a continuation, on the
two-universe `Aeneas.Std.bind`.  See `ispec_bind'`. -/
theorem ispec_ramified_bind' {α : Type u} {β : Type v} {P Pm F : IPre}
    {Qm : IPost α} {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : ispec Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, ispec (Qm value ∗ F) (next value) Q) :
    ispec P (Aeneas.Std.bind m next) Q :=
  ispec_bind' (ispec_conseq (ispec_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- Rewrite part of an `ispec` precondition using an entailment. -/
theorem ispec_rewrite {α : Type u} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
    (hPart : H₁ ⊢ H₂) (hRest : ispec (H₂ ∗ H₃) m Q) : ispec (H₁ ∗ H₃) m Q :=
  ispec_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

theorem dispec_ramified_frame {α : Type u} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : dispec Pm m Qm) (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dispec P m Q :=
  dispec_conseq_frame hStep hPre (postWand_cancel Qm Q)

theorem dispec_ramified_bind {α β : Type u} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α} (hStep : dispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dispec (Qm value ∗ F) (next value) Q) :
    dispec P (m >>= next) Q :=
  dispec_bind
    (dispec_conseq (dispec_frame hStep F) hPre (fun _ => entails_refl _)) hNext

/-- The ramified bind rule on the two-universe `Aeneas.Std.bind`, for a partial
goal.  See `ispec_bind'`. -/
theorem dispec_ramified_bind' {α : Type u} {β : Type v} {P Pm F : IPre}
    {Qm : IPost α} {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : dispec Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, dispec (Qm value ∗ F) (next value) Q) :
    dispec P (Aeneas.Std.bind m next) Q :=
  dispec_bind'
    (dispec_conseq (dispec_frame hStep F) hPre (fun _ => entails_refl _)) hNext

/-- Rewrite part of a partial ispec's precondition using an entailment. -/
theorem dispec_rewrite {α : Type u} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
    (hPart : H₁ ⊢ H₂) (hRest : dispec (H₂ ∗ H₃) m Q) : dispec (H₁ ∗ H₃) m Q :=
  dispec_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

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


/-! ### Bridging lemmas for the pure judgments

These lemmas expose the return and divergence rules without requiring callers
to unseal `Result`. Rules registered for concrete constructors are stated
outside this section, where `Result.ok` and `Result.div` are no longer locally
reducible, so they are indexed under their public names. -/

theorem ispec_ok_apply {α : Type u} {Q : IPost α} {x : α}
    (hTriple : ispec emp (Result.ok x) Q) : Q x ∅ :=
  (ispec_apply hTriple (h := ∅) trivial).ret_post

theorem ispec_ok_intro {α : Type u} {Q : IPost α} {x : α} (hQ : ∀ h, Q x h) :
    ispec emp (Result.ok x) Q :=
  ispec_pure fun h _ => hQ h

theorem dispec_ok_apply {α : Type u} {Q : IPost α} {x : α}
    (hTriple : dispec emp (Result.ok x) Q) : Q x ∅ :=
  (dispec_apply hTriple (h := ∅) trivial).ret_post

theorem dispec_ok_intro {α : Type u} {Q : IPost α} {x : α} (hQ : ∀ h, Q x h) :
    dispec emp (Result.ok x) Q :=
  dispec_pure fun h _ => hQ h

theorem ispec_div_elim {α : Type u} {Q : IPost α}
    (hTriple : ispec emp (Result.div : Result α) Q) : False :=
  (ispec_apply hTriple (h := ∅) trivial).div_false

theorem dispec_div_intro {α : Type u} {P : IPre} {Q : IPost α} :
    dispec P (Result.div : Result α) Q :=
  dispec_div

end ResultImplementation

/-! ## Pure computations

`spec` and `dspec` are named judgments with ordinary `α → Prop`
postconditions. Their definitions preserve the meaning of the former notation:
the corresponding SL ispec at `emp` and a pure postcondition.

Each judgment has its own `step` registration. Pure specifications lift to SL
specifications for framing. SL specifications lift back only when their
precondition is `emp` and their postcondition is pure. Pure goals stay in the
pure judgment; proofs that need spatial intermediate assertions use SL goals
instead. Total specifications also lift to partial ones, never conversely. -/

theorem spec_iff {m : Result α} {Q : α → Prop} :
    spec m Q ↔ ispec emp m (fun value => ⌜Q value⌝) := Iff.rfl

theorem dspec_iff {m : Result α} {Q : α → Prop} :
    dspec m Q ↔ dispec emp m (fun value => ⌜Q value⌝) := Iff.rfl

theorem spec_mono {α : Type u} {Q : α → Prop}
    (m : Result α) (Qm : α → Prop) (h : spec m Qm)
    (hPost : ∀ value, Qm value → Q value) : spec m Q :=
  ispec_conseq h (entails_refl emp) (fun value _ => hPost value)

theorem dspec_mono {α : Type u} {Q : α → Prop}
    (m : Result α) (Qm : α → Prop) (h : dspec m Qm)
    (hPost : ∀ value, Qm value → Q value) : dspec m Q :=
  dispec_conseq h (entails_refl emp) (fun value _ => hPost value)

theorem spec_bind {α : Type u} {β : Type v} {next : α → Result β} {Q : β → Prop}
    (m : Result α) (Qm : α → Prop) (h : spec m Qm)
    (hNext : ∀ value, Qm value → spec (next value) Q) :
    spec (Aeneas.Std.bind m next) Q :=
  ispec_bind' h (fun value => ispec_ipure' (hNext value))

theorem dspec_bind {α : Type u} {β : Type v} {next : α → Result β} {Q : β → Prop}
    (m : Result α) (Qm : α → Prop) (h : dspec m Qm)
    (hNext : ∀ value, Qm value → dspec (next value) Q) :
    dspec (Aeneas.Std.bind m next) Q :=
  dispec_bind' h (fun value => dispec_ipure' (hNext value))

theorem forall_uncurry' {α β : Type _} (P : α → β → Prop) (Q : α × β → Prop) :
    (∀ value, Std.WP.uncurry' P value → Q value) ↔
      ∀ first second, P first second → Q (first, second) :=
  ⟨fun h first second => h (first, second), fun h ⟨first, second⟩ => h first second⟩

theorem forall_uncurry {α β : Type _} (P : α → β → Prop) (Q : α × β → Prop) :
    (∀ value, Std.uncurry P value → Q value) ↔
      ∀ first second, P first second → Q (first, second) :=
  ⟨fun h first second => h (first, second), fun h ⟨first, second⟩ => h first second⟩

/-- Keep tuple binders visible when lifting a pure postcondition into SL. -/
theorem forall_ispec_ipure_uncurry' {α β γ : Type _}
    (P : α → β → Prop) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, ispec (⌜Std.WP.uncurry' P value⌝ ∗ F) (next value) Q) ↔
      ∀ first second, ispec (⌜P first second⌝ ∗ F) (next (first, second)) Q :=
  forall_ispec_uncurry' (fun first second => ⌜P first second⌝) F next Q

theorem forall_ispec_ipure_uncurry {α β γ : Type _}
    (P : α → β → Prop) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, ispec (⌜Std.uncurry P value⌝ ∗ F) (next value) Q) ↔
      ∀ first second, ispec (⌜P first second⌝ ∗ F) (next (first, second)) Q :=
  forall_ispec_uncurry (fun first second => ⌜P first second⌝) F next Q

theorem forall_dispec_ipure_uncurry' {α β γ : Type _}
    (P : α → β → Prop) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, dispec (⌜Std.WP.uncurry' P value⌝ ∗ F) (next value) Q) ↔
      ∀ first second, dispec (⌜P first second⌝ ∗ F) (next (first, second)) Q :=
  forall_dispec_uncurry' (fun first second => ⌜P first second⌝) F next Q

theorem forall_dispec_ipure_uncurry {α β γ : Type _}
    (P : α → β → Prop) (F : IProp) (next : α × β → Result γ) (Q : IPost γ) :
    (∀ value, dispec (⌜Std.uncurry P value⌝ ∗ F) (next value) Q) ↔
      ∀ first second, dispec (⌜P first second⌝ ∗ F) (next (first, second)) Q :=
  forall_dispec_uncurry (fun first second => ⌜P first second⌝) F next Q

open Lean Elab Meta Tactic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation.

It is stated on `Aeneas.Std.bind` rather than on `>>=`: the `Bind` class forces
the two value types into one universe, and a call in a translated program need
not respect that. -/
theorem ispec_step_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β}
    (m : Result α) (Qm : IPost α) (hStep : ispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, ispec (Qm value ∗ F) (next value) Q) :
    ispec P (Aeneas.Std.bind m next) Q :=
  ispec_ramified_bind' hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call. -/
theorem ispec_step_mono {α : Type u} {P Pm : IPre} {Q : IPost α}
    (m : Result α) (Qm : IPost α) (hStep : ispec Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    ispec P m Q :=
  ispec_ramified_frame hStep hRamified

/-- Bind rule used by `step` on a partial goal.  See `ispec_step_bind`. -/
theorem dispec_step_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β}
    {Q : IPost β} (m : Result α) (Qm : IPost α) (hStep : dispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dispec (Qm value ∗ F) (next value) Q) :
    dispec P (Aeneas.Std.bind m next) Q :=
  dispec_ramified_bind' hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call on a partial goal. -/
theorem dispec_step_mono {α : Type u} {P Pm : IPre} {Q : IPost α} (m : Result α)
    (Qm : IPost α) (hStep : dispec Pm m Qm) (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dispec P m Q :=
  dispec_ramified_frame hStep hRamified

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- The tactic `step` runs on the goals it prepares. A no-op on a goal which is
not an `ispec`. -/
macro (name := intro_ispec) "intro_ispec" : tactic =>
  `(tactic| iintro_shallow_post)

#register_spec_info {
    spec_name := ``ispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``ispec_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``ispec_step_bind
    mk_spec_bind_skip_args := 7
    uncurry_elim_tactics := #[
      ``forall_ispec_uncurry',
      ``forall_ispec_uncurry,
      ``forall_ispec_ipure_uncurry', ``forall_ispec_ipure_uncurry,
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair, ``uncurry'_eq,
      ``uncurry_apply, ``uncurry_eq
    ]
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``ispec_ipure_iff,
      ``forall_unit,
      ``sep_emp_l_eq, ``sep_ipure_true_l_eq,
      ``entails_emp_postWand_ipure_iff,
      ``entails_emp_ipure_iff, ``entails_refl, ``true_imp_iff
    ]
    intro_tactic := some ``intro_ispec
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
    mk_spec_mono := ``dispec_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``dispec_step_bind
    mk_spec_bind_skip_args := 7
    uncurry_elim_tactics := #[
      ``forall_dispec_uncurry',
      ``forall_dispec_uncurry,
      ``forall_dispec_ipure_uncurry', ``forall_dispec_ipure_uncurry,
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair, ``uncurry'_eq,
      ``uncurry_apply, ``uncurry_eq
    ]
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``dispec_ipure_iff,
      ``forall_unit,
      ``sep_emp_l_eq, ``sep_ipure_true_l_eq,
      ``entails_emp_postWand_ipure_iff,
      ``entails_emp_ipure_iff, ``entails_refl, ``true_imp_iff
    ]
    intro_tactic := some ``intro_ispec
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
    uncurry_elim_tactics := #[``forall_uncurry', ``forall_uncurry]
    qimp_elim_tactics := #[
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair, ``uncurry'_eq,
      ``uncurry_apply, ``uncurry_eq,
      ``forall_eq, ``forall_eq', ``forall_unit, ``true_imp_iff
    ]
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
    uncurry_elim_tactics := #[``forall_uncurry', ``forall_uncurry]
    qimp_elim_tactics := #[
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair, ``uncurry'_eq,
      ``uncurry_apply, ``uncurry_eq,
      ``forall_eq, ``forall_eq', ``forall_unit, ``true_imp_iff
    ]
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
macro "wp_pures" : tactic => `(tactic| apply ispec_pure)

/-- Apply a specification to the goal, frame the resources it does not need,
and discharge the resulting entailment with `isimpl`. -/
syntax "wp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| wp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine ispec_ramified_frame $thm ?_)
      | none => `(tactic| refine ispec_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state an already-proved ispec under a weaker postcondition. -/
macro "wp_mono " thm:term : tactic =>
  `(tactic| (apply ispec_conseq $thm (entails_refl _) <;> (intro _ <;> iframe)))

/-- Reduce a partial ispec about a terminal `pure v` to the entailment
`P ⊢ Q v`. -/
macro "dwp_pures" : tactic => `(tactic| apply dispec_pure)

/-- Apply a partial specification to the goal, frame the resources it does not
need, and discharge the resulting entailment with `isimpl`. -/
syntax "dwp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| dwp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine dispec_ramified_frame $thm ?_)
      | none => `(tactic| refine dispec_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state an already-proved partial ispec under a weaker postcondition. -/
macro "dwp_mono " thm:term : tactic =>
  `(tactic| (apply dispec_conseq $thm (entails_refl _) <;> (intro _ <;> iframe)))

@[step]
theorem ret.spec (value : α) :
    ⦃ emp ⦄ Result.ok value ⦃⇓ result => ⌜result = value⌝⦄ :=
  ispec_pure fun _ _ => rfl

@[step]
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : Result α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ret.spec value

/-- Pure returns stay in the pure judgment, allowing `step` to infer ordinary
predicate postconditions without introducing spatial entailments. -/
@[step]
theorem ok_spec (value : α) :
    spec (Result.ok value) (fun result => result = value) :=
  ret.spec value

@[step]
theorem pure_spec (value : α) :
    spec (Pure.pure value : Result α) (fun result => result = value) :=
  ok_spec value

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

The syntax is `scoped` in `Aeneas.SepLogic.WP` because `Aeneas.Std.WP` declares
the identical surface for its own, separate judgment; a file chooses between
them by which namespace it opens.
-/

namespace WP

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
    `(Aeneas.SepLogic.spec $m $post)

/-- Macro expansion for several binders. -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.SepLogic.spec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x => $p ⦄div) => do
    let post ← mkPurePost #[x] p
    `(Aeneas.SepLogic.dspec $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(Aeneas.SepLogic.dspec $m $post)

/-- Macro expansion for a postcondition given as a predicate. -/
scoped macro_rules (kind := pureSpecPred)
  | `($m ⦃ $p ⦄) => `(Aeneas.SepLogic.spec $m $p)

scoped macro_rules (kind := pureDspecPred)
  | `($m ⦃ $p ⦄div) => `(Aeneas.SepLogic.dspec $m $p)

/-!
# Pretty-printing

The named pure judgments print their predicate postconditions directly.
SL ispecs always use the separating notation, including ispecs at `emp`
with pure postconditions.
-/

open Lean PrettyPrinter
open Delaborator SubExpr
open Std.Delab
  (enterLams delabBindersWith buildTupleTerm delabUncurryAsTupleWith)

/-- Enter one explicit tuple binder without consuming continuation lambdas. -/
private partial def enterPureUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterPureUncurryOnce acc' k
      else
        enterPureUncurryOnce acc' k
  | _ => k acc

private def isPurePostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | Std.WP.uncurry' _ _ _ _ => true
  | Std.uncurry _ _ _ _ => true
  | _ => false

/-- Recover separate binders, explicit tuple binders, and the final pure body
from the transparent marker chain produced by `mkPurePost`. -/
private partial def delabPurePost : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | Std.WP.uncurry' _ _ _ _ =>
    withAppArg do
      match_expr (← getExpr).consumeMData with
      | Std.uncurry _ _ _ _ =>
        withAppArg <| enterPureUncurryOnce #[] fun tupleBinders => do
          let (patterns, (moreBinders, body)) ←
            delabBindersWith ``Std.uncurry tupleBinders.toList delabPurePost
          return (#[← buildTupleTerm patterns] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | Std.uncurry _ _ _ _ =>
    withAppArg do
      let (tupleBinder, body) ←
        delabUncurryAsTupleWith ``Std.uncurry delab
      return (#[tupleBinder], body)
  | _ => delabLamsThenRecurse
where
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    let e := (← getExpr).consumeMData
    if let .lam _ _ body _ := e then
      if !body.consumeMData.isLambda && !isPurePostBinderWrapper body then
        withBindingBodyUnusedName fun binder =>
          return (#[⟨binder⟩], ← delab)
      else
        enterLams #[] fun binders => do
          if binders.size == 1 && isPurePostBinderWrapper (← getExpr) then
            let (patterns, (moreBinders, body)) ←
              delabBindersWith ``Std.uncurry binders.toList delabPurePost
            return (patterns ++ moreBinders, body)
          else
            delabBindersWith ``Std.uncurry binders.toList delab
    else
      return (#[], ← delab)

/-- Enter one explicit SL tuple binder without consuming continuation lambdas. -/
private partial def enterSLUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterSLUncurryOnce acc' k
      else
        enterSLUncurryOnce acc' k
  | _ => k acc

/-- Recover separate binders, explicit tuple binders, and the final spatial
postcondition from the marker chain produced by `mkPostSyntaxWith`. -/
private partial def delabSLPost : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | Std.WP.uncurry' _ _ _ _ =>
    withAppArg do
      match_expr (← getExpr).consumeMData with
      | Std.uncurry _ _ _ _ =>
        withAppArg <| enterSLUncurryOnce #[] fun tupleBinders => do
          let (patterns, (moreBinders, body)) ←
            delabBindersWith ``Std.uncurry tupleBinders.toList delabSLPost
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
      let (binder, body) ←
        delabUncurryAsTupleWith ``Std.uncurry delab
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
@[app_delab Aeneas.SepLogic.ispec]
def delabSLISpec : Delab :=
  delabSLISpecCore ``Aeneas.SepLogic.ispec false

/-- Delaborator for partial separation-logic ispecs. -/
@[app_delab Aeneas.SepLogic.dispec]
def delabSLDispec : Delab :=
  delabSLISpecCore ``Aeneas.SepLogic.dispec true

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

@[scoped delab app.Aeneas.SepLogic.spec]
def delabPureSpec : Delab :=
  delabPureSpecCore ``Aeneas.SepLogic.spec false

@[scoped delab app.Aeneas.SepLogic.dspec]
def delabPureDspec : Delab :=
  delabPureSpecCore ``Aeneas.SepLogic.dspec true

end WP

end Aeneas.SepLogic
