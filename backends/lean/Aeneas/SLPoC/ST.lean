import Aeneas.Data.Coinductive.Spec
import Aeneas.Std.Primitives
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
# The program logic of the state monad `Result`

`Aeneas.Std.Primitives` defines `Result`, the interaction-tree monad over heap
events. This file builds its correctness judgments, derives the
separation-logic triples, and wires those triples to the `step`/`step*` tactics.

The judgments themselves are not defined here. The meaning of a heap event is
written down once, as the handler `EventSpec` of the state machine
`RustEffect.machine`, and `spec` and `dspec` are then the generic judgments
`TotalSpec` and `PartialSpec` of `Aeneas.Data.Coinductive.Spec` at that machine,
used under their generic names with their generic rules. The machine's runs —
the operational semantics `Result` is adequate for — and the certified
interpreter that runs a proved program are in `Aeneas.SLPoC.Semantics`.
-/

namespace Aeneas.SepLogic

open Aeneas.Data
open Aeneas.Data.Coinductive
open Aeneas.Std (Error Heap Result RustEffect)

universe u

section ResultImplementation

unseal Result
set_option allowUnsafeReducibility true in
attribute [local reducible] Result Result.ok Result.vis Result.div Aeneas.Std.bind

/-! ## The machine of `Result`

`Result` is an interaction tree, so it fixes no meaning for its events; a state
machine (`Aeneas.Data.Coinductive.StateMachine`) does, by saying how one event
is answered on one heap. `RustEffect.machine` is that machine, and `EventSpec`
— its handler — is the single place the meaning of a heap event is written
down: the correctness judgments below are the generic judgments of
`Aeneas.Data.Coinductive.Spec` at this machine, and the runs
`Aeneas.SLPoC.Semantics` proves them adequate for are its runs. -/

/-- What performing `event` on the heap `h` demands, with what follows left to
`C`: a heap event must be defined on the heap it is performed on, and what
follows runs on the answer and the heap it produces; failure is rejected
outright, having no possible answer at all.

This is the whole semantics of the events of `Result`, and the only definition
in this file that looks at them. -/
@[reducible]
def EventSpec : (event : RustEffect.I) → Heap →
    (RustEffect.O event → Heap → Prop) → Prop
  | .guardedModify _ pre modify, h, C =>
      ∃ hPre : pre h, C (.up (modify h hPre).1) (modify h hPre).2
  | .fail _, _, _ => False

/-- What an event demands is monotone in what follows. -/
theorem EventSpec.mono {event : RustEffect.I} {h : Heap}
    {C C' : RustEffect.O event → Heap → Prop}
    (hC : ∀ answer h', C answer h' → C' answer h')
    (hEvent : EventSpec event h C) : EventSpec event h C' := by
  cases event with
  | guardedModify => exact hEvent.imp fun _ hNext => hC _ _ hNext
  | fail => exact hEvent.elim

/-- The machine of `Result`: its states are heaps, and it answers an event the
way `EventSpec` says. Everything below is the generic theory of
`Aeneas.Data.Coinductive` at this one machine. -/
@[reducible]
def RustEffect.machine : StateMachine RustEffect where
  State := Heap
  handle := EventSpec
  handle_mono := EventSpec.mono

/-- The machine is **positively conjunctive**: whatever a heap event owes each
of a nonempty set of demands on a given heap, it owes all of them in one single
transition.  It holds because the guard of an event is a *proposition*, so the
modifier cannot depend on which proof of the guard it is performed with: there
is nothing for the machine to choose.

This is what the admissibility of partial correctness
(`Coinductive.PartialSpec.admissible`, used by `dspec_admissible`) and the
adequacy of `dspec` need. -/
theorem RustEffect.machine_conjunctive : RustEffect.machine.Conjunctive := by
  intro event h Demands ⟨C₀, hC₀⟩ hAll
  cases event with
  | guardedModify EventResult pre modify =>
      exact ⟨(hAll C₀ hC₀).1, fun C hC => (hAll C hC).2⟩
  | fail error => exact (hAll C₀ hC₀).elim

/-- The machine **resolves** its transitions: the one way it answers a heap
event answers it with one definite outcome.  This is what the adequacy of `spec`
needs, and it makes the machine feasible: no heap event is a miracle. -/
theorem RustEffect.machine_resolves : RustEffect.machine.Resolves := by
  intro event h C hHandle
  cases event with
  | guardedModify EventResult pre modify => exact ⟨_, _, hHandle.2, hHandle.1, rfl, rfl⟩
  | fail error => exact hHandle.elim

theorem RustEffect.machine_feasible : RustEffect.machine.Feasible :=
  machine_resolves.feasible

/-! ## Total and partial correctness

`Result` carries two correctness judgments, laid out here the way `Aeneas.Std.WP`
lays out `spec` and `dspec`.

`spec` is *total* correctness. As for `Aeneas.Std.WP.spec` a proof is a finite
derivation ending in `ret`; nothing proves `ITree.div` correct, so a program that
does not terminate has no proof at all.

`dspec` is the divergence-tolerant counterpart. It says what `spec` says of a
run that *stops* and nothing about a run that does not, while still requiring
every event the program reaches to be defined: divergence is permitted, being
stuck is not.

`Aeneas.Std.WP.dspec` is `spec` plus one constructor for `Result.div`, and that
suffices there because the only event of `Result` is `fail`, which has no
continuation: a computation that neither returns nor fails *is* `div`, in one
step. A program of `Result` may perform arbitrarily many heap events before
returning or failing, so an infinite run is an infinite `vis` tree and no
inductive judgment accepts it: partial correctness has to be a **greatest**
fixed point.

Neither judgment is defined here. Both are the judgments of
`Aeneas.Data.Coinductive.Spec` — `TotalSpec` and `PartialSpec`, the least and
the greatest fixed point of the same one-layer condition `SpecF`, differing only
in what divergence owes — at the machine above, and their whole theory is proved
there of an arbitrary machine: the constructors and destructors,
`TotalSpec.induction` and `PartialSpec.coinduction`, the structural rules,
admissibility, and adequacy. Use them under those names; what is added here is
only what is specific to heap events, which is what `EventSpec` reduces to at a
concrete event. -/

/-- Total correctness of `m` on the exact heap `h`. -/
abbrev spec (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  TotalSpec RustEffect.machine (fun value h' => Q value h') m h

/-- Partial correctness of `m` on the exact heap `h`, on assertions.  The
counterpart of `spec`, and named after `Aeneas.Std.WP.dspec`. -/
abbrev dspec (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  PartialSpec RustEffect.machine (fun value h' => Q value h') m h

/-- Partial correctness is admissible: it holds of the limit of a chain of
programs as soon as it holds of every program in it.  This is what
`Lean.Order.fix_induct` — the induction principle `partial_fixpoint` attaches to
a recursive definition — needs, and it is the counterpart of
`Aeneas.Std.WP.dspec_admissible`.  It holds because the machine of `Result` is
conjunctive: what the approximations demand of an event one at a time, it
answers the limit all at once. -/
theorem dspec_admissible (Q : IPost α) (h : Heap) :
    Lean.Order.admissible (fun m : Result α => dspec m Q h) :=
  PartialSpec.admissible RustEffect.machine_conjunctive _ h

/-! ### Failure

The rest of the theory is inherited rather than restated: `spec` and `dspec` are
`abbrev`s, so dot notation on a hypothesis of either finds `.ret`, `.pure`,
`.bind`, `.mono`, `.mono_le`, `.vis_view`, `.toPartial` and the rest in
`TotalSpec` and `PartialSpec`.  What is left is what only `EventSpec` knows: an
event the machine cannot answer is no more correct than one it can answer
wrongly.  A guarded modification is proved correct in one place, and that place
is `guardedModifyWp_spec`, where its weakest precondition meets `TotalSpec`. -/

/-- Failure is not totally correct: it is the event the machine cannot answer,
so `EventSpec` gives `False` outright.  `TotalSpec.div_false` rules out the
other way of not returning. -/
@[simp]
theorem spec_fail (error : Error) (Q : IPost α) (h : Heap) :
    ¬ spec (Result.fail error) Q h :=
  fun hSpec => hSpec.vis_view

@[simp]
theorem spec_fail_vis (error : Error)
    (k : RustEffect.O (RustEffect.I.fail error) → Result α)
    (Q : IPost α) (h : Heap) :
    ¬ spec (.vis (RustEffect.I.fail error) k) Q h :=
  fun hSpec => hSpec.vis_view

/-- Failure is not partially correct either: partial correctness permits
divergence, not stuckness. -/
@[simp]
theorem dspec_fail (error : Error) (Q : IPost α) (h : Heap) :
    ¬ dspec (Result.fail error) Q h :=
  fun hSpec => hSpec.vis_view

@[simp]
theorem dspec_fail_vis (error : Error)
    (k : RustEffect.O (RustEffect.I.fail error) → Result α)
    (Q : IPost α) (h : Heap) :
    ¬ dspec (.vis (RustEffect.I.fail error) k) Q h :=
  fun hSpec => hSpec.vis_view

/-! ## Hoare triples

`triple` and `dtriple` are the two judgments made local, and are declared here
side by side. Both quantify over an arbitrary frame the computation must
preserve; only `triple` claims that the computation terminates. -/

/-- A total-correctness separation triple. The quantified `F` is an arbitrary
frame that the computation must preserve. -/
def triple (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  ∀ F h, (P ∗ F) h → spec m (Q ∗+ F) h

/-- A partial-correctness separation triple.  As in `triple` the quantified `F`
is an arbitrary frame the computation must preserve; unlike `triple` it does not
claim that the computation terminates. -/
def dtriple (P : IPre) (m : Result α) (Q : IPost α) : Prop :=
  ∀ F h, (P ∗ F) h → dspec m (Q ∗+ F) h

syntax:lead (name := specSyntax)
  "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := specSyntaxPred)
  "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
syntax:lead (name := slSpecSyntax)
  " ⦃" term " ⦄" term:lead
  " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := slSpecSyntaxPred)
  " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) =>
      `(triple emp $m (fun $result => ⌜$Q⌝))
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(triple emp $m (fun _ => ⌜$Q⌝))
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄) =>
      `(triple iprop($P) $m (fun $result => iprop($Q)))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄) =>
      `(triple iprop($P) $m (fun _ => iprop($Q)))

syntax:lead (name := dspecSyntax)
  "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄div" : term
syntax:lead (name := dspecSyntaxPred)
  "(" term:lead ")" " ⦃" "⇓ " term " ⦄div" : term
syntax:lead (name := slDspecSyntax)
  " ⦃" term " ⦄" term:lead
  " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄div" : term
syntax:lead (name := slDspecSyntaxPred)
  " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄div" : term

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄div) =>
      `(dtriple emp $m (fun $result => ⌜$Q⌝))
  | `(($m) ⦃⇓ $Q:term⦄div) =>
      `(dtriple emp $m (fun _ => ⌜$Q⌝))
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄div) =>
      `(dtriple iprop($P) $m (fun $result => iprop($Q)))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄div) =>
      `(dtriple iprop($P) $m (fun _ => iprop($Q)))

theorem triple_iff (P : IPre) (m : Result α) (Q : IPost α) :
    triple P m Q ↔ ∀ F h, (P ∗ F) h → spec m (Q ∗+ F) h :=
  Iff.rfl

theorem dtriple_iff (P : IPre) (m : Result α) (Q : IPost α) :
    dtriple P m Q ↔ ∀ F h, (P ∗ F) h → dspec m (Q ∗+ F) h :=
  Iff.rfl

/-- Every total triple is a partial one.  `step` applies the `@[step]`
specifications — which state total correctness — to a partial goal through this
lifting, through the generic `TotalSpec.toPartial`. -/
theorem triple_dtriple {α : Type} {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) : dtriple P m Q :=
  fun F h hPre => (hTriple F h hPre).toPartial

/-! ### `triple` rules -/

theorem triple_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) {h : Heap} (hPre : P h) :
    spec m Q h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact hSpec.mono fun value => sep_elim_right (Q value) emp

theorem triple_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) (H : IProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

/-- The frame rule, framing on the left.  `triple_frame` adds its resource on
the right; a program that walks a data structure usually has to keep what it is
already past on the left. -/
theorem triple_frame_left {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) (H : IProp) :
    triple (H ∗ P) m (fun value => H ∗ Q value) := by
  intro F h hPre
  have hSwapped : (P ∗ (H ∗ F)) h :=
    (sep_assoc P H F).mp h
      ((sep_mono (sep_comm H P).mp (entails_refl F)) h hPre)
  refine (hTriple (H ∗ F) h hSwapped).mono fun value heap hPost => ?_
  exact (sep_mono (sep_comm (Q value) H).mp (entails_refl F)) heap
    ((sep_assoc (Q value) H F).mpr heap hPost)

theorem triple_conseq {P' P : IPre} {m : Result α}
    {Q' Q : IPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (hQ value) (entails_refl F)

/-- An arbitrary postcondition resource may be discarded.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem triple_hany_post {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m (Q ∗+ H)) :
    triple P m Q :=
  triple_conseq hTriple (entails_refl P)
    (fun value => sep_elim_right (Q value) H)

/-- An arbitrary precondition resource may be discarded. -/
theorem triple_hany_pre {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ H) m Q :=
  triple_hany_post (triple_frame hTriple H)

theorem triple_ipure {P : Prop} {H : IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : P → triple H m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, hHF⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hHF

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `triple_ipure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem triple_ipure_keep {P : Prop} {H : IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : P → triple (⌜P⌝ ∗ H) m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, _⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hPre

theorem triple_exists {ι : Sort _} {J : ι → IPre} {m : Result α}
    {Q : IPost α}
    (hTriple : ∀ x, triple (J x) m Q) :
    triple iprop(∃ x, J x) m Q := by
  intro F h hPre
  obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
  exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

theorem triple_conseq_frame {H₂ : IProp} {H₁ H : IPre}
    {Q₁ Q : IPost α}
    {m : Result α}
    (hTriple : triple H₁ m Q₁)
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    triple H m Q :=
  triple_conseq (triple_frame hTriple H₂) hPre hPost

theorem triple_ipure' {P : Prop} {m : Result α} {Q : IPost α}
    (hTriple : P → triple emp m Q) :
    triple ⌜P⌝ m Q := by
  intro F h hPre
  have ⟨hP, hF⟩ := (sep_pure_l P F h).mp hPre
  exact hTriple hP F h ((sep_emp_l F).mpr h hF)

theorem triple_pure {P : IPre} {Q : IPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : Result α) Q := by
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

/-- The frame rule for one event: the frame a triple carries is absorbed into
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
is proved correct: `TotalSpec.vis` hands the event to the machine, and what the
machine demands of it is `EventSpec` at `guardedModify` — the guard, and the
postcondition of what the modification returns. -/
theorem guardedModifyWp_spec {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {Q : IPost α} {h : Heap}
    (hWp : guardedModifyWp pre modify Q h) :
    spec (Result.guardedModify pre modify) Q h := by
  have hWp' := hWp Heap.empty (PartialCommMonoid.compatible_comm
    (PartialCommMonoid.compatible_empty_left h))
  simp only [Heap.union_empty] at hWp'
  obtain ⟨hPre, h', -, hModify, hPost⟩ := hWp'
  subst h'
  refine TotalSpec.vis (M := RustEffect.machine)
    (event := RustEffect.I.guardedModify _ pre modify) ?_
  exact ⟨hPre, .ret hPost⟩

/-- The specification of a guarded modification is what its weakest precondition
says: absorb the triple's frame into the one `guardedModifyWp` quantifies over,
then read off total correctness. -/
theorem triple_guardedModify {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {P : IPre} {Q : IPost α}
    (hWp : P ⊢ guardedModifyWp pre modify Q) :
    triple P (Result.guardedModify pre modify) Q := fun F h hPre =>
  guardedModifyWp_spec
    (guardedModifyWp_frame pre modify Q F h
      (sep_mono hWp (entails_refl F) h hPre))

theorem triple_bind {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem triple_seq {P H : IPre} {Q : IPost β}
    {m₁ : Result α} {m₂ : Result β}
    (hFirst : triple P m₁ (fun _ => H))
    (hSecond : triple H m₂ Q) :
    triple P (m₁ >>= fun _ => m₂) Q :=
  triple_bind hFirst (fun _ => hSecond)

/-! ### `dtriple` rules -/

theorem dtriple_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) {h : Heap} (hPre : P h) : dspec m Q h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact hSpec.mono fun value => sep_elim_right (Q value) emp

theorem dtriple_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) (H : IProp) : dtriple (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact hSpec.mono fun value heap => (sep_assoc (Q value) H F).mpr heap

theorem dtriple_conseq {P' P : IPre} {m : Result α} {Q' Q : IPost α}
    (hTriple : dtriple P' m Q') (hP : P ⊢ P') (hQ : Q' ⊢+ Q) : dtriple P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact hSpec.mono fun value => sep_mono (hQ value) (entails_refl F)

theorem dtriple_hany_post {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m (Q ∗+ H)) : dtriple P m Q :=
  dtriple_conseq hTriple (entails_refl P) (fun value => sep_elim_right (Q value) H)

theorem dtriple_hany_pre {P H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) : dtriple (P ∗ H) m Q :=
  dtriple_hany_post (dtriple_frame hTriple H)

theorem dtriple_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : P → dtriple H m Q) : dtriple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, hHF⟩ := (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hHF

/-- Copy a pure fact of the precondition into the local context without
consuming it. -/
theorem dtriple_ipure_keep {P : Prop} {H : IPre} {m : Result α} {Q : IPost α}
    (hTriple : P → dtriple (⌜P⌝ ∗ H) m Q) : dtriple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, _⟩ := (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hPre

theorem dtriple_ipure' {P : Prop} {m : Result α} {Q : IPost α}
    (hTriple : P → dtriple emp m Q) : dtriple ⌜P⌝ m Q := by
  intro F h hPre
  have ⟨hP, hF⟩ := (sep_pure_l P F h).mp hPre
  exact hTriple hP F h ((sep_emp_l F).mpr h hF)

theorem dtriple_exists {ι : Sort _} {J : ι → IPre} {m : Result α} {Q : IPost α}
    (hTriple : ∀ x, dtriple (J x) m Q) : dtriple iprop(∃ x, J x) m Q := by
  intro F h hPre
  obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
  exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

theorem dtriple_conseq_frame {H₂ : IProp} {H₁ H : IPre} {Q₁ Q : IPost α}
    {m : Result α} (hTriple : dtriple H₁ m Q₁) (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) : dtriple H m Q :=
  dtriple_conseq (dtriple_frame hTriple H₂) hPre hPost

theorem dtriple_pure {P : IPre} {Q : IPost α} {value : α} (hPost : P ⊢ Q value) :
    dtriple P (pure value : Result α) Q := by
  intro F h hPre
  exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- Divergence satisfies every partial triple: nothing is claimed of a run that
does not stop, not even that it owns anything. -/
theorem dtriple_div {P : IPre} {Q : IPost α} :
    dtriple P (ITree.div : Result α) Q :=
  fun _ _ _ => PartialSpec.div

theorem dtriple_bind {P : IPre} {Q₁ : IPost α} {Q : IPost β} {m : Result α}
    {next : α → Result β} (hFirst : dtriple P m Q₁)
    (hNext : ∀ value, dtriple (Q₁ value) (next value) Q) :
    dtriple P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem dtriple_seq {P H : IPre} {Q : IPost β} {m₁ : Result α} {m₂ : Result β}
    (hFirst : dtriple P m₁ (fun _ => H)) (hSecond : dtriple H m₂ Q) :
    dtriple P (m₁ >>= fun _ => m₂) Q :=
  dtriple_bind hFirst (fun _ => hSecond)

/-! ## Ramified rules -/

/-- The ramified frame rule. The wand's conclusion is affine, so `Q` alone is
enough to permit leftover resources to be discarded. -/
theorem triple_ramified_frame {α : Type} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_conseq_frame hStep hPre (postWand_cancel Qm Q)

/-- The ramified frame rule for a call followed by a continuation. -/
theorem triple_ramified_bind {α β : Type} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_bind (triple_conseq (triple_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- Rewrite part of a triple's precondition using an entailment. -/
theorem triple_rewrite {α : Type} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
    (hPart : H₁ ⊢ H₂) (hRest : triple (H₂ ∗ H₃) m Q) : triple (H₁ ∗ H₃) m Q :=
  triple_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

theorem dtriple_ramified_frame {α : Type} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : dtriple Pm m Qm) (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dtriple P m Q :=
  dtriple_conseq_frame hStep hPre (postWand_cancel Qm Q)

theorem dtriple_ramified_bind {α β : Type} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α} (hStep : dtriple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dtriple (Qm value ∗ F) (next value) Q) :
    dtriple P (m >>= next) Q :=
  dtriple_bind
    (dtriple_conseq (dtriple_frame hStep F) hPre (fun _ => entails_refl _)) hNext

/-- Rewrite part of a partial triple's precondition using an entailment. -/
theorem dtriple_rewrite {α : Type} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
    (hPart : H₁ ⊢ H₂) (hRest : dtriple (H₂ ∗ H₃) m Q) : dtriple (H₁ ∗ H₃) m Q :=
  dtriple_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

/-! ## Reasoning about loops

The rules a partial triple is for: an invariant that the body re-establishes
proves the loop, with no measure and no termination argument. A recursion in
`Result` is proved with `dtriple_admissible` and the `fixpoint_induct` principle
`partial_fixpoint` attaches to it, and anything else by
`PartialSpec.coinduction` itself. -/

/-- A partial triple is admissible in the program, so it may be proved of a
`partial_fixpoint` by `Lean.Order.fix_induct`. -/
theorem dtriple_admissible {α : Type} (P : IPre) (Q : IPost α) :
    Lean.Order.admissible (fun m : Result α => dtriple P m Q) := by
  intro c hc hAll F h hPre
  exact dspec_admissible (Q ∗+ F) h c hc fun x hx => hAll x hx F h hPre

/-- The same for a family of triples about a recursive *function*, which is the
shape `fixpoint_induct` expects. -/
theorem dtriple_admissible_pi {ι α : Type} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible
      (fun f : ι → Result α => ∀ x, dtriple (P x) (f x) (Q x)) :=
  Lean.Order.admissible_pi_apply (fun x m => dtriple (P x) m (Q x))
    fun x => dtriple_admissible (P x) (Q x)

/-- And the same for a specification that quantifies over parameters of its own
— a ghost value, an old contents — which is the shape `fixpoint_induct` takes
when the argument of the recursion does not change. -/
theorem dtriple_admissible_forall {ι α : Type} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible (fun m : Result α => ∀ x, dtriple (P x) m (Q x)) :=
  Lean.Order.admissible_pi _ fun x => dtriple_admissible (P x) (Q x)

/-! ## Wiring of `step` to separation-logic triples

Both judgments are registered, back to back, and `dtriple` declares `triple` as
a lifting so that the `@[step]` specifications — which state total correctness —
apply to a partial goal as they stand, exactly as `Aeneas.Std.WP.dspec`
registers `Std.WP.spec_dspec`. -/

end ResultImplementation

open Lean Elab Meta Tactic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation. -/
theorem triple_step_bind {α β : Type} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β}
    (m : Result α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_ramified_bind hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call. -/
theorem triple_step_mono {α : Type} {P Pm : IPre} {Q : IPost α}
    (m : Result α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-- Bind rule used by `step` on a partial goal. -/
theorem dtriple_step_bind {α β : Type} {P Pm F : IPre} {next : α → Result β}
    {Q : IPost β} (m : Result α) (Qm : IPost α) (hStep : dtriple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dtriple (Qm value ∗ F) (next value) Q) :
    dtriple P (m >>= next) Q :=
  dtriple_ramified_bind hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call on a partial goal. -/
theorem dtriple_step_mono {α : Type} {P Pm : IPre} {Q : IPost α} (m : Result α)
    (Qm : IPost α) (hStep : dtriple Pm m Qm) (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dtriple P m Q :=
  dtriple_ramified_frame hStep hRamified

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- The tactic `step` runs on the goals it prepares. A no-op on a goal which is
not a triple. -/
macro "intro_triple" : tactic =>
  `(tactic| (isimp; iintro_shallow))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 7
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``forall_unit, ``true_imp_iff
    ]
    intro_tactic := SpecInfo.tac `(tactic| intro_triple)
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[]
  }

#register_spec_info {
    spec_name := ``dtriple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``dtriple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``dtriple_step_bind
    mk_spec_bind_skip_args := 7
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``forall_unit, ``true_imp_iff
    ]
    intro_tactic := SpecInfo.tac `(tactic| intro_triple)
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[
      { from_statement := ``triple
        conversion_thm := ``triple_dtriple
        conversion_thm_inferred_args := 4 }
    ]
  }

/-! ## Weakest-precondition tactics -/

/-- Reduce a triple about a terminal `pure v` to the entailment `P ⊢ Q v`. -/
macro "wp_pures" : tactic => `(tactic| apply triple_pure)

/-- Apply a specification to the goal, frame the resources it does not need,
and discharge the resulting entailment with `isimpl`. -/
syntax "wp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| wp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine triple_ramified_frame $thm ?_)
      | none => `(tactic| refine triple_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state an already-proved triple under a weaker postcondition. -/
macro "wp_mono " thm:term : tactic =>
  `(tactic| (apply triple_conseq $thm (entails_refl _) <;> (intro _ <;> iframe)))

/-- Reduce a partial triple about a terminal `pure v` to the entailment
`P ⊢ Q v`. -/
macro "dwp_pures" : tactic => `(tactic| apply dtriple_pure)

/-- Apply a partial specification to the goal, frame the resources it does not
need, and discharge the resulting entailment with `isimpl`. -/
syntax "dwp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| dwp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine dtriple_ramified_frame $thm ?_)
      | none => `(tactic| refine dtriple_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state an already-proved partial triple under a weaker postcondition. -/
macro "dwp_mono " thm:term : tactic =>
  `(tactic| (apply dtriple_conseq $thm (entails_refl _) <;> (intro _ <;> iframe)))

@[step]
theorem ret.spec (value : α) :
    ⦃ emp ⦄ Result.ok value ⦃⇓ result => ⌜result = value⌝⦄ :=
  triple_pure fun _ _ => rfl

@[step]
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : Result α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ret.spec value

end Aeneas.SepLogic
