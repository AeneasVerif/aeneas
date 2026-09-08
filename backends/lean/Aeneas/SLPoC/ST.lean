import Aeneas.Std.Delab
import Aeneas.Data.Coinductive.Spec
import Aeneas.Std.Primitives
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
# The program logic of the state monad `Result`

`Aeneas.Std.Primitives` defines `Result`, the interaction-tree monad over heap
events. This file builds its correctness judgments, derives the
separation-logic triples, wires those triples to the `step`/`step*` tactics,
and declares the `⦃ value => p ⦄` notation for pure computations — which is
notation for the triple that owns nothing, not a judgment of its own.

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

universe u v

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

/- The `⇓` is inside `atomic` so that the parser backtracks when it is absent:
`(m) ⦃ value => p ⦄`, the pure-computation notation of `Aeneas.SepLogic.WP`,
starts with exactly the same tokens and must stay parseable. -/
syntax:lead (name := specSyntax)
  atomic("(" term:lead ")" " ⦃" "⇓ ") Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := specSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄" : term
syntax:lead (name := slSpecSyntax)
  "⦃ " term " ⦄" ppSpace term:lead ppSpace
  "⦃" "⇓" ppSpace Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := slSpecSyntaxPred)
  "⦃ " term " ⦄" ppSpace term:lead ppSpace "⦃" "⇓" ppSpace term " ⦄" : term

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
  atomic("(" term:lead ")" " ⦃" "⇓ ") Lean.Parser.Term.funBinder " => " term " ⦄div" : term
syntax:lead (name := dspecSyntaxPred)
  atomic("(" term:lead ")" " ⦃" "⇓ ") term " ⦄div" : term
syntax:lead (name := slDspecSyntax)
  "⦃ " term " ⦄" ppSpace term:lead ppSpace
  "⦃" "⇓" ppSpace Lean.Parser.Term.funBinder " => " term " ⦄div" : term
syntax:lead (name := slDspecSyntaxPred)
  "⦃ " term " ⦄" ppSpace term:lead ppSpace "⦃" "⇓" ppSpace term " ⦄div" : term

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
theorem triple_dtriple {α : Type u} {P : IPre} {m : Result α} {Q : IPost α}
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

/-- A triple with a pure precondition and postcondition is a pure implication
whose conclusion owns nothing. -/
theorem triple_ipure_iff {P : Prop} {m : Result α} {Q : α → Prop} :
    triple ⌜P⌝ m (fun value => ⌜Q value⌝) ↔
      (P → triple emp m (fun value => ⌜Q value⌝)) := by
  constructor
  · intro hTriple hP
    exact triple_conseq hTriple ((entails_emp_ipure_iff P).2 hP)
      (fun _ => entails_refl _)
  · exact triple_ipure'

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

theorem triple_bind {α β : Type u} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

/-- `triple_bind` on `Aeneas.Std.bind` rather than on `>>=`.

The `Bind` class puts the two value types in the *same* universe, which a call
in a translated Rust program need not: a function returning a `Type u` may be
followed by a continuation returning a `Type v`.  `Aeneas.Std.bind` is the
two-universe bind `Result` is really given, so the rule `step` uses is this one.
-/
theorem triple_bind' {α : Type u} {β : Type v} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (Aeneas.Std.bind m next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem triple_seq {α β : Type u} {P H : IPre} {Q : IPost β}
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

/-- A partial triple with a pure precondition and postcondition is a pure
implication whose conclusion owns nothing. -/
theorem dtriple_ipure_iff {P : Prop} {m : Result α} {Q : α → Prop} :
    dtriple ⌜P⌝ m (fun value => ⌜Q value⌝) ↔
      (P → dtriple emp m (fun value => ⌜Q value⌝)) := by
  constructor
  · intro hTriple hP
    exact dtriple_conseq hTriple ((entails_emp_ipure_iff P).2 hP)
      (fun _ => entails_refl _)
  · exact dtriple_ipure'

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

theorem dtriple_bind {α β : Type u} {P : IPre} {Q₁ : IPost α} {Q : IPost β} {m : Result α}
    {next : α → Result β} (hFirst : dtriple P m Q₁)
    (hNext : ∀ value, dtriple (Q₁ value) (next value) Q) :
    dtriple P (m >>= next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

/-- `dtriple_bind` on `Aeneas.Std.bind`, the two-universe bind.  See
`triple_bind'`. -/
theorem dtriple_bind' {α : Type u} {β : Type v} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Result α} {next : α → Result β} (hFirst : dtriple P m Q₁)
    (hNext : ∀ value, dtriple (Q₁ value) (next value) Q) :
    dtriple P (Aeneas.Std.bind m next) Q := by
  intro F h hPre
  apply (hFirst F h hPre).bind
  intro value h' hPost
  exact hNext value F h' hPost

theorem dtriple_seq {α β : Type u} {P H : IPre} {Q : IPost β} {m₁ : Result α} {m₂ : Result β}
    (hFirst : dtriple P m₁ (fun _ => H)) (hSecond : dtriple H m₂ Q) :
    dtriple P (m₁ >>= fun _ => m₂) Q :=
  dtriple_bind hFirst (fun _ => hSecond)

/-! ## Ramified rules -/

/-- The ramified frame rule. The wand's conclusion is affine, so `Q` alone is
enough to permit leftover resources to be discarded. -/
theorem triple_ramified_frame {α : Type u} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_conseq_frame hStep hPre (postWand_cancel Qm Q)

/-- The ramified frame rule for a call followed by a continuation. -/
theorem triple_ramified_bind {α β : Type u} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_bind (triple_conseq (triple_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- The ramified frame rule for a call followed by a continuation, on the
two-universe `Aeneas.Std.bind`.  See `triple_bind'`. -/
theorem triple_ramified_bind' {α : Type u} {β : Type v} {P Pm F : IPre}
    {Qm : IPost α} {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (Aeneas.Std.bind m next) Q :=
  triple_bind' (triple_conseq (triple_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- Rewrite part of a triple's precondition using an entailment. -/
theorem triple_rewrite {α : Type u} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
    (hPart : H₁ ⊢ H₂) (hRest : triple (H₂ ∗ H₃) m Q) : triple (H₁ ∗ H₃) m Q :=
  triple_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

theorem dtriple_ramified_frame {α : Type u} {P Pm : IPre} {Q Qm : IPost α}
    {m : Result α} (hStep : dtriple Pm m Qm) (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dtriple P m Q :=
  dtriple_conseq_frame hStep hPre (postWand_cancel Qm Q)

theorem dtriple_ramified_bind {α β : Type u} {P Pm F : IPre} {Qm : IPost α}
    {next : α → Result β} {Q : IPost β} {m : Result α} (hStep : dtriple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dtriple (Qm value ∗ F) (next value) Q) :
    dtriple P (m >>= next) Q :=
  dtriple_bind
    (dtriple_conseq (dtriple_frame hStep F) hPre (fun _ => entails_refl _)) hNext

/-- The ramified bind rule on the two-universe `Aeneas.Std.bind`, for a partial
goal.  See `triple_bind'`. -/
theorem dtriple_ramified_bind' {α : Type u} {β : Type v} {P Pm F : IPre}
    {Qm : IPost α} {next : α → Result β} {Q : IPost β} {m : Result α}
    (hStep : dtriple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, dtriple (Qm value ∗ F) (next value) Q) :
    dtriple P (Aeneas.Std.bind m next) Q :=
  dtriple_bind'
    (dtriple_conseq (dtriple_frame hStep F) hPre (fun _ => entails_refl _)) hNext

/-- Rewrite part of a partial triple's precondition using an entailment. -/
theorem dtriple_rewrite {α : Type u} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : Result α}
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
theorem dtriple_admissible {α : Type u} (P : IPre) (Q : IPost α) :
    Lean.Order.admissible (fun m : Result α => dtriple P m Q) := by
  intro c hc hAll F h hPre
  exact dspec_admissible (Q ∗+ F) h c hc fun x hx => hAll x hx F h hPre

/-- The same for a family of triples about a recursive *function*, which is the
shape `fixpoint_induct` expects. -/
theorem dtriple_admissible_pi {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible
      (fun f : ι → Result α => ∀ x, dtriple (P x) (f x) (Q x)) :=
  Lean.Order.admissible_pi_apply (fun x m => dtriple (P x) m (Q x))
    fun x => dtriple_admissible (P x) (Q x)

/-- And the same for a specification that quantifies over parameters of its own
— a ghost value, an old contents — which is the shape `fixpoint_induct` takes
when the argument of the recursion does not change. -/
theorem dtriple_admissible_forall {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible (fun m : Result α => ∀ x, dtriple (P x) m (Q x)) :=
  Lean.Order.admissible_pi _ fun x => dtriple_admissible (P x) (Q x)


/-! ### Bridging lemmas for the pure judgments

`Aeneas.SepLogic.WP` states the pure judgments below, *outside* this section.
It has to be outside: `Result.ok` and `Result.div` are `[local reducible]` here,
so a `@[simp]` lemma stated in this section would be indexed under `ITree.ret`
rather than under `Result.ok`, and would never fire at a call site.  These are
the three facts whose proofs do need that reducibility, exported so that the
pure lemmas can be stated where they are indexed correctly. -/

theorem triple_ok_apply {α : Type u} {Q : IPost α} {x : α}
    (hTriple : triple emp (Result.ok x) Q) : Q x ∅ :=
  (triple_apply hTriple (h := ∅) trivial).ret_post

theorem triple_ok_intro {α : Type u} {Q : IPost α} {x : α} (hQ : ∀ h, Q x h) :
    triple emp (Result.ok x) Q :=
  triple_pure fun h _ => hQ h

theorem dtriple_ok_apply {α : Type u} {Q : IPost α} {x : α}
    (hTriple : dtriple emp (Result.ok x) Q) : Q x ∅ :=
  (dtriple_apply hTriple (h := ∅) trivial).ret_post

theorem dtriple_ok_intro {α : Type u} {Q : IPost α} {x : α} (hQ : ∀ h, Q x h) :
    dtriple emp (Result.ok x) Q :=
  dtriple_pure fun h _ => hQ h

theorem triple_div_elim {α : Type u} {Q : IPost α}
    (hTriple : triple emp (Result.div : Result α) Q) : False :=
  (triple_apply hTriple (h := ∅) trivial).div_false

theorem dtriple_div_intro {α : Type u} {P : IPre} {Q : IPost α} :
    dtriple P (Result.div : Result α) Q :=
  dtriple_div

/-! ### What a pure specification does not determine

`Aeneas.Std.WP.spec m p` is *equivalent* to `∃ value, m = .ok value ∧ p value`,
because the machine it is taken at answers no event at all.  The triple at `emp`
is weaker, and has to be: `emp` owns nothing, but an event that *needs* nothing
is still permitted, and such an event returns no value.

The equivalence comes back as soon as the program is known to perform no heap
event — which is exactly what a translated *pure* Rust function is.  Failure is
not a heap event and is ruled out by the triple itself, so it is allowed here. -/

/-- `m` performs no heap event.  Failure is not excluded: it is an event the
machine cannot answer, so a triple rules it out by itself. -/
def HeapFree {α : Type} (m : Result α) : Prop :=
  ∀ (EventResult : Type) (pre : Heap → Prop) modify k,
    m ≠ Result.vis (.guardedModify EventResult pre modify) k

/-- A return performs no heap event. -/
theorem HeapFree.ok {α : Type} (value : α) : HeapFree (Result.ok value) := by
  intro _ _ _ _ hEq
  simp [Result.ok, Result.vis] at hEq

/-- Neither does a failure: failure is the event the machine cannot answer, and
a triple rules it out on its own. -/
theorem HeapFree.fail {α : Type} (error : Error) :
    HeapFree (Result.fail error : Result α) := by
  intro _ _ _ _ hEq
  exact absurd (Aeneas.Data.Coinductive.vis_inj_effect hEq) (by simp)

/-- Nor does divergence. -/
theorem HeapFree.div {α : Type} : HeapFree (Result.div : Result α) := by
  intro _ _ _ _ hEq
  simp [Result.div, Result.vis] at hEq

/-- The counterpart of `Aeneas.Std.WP.spec_imp_exists`: a total triple owning
nothing determines an event-free program, and hands its postcondition back at
the empty heap. -/
theorem triple_emp_eq_ok {α : Type} {m : Result α} {Q : IPost α}
    (hHeapFree : HeapFree m) (hTriple : triple emp m Q) :
    ∃ value, m = Result.ok value ∧ Q value ∅ := by
  have hSpec := triple_apply hTriple (h := ∅) trivial
  cases m with
  | ret value => exact ⟨value, rfl, hSpec.ret_post⟩
  | vis event k =>
      cases event with
      | guardedModify EventResult pre modify => exact absurd rfl (hHeapFree _ _ _ k)
      | fail error => exact hSpec.vis_view.elim
  | div => exact hSpec.div_false.elim

/-! ## Wiring of `step` to separation-logic triples

Both judgments are registered, back to back, and `dtriple` declares `triple` as
a lifting so that the `@[step]` specifications — which state total correctness —
apply to a partial goal as they stand.

These two entries are the *only* ones this file registers: the pure-computation
notation below is notation for these judgments, so `step` needs nothing extra
for it, and a pure specification needs no lifting to be used on a heap goal. -/

end ResultImplementation

/-! ## Pure computations

A great many Rust functions touch no heap at all: a scalar addition, an
arithmetic overflow check, a lookup in a `Vec` whose contents are carried by the
value rather than by the heap.  Their specifications want to say only what the
call *returns*, on a postcondition `α → Prop`, with no assertion, no frame and
no points-to in sight.

That is not a second program logic, and — unlike `Aeneas.Std.WP.spec` — it is
not a second *judgment* either.  It is **notation**:

```
m ⦃ value => p value ⦄     is     triple  emp m (fun value => ⌜p value⌝)
m ⦃ value => p value ⦄div  is     dtriple emp m (fun value => ⌜p value⌝)
```

There is no `spec` constant to unfold, no bridging lemma to apply, and nothing
to register with `step` a second time.  A pure specification *is* a triple, so:

* everything the triples prove applies to it — the bind rule of a pure
  specification is `triple_bind`, its rule of consequence is `triple_conseq`,
  and its admissibility is `dtriple_admissible`;
* `step` uses a pure specification inside a proof about a heap-manipulating
  program by its ordinary framing, with no lifting registered and none needed;
* conversely a function whose *implementation* allocates, mutates and frees may
  be given a *pure* specification, because owning nothing is a claim about the
  specification and not about the implementation.  Under a separate pure
  judgment that statement is not merely unprovable but false, since such a
  judgment is taken at a machine that answers no event;
* a higher-order combinator states its callee's contract once, as a
  precondition/postcondition pair, instead of once per judgment, and the pure
  case is that contract at `emp`.

The syntax is declared at the end of this file, after the triples are wired to
`step`.  What it costs is `triple_emp_eq_ok` above: a pure-shaped triple no
longer determines the program on its own.  `Aeneas.SLPoC.Tests.PureSpec`
exercises all of this. -/

open Lean Elab Meta Tactic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation.

It is stated on `Aeneas.Std.bind` rather than on `>>=`: the `Bind` class forces
the two value types into one universe, and a call in a translated program need
not respect that. -/
theorem triple_step_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β}
    (m : Result α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (Aeneas.Std.bind m next) Q :=
  triple_ramified_bind' hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call. -/
theorem triple_step_mono {α : Type u} {P Pm : IPre} {Q : IPost α}
    (m : Result α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-- Bind rule used by `step` on a partial goal.  See `triple_step_bind`. -/
theorem dtriple_step_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β}
    {Q : IPost β} (m : Result α) (Qm : IPost α) (hStep : dtriple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F) (hNext : ∀ value, dtriple (Qm value ∗ F) (next value) Q) :
    dtriple P (Aeneas.Std.bind m next) Q :=
  dtriple_ramified_bind' hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call on a partial goal. -/
theorem dtriple_step_mono {α : Type u} {P Pm : IPre} {Q : IPost α} (m : Result α)
    (Qm : IPost α) (hStep : dtriple Pm m Qm) (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    dtriple P m Q :=
  dtriple_ramified_frame hStep hRamified

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- Internal tuple destructuring marker for pure postconditions.

Unlike a pattern lambda, this survives elaboration in a form the delaborator
can recognize.  Its simp lemmas make it transparent to `step`. -/
@[inline] def purePostUncurry {α β γ : Type _} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

@[simp]
theorem purePostUncurry_apply {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    purePostUncurry f p = f p.1 p.2 := by
  cases p
  rfl

@[simp]
theorem purePostUncurry_eq {α β γ : Type _} (f : α → β → γ) :
    purePostUncurry f = fun p => f p.1 p.2 := by
  funext p
  exact purePostUncurry_apply f p

/-- Internal marker for a boundary between separate pure-postcondition binders.

It has the same semantics as `purePostUncurry`, but the delaborator prints it
as `x y => ...` rather than `(x, y) => ...`. -/
@[inline] def purePostCurry {α β γ : Type _} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

@[simp]
theorem purePostCurry_apply {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    purePostCurry f p = f p.1 p.2 := by
  cases p
  rfl

@[simp]
theorem purePostCurry_eq {α β γ : Type _} (f : α → β → γ) :
    purePostCurry f = fun p => f p.1 p.2 := by
  funext p
  exact purePostCurry_apply f p

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
      ``triple_ipure_iff,
      ``forall_unit,
      ``purePostCurry_apply, ``purePostCurry_eq,
      ``purePostUncurry_apply, ``purePostUncurry_eq,
      ``sep_emp_l_eq, ``sep_ipure_true_l_eq,
      ``entails_emp_postWand_ipure_iff,
      ``entails_emp_ipure_iff, ``entails_refl, ``true_imp_iff
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
      ``dtriple_ipure_iff,
      ``forall_unit,
      ``purePostCurry_apply, ``purePostCurry_eq,
      ``purePostUncurry_apply, ``purePostUncurry_eq,
      ``sep_emp_l_eq, ``sep_ipure_true_l_eq,
      ``entails_emp_postWand_ipure_iff,
      ``entails_emp_ipure_iff, ``entails_refl, ``true_imp_iff
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

/-!
# Hoare triple notation for pure computations

`⦃ ⦄` writes a pure specification the way a Rust programmer reads a return
value: `f x ⦃ y => y > 0 ⦄` is the triple that owns nothing,
`triple emp (f x) (fun y => ⌜y > 0⌝)`, and several binders destructure a
returned tuple, so `f x ⦃ y z => ... ⦄` names the two components of a pair
without a pattern match of its own.

This is *notation*, not a definition.  It is the same surface, and the same
expansion, as the separation-logic notation of the triples above, read at `emp`
with a pure postcondition:

```
m ⦃ x => p ⦄      is      ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄
m ⦃ x => p ⦄div   is      ⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄div
```

so the two forms are not merely equivalent, they are the same proposition, and
`step` is driven by the `triple`/`dtriple` registrations alone.

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

open Lean PrettyPrinter

/-- Build a `purePostUncurry` chain for the leaves of a tuple pattern. -/
private partial def buildPureUncurryLam (xs : List Term) (body : Term) :
    MacroM Term := do
  let uncurryIdent := mkIdent ``purePostUncurry
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildPureUncurryLam rest body
    `($uncurryIdent (fun $a => $inner))

/-- Elaborate one possibly nested tuple binder without generating a matcher
function, so the delaborator can recover the pattern from `purePostUncurry`. -/
private partial def mkPureBinderFun (depth : Nat) (binder : Term) (body : Term) :
    MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkPureBinderFun (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildPureUncurryLam leafIdents wrappedBody
  | _ => `(fun $binder => $body)

/-- Preserve the boundary between separate binders with `purePostCurry`, while
using `purePostUncurry` inside each explicit tuple binder. -/
private partial def mkPurePostSyntax (body : Term) (depth : Nat)
    (binders : List Term) : MacroM Term := do
  match binders with
  | [] => pure body
  | [x] => mkPureBinderFun depth x body
  | x :: rest =>
    let rest ← mkPurePostSyntax body (depth + 1) rest
    let inner ← mkPureBinderFun depth x rest
    `(purePostCurry $inner)

/-- The `IPost` a pure postcondition denotes.  Transparent marker functions
record whether each product came from separate binders or an explicit tuple
pattern, allowing the delaborator to reproduce the original surface syntax. -/
private def mkPurePost (binders : Array Term) (p : Term) : MacroM Term := do
  let body ← `(⌜$p⌝)
  mkPurePostSyntax body 0 binders.toList

/-- Macro expansion for a single binder. -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x => $p ⦄) => do
    let post ← mkPurePost #[x] p
    `(triple emp $m $post)

/-- Macro expansion for several binders. -/
scoped macro_rules (kind := pureSpecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(triple emp $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x => $p ⦄div) => do
    let post ← mkPurePost #[x] p
    `(dtriple emp $m $post)

scoped macro_rules (kind := pureDspecBinders)
  | `($m ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPurePost (#[x] ++ xs) p
    `(dtriple emp $m $post)

/-- Macro expansion for a postcondition given as a predicate. -/
scoped macro_rules (kind := pureSpecPred)
  | `($m ⦃ $p ⦄) => `(triple emp $m (fun value => ⌜$p value⌝))

scoped macro_rules (kind := pureDspecPred)
  | `($m ⦃ $p ⦄div) => `(dtriple emp $m (fun value => ⌜$p value⌝))

/-!
# Pretty-printing

`triple`/`dtriple` have no delaborator of their own, so a goal of the pure shape
— precondition `emp`, postcondition `fun x => ⌜...⌝`, which is exactly what the
macros above produce — is printed back in the pure notation.  Anything else
falls through to the ordinary application printer, so a separating triple still
prints as one.
-/

open Delaborator SubExpr
open Std.Delab
  (enterLams delabBindersWith buildTupleTerm delabUncurryAsTupleWith)

/-- Delaborate the `⌜body⌝` at the end of a pure postcondition. -/
private def delabPureBody : DelabM Term := do
  guard ((← getExpr).isAppOfArity ``ipure 1)
  withAppArg delab

/-- Enter one explicit tuple binder without consuming continuation lambdas. -/
private partial def enterPureUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``purePostUncurry 4 then
        withAppArg <| enterPureUncurryOnce acc' k
      else
        enterPureUncurryOnce acc' k
  | _ => k acc

private def isPurePostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | purePostCurry _ _ _ _ => true
  | purePostUncurry _ _ _ _ => true
  | _ => false

/-- Recover separate binders, explicit tuple binders, and the final pure body
from the transparent marker chain produced by `mkPurePost`. -/
private partial def delabPurePost : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | purePostCurry _ _ _ _ =>
    withAppArg do
      match_expr (← getExpr).consumeMData with
      | purePostUncurry _ _ _ _ =>
        withAppArg <| enterPureUncurryOnce #[] fun tupleBinders => do
          let (patterns, (moreBinders, body)) ←
            delabBindersWith ``purePostUncurry tupleBinders.toList delabPurePost
          return (#[← buildTupleTerm patterns] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | purePostUncurry _ _ _ _ =>
    withAppArg do
      let (tupleBinder, body) ←
        delabUncurryAsTupleWith ``purePostUncurry delabPureBody
      return (#[tupleBinder], body)
  | _ => delabLamsThenRecurse
where
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    let e := (← getExpr).consumeMData
    if let .lam _ _ body _ := e then
      if !body.consumeMData.isLambda && !isPurePostBinderWrapper body then
        withBindingBodyUnusedName fun binder =>
          return (#[⟨binder⟩], ← delabPureBody)
      else
        enterLams #[] fun binders => do
          if binders.size == 1 && isPurePostBinderWrapper (← getExpr) then
            let (patterns, (moreBinders, body)) ←
              delabBindersWith ``purePostUncurry binders.toList delabPurePost
            return (patterns ++ moreBinders, body)
          else
            delabBindersWith ``purePostUncurry binders.toList delabPureBody
    else
      return (#[], ← delabPureBody)

/-- Print an arbitrary separation-logic postcondition using binder syntax when
it is a lambda and predicate syntax otherwise. -/
private def delabSLTriplePost (pre monadExpr : Term) (isPartial : Bool) :
    DelabM Term := do
  if (← getExpr).consumeMData.isLambda then
    withBindingBodyUnusedName fun binder => do
      let binder : Term := ⟨binder⟩
      let body ← delab
      if isPartial then
        `(⦃$pre⦄ $monadExpr ⦃⇓ $binder => $body⦄div)
      else
        `(⦃$pre⦄ $monadExpr ⦃⇓ $binder => $body⦄)
  else
    let post ← delab
    if isPartial then
      `(⦃$pre⦄ $monadExpr ⦃⇓ $post⦄div)
    else
      `(⦃$pre⦄ $monadExpr ⦃⇓ $post⦄)

/-- Print an arbitrary triple using the general separation-logic notation. -/
private def delabSLTripleCore (tripleName : Name) (isPartial : Bool) : Delab := do
  guard ((← getExpr).isAppOfArity tripleName 4)
  let monadExpr ← withNaryArg 2 delab
  let pre ← withNaryArg 1 delab
  withNaryArg 3 <| delabSLTriplePost pre monadExpr isPartial

/-- Print a pure triple using pure notation. This delaborator fails on general
separation-logic triples, allowing the global SL delaborator to handle them. -/
private def delabPureTripleCore (tripleName : Name) (isPartial : Bool) : Delab := do
  guard ((← getExpr).isAppOfArity tripleName 4)
  guard (← withNaryArg 1 do
    return (← getExpr).isConstOf ``Aeneas.SepLogic.«emp»)
  let monadExpr ← withNaryArg 2 delab
  let (binders, body) ← withNaryArg 3 delabPurePost
  guard (binders.size > 0)
  if isPartial then
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $body ⦄div)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $body ⦄)

/-- Global fallback delaborator for total separation-logic triples. -/
@[app_delab Aeneas.SepLogic.triple]
def delabSLTriple : Delab :=
  delabSLTripleCore ``Aeneas.SepLogic.triple false

/-- Global fallback delaborator for partial separation-logic triples. -/
@[app_delab Aeneas.SepLogic.dtriple]
def delabSLDtriple : Delab :=
  delabSLTripleCore ``Aeneas.SepLogic.dtriple true

/-- Scoped pure-notation delaborator for total triples. -/
@[scoped delab app.Aeneas.SepLogic.triple]
def delabPureTriple : Delab :=
  delabPureTripleCore ``Aeneas.SepLogic.triple false

/-- Scoped pure-notation delaborator for partial triples. -/
@[scoped delab app.Aeneas.SepLogic.dtriple]
def delabPureDtriple : Delab :=
  delabPureTripleCore ``Aeneas.SepLogic.dtriple true

end WP

end Aeneas.SepLogic
