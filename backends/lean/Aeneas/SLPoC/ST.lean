import Aeneas.Data.Coinductive.StateMachine
import Aeneas.Std.Primitives
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
# The program logic of the state monad `Result`

`Aeneas.Std.Primitives` defines `Result`, the interaction-tree monad over heap
events. This file builds its correctness judgments, derives the
separation-logic triples, and wires those triples to the `step`/`step*` tactics.
All of it is denotational: the operational semantics `Result` is adequate for,
and the certified interpreter that runs a proved program, are in
`Aeneas.SLPoC.Semantics`.
-/

namespace Aeneas.SepLogic

open Aeneas.Data.Coinductive
open Aeneas.Std (Error Heap Result RustEffect)

universe u

section ResultImplementation

unseal Result
set_option allowUnsafeReducibility true in
attribute [local reducible] Result Result.ok Result.vis Result.div Aeneas.Std.bind

/-! ## Total and partial correctness

`Result` carries two correctness judgments, laid out here the way `Aeneas.Std.WP`
lays out `spec` and `dspec`.

`TotalSpec`, exposed as `spec`, is *total* correctness. As for `Aeneas.Std.WP.spec`
a proof is a finite derivation ending in `ret`; nothing proves `ITree.div`
correct, so a program that does not terminate has no proof at all.

`PartialSpec`, exposed as `dspec`, is the divergence-tolerant counterpart. It
says what `spec` says of a run that *stops* and nothing about a run that does
not, while still requiring every event the program reaches to be defined:
divergence is permitted, being stuck is not.

`Aeneas.Std.WP.dspec` is `spec` plus one constructor for `Result.div`, and that
suffices there because the only event of `Result` is `fail`, which has no
continuation: a computation that neither returns nor fails *is* `div`, in one
step. A program of `Result` may perform arbitrarily many heap events before
returning or failing, so an infinite run is an infinite `vis` tree and no
inductive judgment accepts it: partial correctness has to be a **greatest**
fixed point.

Both judgments are therefore fixed points of the *same* one-layer condition
`SpecF`, whose event case is `EventSpec`: what a heap event demands of the run
that follows it is not a property of either judgment, so it is written down
exactly once.  They differ only in what divergence owes — nothing for
`PartialSpec` (`SpecF Q True`), the impossible for `TotalSpec` (`SpecF Q False`)
— and in which fixed point is taken.  Neither is
an inductive: `TotalSpec` is the least fixed point written impredicatively as
the intersection of the pre-fixed points, exactly as `Exec` of
`Aeneas.Data.Coinductive.StateMachine` is, and `PartialSpec` is the greatest,
written as the union of the post-fixed points.

So both have to be given what an inductive definition offers for free.
`TotalSpec.induction` is the recursor and `PartialSpec.coinduction` the
introduction rule the loop invariant is applied to; `.ret` and `.vis` are the
constructors, `.ret_post`, `.div_false`/`.div` and `.vis_view` the destructors;
and each is read off one half of the fixed-point equation — `.intro` and
`.step`, which both judgments have.  `.vis_view` lands in `EventSpec`, which is
the `∃` guard of a heap event and `False` at `fail`, so it is also where
`.fail_vis_false` comes from. -/

/-- What performing `event` on the heap `h` demands, with the rest of the run
left to `X`: a heap event must be defined on the heap it is performed on, and
its continuation runs on the heap it produces; failure is rejected outright.

This is the single place the meaning of an event is written down. `SpecF` is
`ITree.cases` with this in its `vis` case, `SpecF.vis` is the equation that
exposes it, and both correctness judgments are fixed points of `SpecF`, so
nothing below has to say it again. -/
def EventSpec (X : Result α → Heap → Prop) :
    (event : RustEffect.I) → (RustEffect.O event → Result α) → Heap → Prop
  | RustEffect.I.guardedModify _ pre modify, k, h =>
      ∃ hPre : pre h, X (k (.up (modify h hPre).1)) (modify h hPre).2
  | RustEffect.I.fail _, _, _ => False

/-- What an event demands is monotone in the rest of the run: this is the only
proof that has to look at the two events. -/
theorem EventSpec.mono {X X' : Result α → Heap → Prop}
    (hX : ∀ m h, X m h → X' m h) {event : RustEffect.I}
    {k : RustEffect.O event → Result α} {h : Heap}
    (hEvent : EventSpec X event k h) : EventSpec X' event k h := by
  cases event with
  | guardedModify EventResult pre modify =>
      obtain ⟨hPre, hNext⟩ := hEvent
      exact ⟨hPre, hX _ _ hNext⟩
  | fail error => exact hEvent.elim

/-- One layer of a correctness judgment, with the rest of the run left to `X`
and divergence left to `Div`: a returned value satisfies the postcondition, a
divergent tree owes `Div`, and an event owes `EventSpec`.

`TotalSpec` is the least fixed point of `SpecF Q False` and `PartialSpec` the
greatest fixed point of `SpecF Q True`; the two differ only in `Div`. -/
def SpecF (Q : α → Heap → Prop) (Div : Prop) (X : Result α → Heap → Prop)
    (m : Result α) (h : Heap) : Prop :=
  ITree.cases
    (motive := fun _ => Prop)
    (fun value => Q value h)
    Div
    (fun event k => EventSpec X event k h)
    m

/-! The computation rules of `SpecF`, named after the `ITree.cases.*` they are
proved from.  Every proof below rewrites with these rather than unfolding
`SpecF` by hand. -/

theorem SpecF.ret {Q : α → Heap → Prop} {Div : Prop} {X : Result α → Heap → Prop}
    {value : α} {h : Heap} :
    SpecF Q Div X (.ret value) h = Q value h := by
  simp only [SpecF, ITree.cases.ret]

/-- `SpecF.ret` as the `ret` case of `ITree.cases` writes it. -/
theorem SpecF.pure {Q : α → Heap → Prop} {Div : Prop} {X : Result α → Heap → Prop}
    {value : α} {h : Heap} :
    SpecF Q Div X (Pure.pure value) h = Q value h := by
  simp only [SpecF, ITree.cases.pure]

theorem SpecF.div {Q : α → Heap → Prop} {Div : Prop} {X : Result α → Heap → Prop}
    {h : Heap} : SpecF Q Div X (ITree.div : Result α) h = Div := by
  simp only [SpecF, ITree.cases.div]

/-- The event case, which hands the obligation straight back to `EventSpec`;
`simp only [SpecF.vis, EventSpec]` is what reduces it for a concrete event. -/
theorem SpecF.vis {Q : α → Heap → Prop} {Div : Prop} {X : Result α → Heap → Prop}
    {event : RustEffect.I} {k : RustEffect.O event → Result α} {h : Heap} :
    SpecF Q Div X (.vis event k) h = EventSpec X event k h := by
  simp only [SpecF, ITree.cases.vis]

/-- The layer is monotone in everything: in the postcondition, in what
divergence owes, and in the rest of the run. -/
theorem SpecF.mono {Q Q' : α → Heap → Prop} {Div Div' : Prop}
    {X X' : Result α → Heap → Prop}
    (hQ : ∀ value h, Q value h → Q' value h) (hDiv : Div → Div')
    (hX : ∀ m h, X m h → X' m h) {m : Result α} {h : Heap}
    (hLayer : SpecF Q Div X m h) : SpecF Q' Div' X' m h := by
  revert hLayer
  cases m using ITree.cases with
  | ret value =>
      simp only [SpecF.pure]
      exact hQ value h
  | div =>
      simp only [SpecF.div]
      exact hDiv
  | vis event k =>
      simp only [SpecF.vis]
      exact EventSpec.mono hX

/-- The common case of `SpecF.mono`: only the rest of the run is weakened. -/
theorem SpecF.mono_tail {Q : α → Heap → Prop} {Div : Prop}
    {X X' : Result α → Heap → Prop} (hX : ∀ m h, X m h → X' m h)
    {m : Result α} {h : Heap} (hLayer : SpecF Q Div X m h) : SpecF Q Div X' m h :=
  hLayer.mono (fun _ _ => id) id hX

/-- Total correctness of `m` on the exact heap `h`: the **least** fixed point of
`SpecF Q False`, spelled out as the intersection of its pre-fixed points, the
way `Exec` of `Aeneas.Data.Coinductive.StateMachine` is.  A witness is a finite
derivation, and `False` in the divergence slot is what makes it finite: no
relation closed under the layer has to accept `ITree.div`, so a program that
does not terminate has no proof at all. -/
def TotalSpec (Q : α → Heap → Prop) (m : Result α) (h : Heap) : Prop :=
  ∀ X : Result α → Heap → Prop,
    (∀ m' h', SpecF Q False X m' h' → X m' h') → X m h

/-- Partial correctness of `m` on the exact heap `h`: the **greatest** fixed
point of `SpecF Q True`, spelled out as the union of its post-fixed points — the
exact dual of `TotalSpec`.  A witness is a *coinduction hypothesis* — a relation
between configurations that reproduces itself one event at a time — rather than
a finite derivation, so a program with no `ret` in sight may satisfy it. -/
def PartialSpec (Q : α → Heap → Prop) (m : Result α) (h : Heap) : Prop :=
  ∃ X : Result α → Heap → Prop,
    (∀ m' h', X m' h' → SpecF Q True X m' h') ∧ X m h

/-- Total correctness of `m` on the exact heap `h`. -/
abbrev spec (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  TotalSpec (fun value h' => Q value h') m h

/-- Partial correctness of `m` on the exact heap `h`, on assertions.  The
counterpart of `spec`, and named after `Aeneas.Std.WP.dspec`. -/
abbrev dspec (m : Result α) (Q : IPost α) (h : Heap) : Prop :=
  PartialSpec (fun value h' => Q value h') m h

/-! ### The constructors and destructors of `TotalSpec`

Neither judgment is an inductive, so both have to be given what an inductive
definition offers for free.  For `TotalSpec` that is `TotalSpec.induction` — the
recursor — together with the constructors `.ret` and `.vis` and the destructors
`.ret_post`, `.div_false` and `.vis_view`; all of them are read off the two
halves `TotalSpec.intro` and `TotalSpec.step` of the fixed-point equation. -/

/-- The induction principle of `TotalSpec`, and the elimination rule the
definition is: a property that holds of a returned value satisfying the
postcondition and survives one heap event holds of every configuration total
correctness holds of.

There is no obligation for `ITree.div` and none for failure — that is what the
`False` in `SpecF Q False` buys — so this is exactly the recursor an inductive
definition would have provided. -/
theorem TotalSpec.induction {Q : α → Heap → Prop} {P : Result α → Heap → Prop}
    (hRet : ∀ value h', Q value h' → P (.ret value) h')
    (hVis : ∀ {EventResult : Type} {pre : Heap → Prop}
      {modify : (h : Heap) → pre h → EventResult × Heap}
      {k : RustEffect.O (RustEffect.I.guardedModify EventResult pre modify) → Result α}
      (h' : Heap) (hPre : pre h'),
      P (k (.up (modify h' hPre).1)) (modify h' hPre).2 →
      P (.vis (RustEffect.I.guardedModify EventResult pre modify) k) h')
    {m : Result α} {h : Heap} (hSpec : TotalSpec Q m h) : P m h := by
  refine hSpec P fun m' h' hLayer => ?_
  revert hLayer
  cases m' using ITree.cases with
  | ret value =>
      simp only [SpecF.pure]
      exact hRet value h'
  | div =>
      simp only [SpecF.div]
      exact False.elim
  | vis event k =>
      cases event with
      | guardedModify EventResult pre modify =>
          simp only [SpecF.vis, EventSpec]
          rintro ⟨hPre, hP⟩
          exact hVis h' hPre hP
      | fail error =>
          simp only [SpecF.vis, EventSpec]
          exact False.elim

/-- Total correctness is a pre-fixed point: one layer of it is it.  This is the
two constructors at once, and the exact counterpart of `PartialSpec.intro`. -/
theorem TotalSpec.intro {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    (hLayer : SpecF Q False (TotalSpec Q) m h) : TotalSpec Q m h :=
  fun X hClosed => hClosed m h (hLayer.mono_tail fun _ _ hSpec => hSpec X hClosed)

/-- And it is a fixed point: it survives one event.  Every destructor below is
this rule read in one of the four cases of `SpecF`, and it is the counterpart of
`PartialSpec.step`. -/
theorem TotalSpec.step {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    (hSpec : TotalSpec Q m h) : SpecF Q False (TotalSpec Q) m h :=
  hSpec.induction
    (P := SpecF Q False (TotalSpec Q))
    (fun _ _ hPost => by simpa only [SpecF.ret] using hPost)
    fun _ hPre hLayer => by
      simpa only [SpecF.vis, EventSpec] using ⟨hPre, TotalSpec.intro hLayer⟩

theorem TotalSpec.ret {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hPost : Q value h) : TotalSpec Q (.ret value) h :=
  intro (by simpa only [SpecF.ret] using hPost)

theorem TotalSpec.pure {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hPost : Q value h) : TotalSpec Q (Pure.pure value) h :=
  ret hPost

theorem TotalSpec.vis {Q : α → Heap → Prop} {EventResult : Type}
    {pre : Heap → Prop} {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.O (RustEffect.I.guardedModify EventResult pre modify) → Result α}
    {h : Heap} (hPre : pre h)
    (hNext : TotalSpec Q
      (k (.up (modify h hPre).1)) (modify h hPre).2) :
    TotalSpec Q (.vis (RustEffect.I.guardedModify EventResult pre modify) k) h :=
  intro (by simpa only [SpecF.vis, EventSpec] using ⟨hPre, hNext⟩)

theorem TotalSpec.ret_post {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hSpec : TotalSpec Q (.ret value) h) : Q value h := by
  simpa only [SpecF.ret] using hSpec.step

/-- Divergence is never totally correct.  This is the case `PartialSpec`
deliberately keeps. -/
theorem TotalSpec.div_false {Q : α → Heap → Prop} {h : Heap}
    (hSpec : TotalSpec Q (.div : Result α) h) : False := by
  simpa only [SpecF.div] using hSpec.step

/-- The event destructor, in the shape `EventSpec` states it: a heap event is
defined here and total correctness continues on the heap it produces, while
failure gives `False`.  `TotalSpec.fail_vis_false` is this rule read at `fail`. -/
theorem TotalSpec.vis_view {Q : α → Heap → Prop} {event : RustEffect.I}
    {k : RustEffect.O event → Result α} {h : Heap}
    (hSpec : TotalSpec Q (.vis event k) h) : EventSpec (TotalSpec Q) event k h := by
  simpa only [SpecF.vis] using hSpec.step

theorem TotalSpec.fail_vis_false {Q : α → Heap → Prop} {error : Error}
    {k : RustEffect.O (RustEffect.I.fail error) → Result α} {h : Heap}
    (hSpec : TotalSpec Q (.vis (RustEffect.I.fail error) k) h) : False :=
  hSpec.vis_view

theorem TotalSpec.fail_false {Q : α → Heap → Prop} {error : Error}
    {h : Heap} (hSpec : TotalSpec Q (Result.fail error) h) : False :=
  hSpec.fail_vis_false

/-! ### The constructors and destructors of `PartialSpec`

The same for the greatest fixed point, where `PartialSpec.coinduction` takes the
place `TotalSpec.induction` has above, and what the two liftings below are
proved from. -/

/-- The introduction rule: a relation closed under one event proves partial
correctness of every configuration it holds of.  This is what a loop invariant
is applied to. -/
theorem PartialSpec.coinduction {Q : α → Heap → Prop} (X : Result α → Heap → Prop)
    (hClosed : ∀ m' h', X m' h' → SpecF Q True X m' h') {m : Result α} {h : Heap}
    (hX : X m h) : PartialSpec Q m h :=
  ⟨X, hClosed, hX⟩

/-- Partial correctness is a post-fixed point: it survives one event. -/
theorem PartialSpec.step {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    (hSpec : PartialSpec Q m h) : SpecF Q True (PartialSpec Q) m h := by
  obtain ⟨X, hClosed, hX⟩ := hSpec
  exact (hClosed m h hX).mono_tail fun m' h' hX' => ⟨X, hClosed, hX'⟩

/-- And it is a fixed point: one layer of it is it. -/
theorem PartialSpec.intro {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    (hLayer : SpecF Q True (PartialSpec Q) m h) : PartialSpec Q m h := by
  refine coinduction
    (fun m' h' => PartialSpec Q m' h' ∨ (m' = m ∧ h' = h)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro m' h' (hSpec | ⟨rfl, rfl⟩)
  · exact hSpec.step.mono_tail fun _ _ => Or.inl
  · exact hLayer.mono_tail fun _ _ => Or.inl

theorem PartialSpec.ret {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hPost : Q value h) : PartialSpec Q (.ret value) h :=
  intro (by simpa only [SpecF.ret] using hPost)

theorem PartialSpec.pure {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hPost : Q value h) : PartialSpec Q (Pure.pure value) h :=
  ret hPost

/-- Divergence owes nothing.  This is the constructor `TotalSpec` deliberately
does not have. -/
theorem PartialSpec.div {Q : α → Heap → Prop} {h : Heap} :
    PartialSpec Q (ITree.div : Result α) h :=
  intro (by simp only [SpecF.div])

theorem PartialSpec.vis {Q : α → Heap → Prop} {EventResult : Type}
    {pre : Heap → Prop} {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.O (RustEffect.I.guardedModify EventResult pre modify) → Result α}
    {h : Heap} (hPre : pre h)
    (hNext : PartialSpec Q
      (k (.up (modify h hPre).1)) (modify h hPre).2) :
    PartialSpec Q (.vis (RustEffect.I.guardedModify EventResult pre modify) k) h :=
  intro (by simpa only [SpecF.vis, EventSpec] using ⟨hPre, hNext⟩)

theorem PartialSpec.ret_post {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hSpec : PartialSpec Q (.ret value) h) : Q value h := by
  simpa only [SpecF.ret] using hSpec.step

/-- The event destructor; the counterpart of `TotalSpec.vis_view`, and
`PartialSpec.fail_vis_false` is again the same rule read at `fail`. -/
theorem PartialSpec.vis_view {Q : α → Heap → Prop} {event : RustEffect.I}
    {k : RustEffect.O event → Result α} {h : Heap}
    (hSpec : PartialSpec Q (.vis event k) h) :
    EventSpec (PartialSpec Q) event k h := by
  simpa only [SpecF.vis] using hSpec.step

theorem PartialSpec.fail_vis_false {Q : α → Heap → Prop} {error : Error}
    {k : RustEffect.O (RustEffect.I.fail error) → Result α} {h : Heap}
    (hSpec : PartialSpec Q (.vis (RustEffect.I.fail error) k) h) : False :=
  hSpec.vis_view

theorem PartialSpec.fail_false {Q : α → Heap → Prop} {error : Error}
    {h : Heap} (hSpec : PartialSpec Q (Result.fail error) h) : False :=
  hSpec.fail_vis_false

@[simp]
theorem dspec_ret (value : α) (Q : IPost α) (h : Heap) :
    dspec (ITree.ret value : Result α) Q h ↔ Q value h :=
  ⟨PartialSpec.ret_post, fun hPost => .ret hPost⟩

@[simp]
theorem dspec_pure (value : α) (Q : IPost α) (h : Heap) :
    dspec (Pure.pure value : Result α) Q h ↔ Q value h :=
  dspec_ret value Q h

/-- Divergence satisfies every partial specification — the exact converse of
`spec_div`. -/
@[simp]
theorem dspec_div (Q : IPost α) (h : Heap) : dspec (ITree.div : Result α) Q h :=
  PartialSpec.div

@[simp]
theorem dspec_fail (error : Error) (Q : IPost α) (h : Heap) :
    ¬ dspec (Result.fail error) Q h :=
  PartialSpec.fail_false

@[simp]
theorem dspec_fail_vis (error : Error)
    (k : RustEffect.O (RustEffect.I.fail error) → Result α)
    (Q : IPost α) (h : Heap) :
    ¬ dspec (.vis (RustEffect.I.fail error) k) Q h :=
  PartialSpec.fail_vis_false

/-- Total correctness is partial correctness: the counterpart of
`Aeneas.Std.WP.spec_dspec`, and what lets `step` use an `@[step]` triple inside
a partial-correctness proof. -/
theorem TotalSpec.toPartial {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    (hSpec : TotalSpec Q m h) : PartialSpec Q m h :=
  hSpec.induction (P := PartialSpec Q) (fun _ _ hPost => .ret hPost)
    fun _ hPre hSpec' => .vis hPre hSpec'

theorem spec_dspec {Q : IPost α} {m : Result α} {h : Heap} (hSpec : spec m Q h) :
    dspec m Q h :=
  hSpec.toPartial

open Lean.Order in
/-- Partial correctness is admissible: it holds of the limit of a chain of
programs as soon as it holds of every program in it.  This is what
`Lean.Order.fix_induct` — the induction principle `partial_fixpoint` attaches to
a recursive definition — needs, and it is the counterpart of
`Aeneas.Std.WP.dspec_admissible`. -/
theorem PartialSpec.admissible (Q : α → Heap → Prop) (h : Heap) :
    Lean.Order.admissible (fun m : Result α => PartialSpec Q m h) := by
  intro c hc hAll
  refine coinduction
    (fun t u => ∃ c' : Result α → Prop, ∃ hc' : chain c',
      (∀ x, c' x → PartialSpec Q x u) ∧ t = CCPO.csup hc')
    ?_ ⟨c, hc, hAll, rfl⟩
  rintro t u ⟨c', hc', hAll', rfl⟩
  generalize hEq : CCPO.csup hc' = t
  cases t using ITree.cases with
  | ret value =>
      simp only [SpecF.pure]
      exact (hAll' _ (ITree.csup_ret_mem hc' hEq)).ret_post
  | div => simp only [SpecF.div]
  | vis event k =>
      cases event with
      | guardedModify EventResult pre modify =>
          simp only [SpecF.vis, EventSpec]
          obtain ⟨k', hMem⟩ := ITree.csup_vis_mem hc' hEq
          obtain ⟨hPre, -⟩ := (hAll' _ hMem).vis_view
          refine ⟨hPre,
            ITree.visChain c' (RustEffect.I.guardedModify EventResult pre modify)
              (.up (modify u hPre).1),
            ITree.visChain_chain hc' (RustEffect.I.guardedModify EventResult pre modify) _, ?_, ?_⟩
          · rintro _ ⟨k'', hMem'', rfl⟩
            exact (hAll' _ hMem'').vis_view.choose_spec
          · rw [ITree.csup_vis hc' hMem] at hEq
            obtain ⟨-, hHEq⟩ := vis_inj hEq
            obtain rfl := eq_of_heq hHEq
            rfl
      | fail error =>
          simp only [SpecF.vis, EventSpec]
          obtain ⟨_, hMem⟩ := ITree.csup_vis_mem hc' hEq
          exact (hAll' _ hMem).fail_vis_false

theorem dspec_admissible (Q : IPost α) (h : Heap) :
    Lean.Order.admissible (fun m : Result α => dspec m Q h) :=
  PartialSpec.admissible _ h

/-! ### `spec` theorems -/

theorem TotalSpec.mono {Q Q' : α → Heap → Prop}
    (hQ : ∀ value h, Q value h → Q' value h)
    {m : Result α} {h : Heap} (hSpec : TotalSpec Q m h) :
    TotalSpec Q' m h :=
  hSpec.induction (P := TotalSpec Q') (fun value h' hPost => .ret (hQ value h' hPost))
    fun _ hPre hSpec' => .vis hPre hSpec'

theorem spec_mono {Q Q' : IPost α} {m : Result α} {h : Heap}
    (hSpec : spec m Q h) (hQ : Q ⊢+ Q') : spec m Q' h :=
  hSpec.mono fun value h' => hQ value h'

theorem TotalSpec.bind {Q₁ : α → Heap → Prop} {Q₂ : β → Heap → Prop}
    {m : Result α} {next : α → Result β} {h : Heap}
    (hFirst : TotalSpec Q₁ m h)
    (hNext : ∀ value h', Q₁ value h' → TotalSpec Q₂ (next value) h') :
    TotalSpec Q₂ (m >>= next) h :=
  hFirst.induction (P := fun t u => TotalSpec Q₂ (t >>= next) u)
    (fun value h' hPost => by
      simpa only [Bind.bind, itree_ret_bind] using hNext value h' hPost)
    fun _ hPre hSpec' => by
      rw [vis_bind]
      exact .vis hPre hSpec'

theorem spec_bind {Q₁ : IPost α} {Q₂ : IPost β}
    {m : Result α} {next : α → Result β} {h : Heap}
    (hFirst : spec m Q₁ h)
    (hNext : ∀ value h', Q₁ value h' → spec (next value) Q₂ h') :
    spec (m >>= next) Q₂ h :=
  TotalSpec.bind hFirst hNext

theorem spec_ret (value : α) (Q : IPost α) (h : Heap) :
    spec (ITree.ret value : Result α) Q h ↔ Q value h :=
  ⟨TotalSpec.ret_post, fun hPost => .ret hPost⟩

theorem spec_pure (value : α) (Q : IPost α) (h : Heap) :
    spec (Pure.pure value : Result α) Q h ↔ Q value h :=
  spec_ret value Q h

/-- Total correctness at a guarded modification, the one node that does any
work: the guard must hold on the heap the event is performed on, and the
postcondition must hold of what the modification returns. -/
theorem spec_guardedModify {α : Type} {pre : Heap → Prop}
    (modify : (h : Heap) → pre h → α × Heap) (Q : IPost α) (h : Heap) :
    spec (Result.guardedModify pre modify) Q h ↔
      ∃ hPre : pre h, Q (modify h hPre).1 (modify h hPre).2 :=
  ⟨fun hSpec =>
      let ⟨hPre, hNext⟩ := hSpec.vis_view
      ⟨hPre, hNext.ret_post⟩,
    fun ⟨hPre, hPost⟩ => .vis hPre (.ret hPost)⟩

/-- Divergence cannot satisfy a total-correctness specification. -/
theorem spec_div (Q : IPost α) (h : Heap) :
    ¬ spec (ITree.div : Result α) Q h :=
  TotalSpec.div_false

@[simp]
theorem spec_fail (error : Error) (Q : IPost α) (h : Heap) :
    ¬ spec (Result.fail error) Q h :=
  TotalSpec.fail_false

@[simp]
theorem spec_fail_vis (error : Error)
    (k : RustEffect.O (RustEffect.I.fail error) → Result α)
    (Q : IPost α) (h : Heap) :
    ¬ spec (.vis (RustEffect.I.fail error) k) Q h :=
  TotalSpec.fail_vis_false

open Lean.Order in
/-- Total correctness is monotone in the interaction-tree approximation order. -/
theorem spec_mono_le {m m' : Result α} (hLe : m ⊑ m') (Q : IPost α)
    {h : Heap} (hSpec : spec m Q h) : spec m' Q h := by
  refine hSpec.induction
    (P := fun t u => ∀ t', t ⊑ t' → spec t' Q u) ?_ ?_ m' hLe
  · intro value h' hPost t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe'
    · exact absurd hDiv not_ret_div
    · obtain rfl := ret_inj.mp hRet
      exact .ret hPost
    · exact absurd hVis not_vis_ret
  · intro _ _ _ _ _ hPre ih t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe''⟩ := hLe'
    · exact absurd hDiv.symm not_div_vis
    · exact absurd hRet.symm not_vis_ret
    · obtain ⟨rfl, hCont⟩ := vis_inj hVis
      obtain rfl := eq_of_heq hCont
      exact .vis hPre (ih _ (hLe'' _))

/-! ### `dspec` theorems -/

theorem PartialSpec.mono {Q Q' : α → Heap → Prop}
    (hQ : ∀ value h, Q value h → Q' value h) {m : Result α} {h : Heap}
    (hSpec : PartialSpec Q m h) : PartialSpec Q' m h :=
  coinduction (PartialSpec Q)
    (fun _ _ hSpec' => hSpec'.step.mono hQ id fun _ _ => id) hSpec

theorem dspec_mono {Q Q' : IPost α} {m : Result α} {h : Heap}
    (hSpec : dspec m Q h) (hQ : Q ⊢+ Q') : dspec m Q' h :=
  hSpec.mono fun value h' => hQ value h'

theorem PartialSpec.bind {Q₁ : α → Heap → Prop} {Q₂ : β → Heap → Prop}
    {m : Result α} {next : α → Result β} {h : Heap}
    (hFirst : PartialSpec Q₁ m h)
    (hNext : ∀ value h', Q₁ value h' → PartialSpec Q₂ (next value) h') :
    PartialSpec Q₂ (m >>= next) h := by
  refine coinduction
    (fun t h' => (∃ m', t = m' >>= next ∧ PartialSpec Q₁ m' h') ∨
      PartialSpec Q₂ t h')
    ?_ (Or.inl ⟨m, rfl, hFirst⟩)
  rintro t h' (⟨m', rfl, hSpec⟩ | hSpec)
  · revert hSpec
    cases m' using ITree.cases with
    | ret value =>
        simp only [pure_bind]
        intro hSpec
        exact ((hNext value h' hSpec.ret_post).step).mono_tail fun _ _ => Or.inr
    | div => simp only [div_bind, SpecF.div, implies_true]
    | vis event k =>
        cases event with
        | guardedModify Result pre modify =>
            simp only [vis_bind, SpecF.vis, EventSpec]
            rintro hSpec
            obtain ⟨hPre, hNext'⟩ := hSpec.vis_view
            exact ⟨hPre, Or.inl ⟨_, rfl, hNext'⟩⟩
        | fail error =>
            simp only [vis_bind, SpecF.vis, EventSpec]
            exact fun hSpec => hSpec.fail_vis_false
  · exact hSpec.step.mono_tail fun _ _ => Or.inr

theorem dspec_bind {Q₁ : IPost α} {Q₂ : IPost β} {m : Result α} {next : α → Result β}
    {h : Heap} (hFirst : dspec m Q₁ h)
    (hNext : ∀ value h', Q₁ value h' → dspec (next value) Q₂ h') :
    dspec (m >>= next) Q₂ h :=
  PartialSpec.bind hFirst hNext

open Lean.Order in
/-- Partial correctness is *anti*-monotone in the interaction-tree
approximation order, where total correctness is monotone (`spec_mono_le`): an
approximation of a partially correct program does less, and divergence owes
nothing. -/
theorem PartialSpec.mono_le {m m' : Result α} (hLe : m ⊑ m') {Q : α → Heap → Prop}
    {h : Heap} (hSpec : PartialSpec Q m' h) : PartialSpec Q m h := by
  refine coinduction (fun t h' => ∃ t', t ⊑ t' ∧ PartialSpec Q t' h') ?_
    ⟨m', hLe, hSpec⟩
  rintro t h' ⟨t', hLe', hSpec'⟩
  rw [ITree.le_unfold] at hLe'
  obtain rfl | ⟨value, rfl, rfl⟩ | ⟨event, k, k', rfl, rfl, hCont⟩ := hLe'
  · simp only [SpecF.div]
  · simpa only [SpecF.ret] using hSpec'.ret_post
  · cases event with
    | guardedModify Result pre modify =>
        simp only [SpecF.vis, EventSpec]
        obtain ⟨hPre, hNext⟩ := hSpec'.vis_view
        exact ⟨hPre, _, hCont _, hNext⟩
    | fail error =>
        simp only [SpecF.vis, EventSpec]
        exact hSpec'.fail_vis_false

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
lifting, exactly as `Aeneas.Std.WP.spec_dspec` does for `Result`. -/
theorem triple_dtriple {α : Type} {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) : dtriple P m Q :=
  fun F h hPre => spec_dspec (hTriple F h hPre)

/-! ### `triple` rules -/

theorem triple_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) {h : Heap} (hPre : P h) :
    spec m Q h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact spec_mono hSpec fun value => sep_elim_right (Q value) emp

theorem triple_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : triple P m Q) (H : IProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact spec_mono hSpec fun value heap =>
    (sep_assoc (Q value) H F).mpr heap

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
  refine spec_mono (hTriple (H ∗ F) h hSwapped) fun value heap hPost => ?_
  exact (sep_mono (sep_comm (Q value) H).mp (entails_refl F)) heap
    ((sep_assoc (Q value) H F).mpr heap hPost)

theorem triple_conseq {P' P : IPre} {m : Result α}
    {Q' Q : IPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact spec_mono hSpec fun value =>
    sep_mono (hQ value) (entails_refl F)

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
exactly the heap it owns, taking the frame to be empty. This is the only place
`guardedModifyWp` meets `TotalSpec`; `spec_guardedModify` does the rest. -/
theorem guardedModifyWp_spec {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {Q : IPost α} {h : Heap}
    (hWp : guardedModifyWp pre modify Q h) :
    spec (Result.guardedModify pre modify) Q h := by
  rw [spec_guardedModify]
  have hWp' := hWp Heap.empty (PartialCommMonoid.compatible_comm
    (PartialCommMonoid.compatible_empty_left h))
  simp only [Heap.union_empty] at hWp'
  obtain ⟨hPre, h', -, hModify, hPost⟩ := hWp'
  subst h'
  exact ⟨hPre, hPost⟩

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
  apply spec_bind (hFirst F h hPre)
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
  exact dspec_mono hSpec fun value => sep_elim_right (Q value) emp

theorem dtriple_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) (H : IProp) : dtriple (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact dspec_mono hSpec fun value heap => (sep_assoc (Q value) H F).mpr heap

theorem dtriple_conseq {P' P : IPre} {m : Result α} {Q' Q : IPost α}
    (hTriple : dtriple P' m Q') (hP : P ⊢ P') (hQ : Q' ⊢+ Q) : dtriple P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact dspec_mono hSpec fun value => sep_mono (hQ value) (entails_refl F)

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
  apply dspec_bind (hFirst F h hPre)
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
