import Aeneas.Data.Coinductive.Spec

/-!
# A choice event, angelic and demonic

`Aeneas.Data.Coinductive.Spec` asks a machine for two healthiness conditions
rather than for determinism: `StateMachine.Resolves`, which total correctness is
adequate against, and `StateMachine.Conjunctive` together with
`StateMachine.Feasible`, which partial correctness needs.  This file is what
those conditions are *for*: a single event `choice a`, "produce an element of
`a`", read once angelically and once demonically, showing that each reading
satisfies one half and fails the other.

The angelic machine is the interesting one, because it is the reading
`Aeneas.SepLogic.EventSpec` already uses — a heap event is answered by an
existential.  `RustEffect.machine` is nevertheless conjunctive, and
`angelic_conjunctive_of_subsingleton` is why: the guard of a heap event is a
*proposition*, so the machine chooses from a subsingleton, which is no choice at
all.  Widen that guard to a real type — add `choice` to `RustEffect.I` — and
`not_angelic_conjunctive` applies: `dspec_admissible` is then false, and with it
partial correctness of every program defined by `partial_fixpoint`.
`not_admissible` exhibits that failure concretely.
-/

namespace Aeneas.Data.Coinductive.ChoiceTest

open Lean.Order

/-! ## The effect and its two machines -/

/-- One event per type: `choice a` is answered by an element of `a`. -/
@[reducible] def ChoiceEffect : Effect where
  I := Type
  O a := ULift a

/-- The **angelic** reading: the machine answers a demand whenever *some*
element of `a` meets it.  This is the reading of `Aeneas.SepLogic.EventSpec`,
and the choice operator of *Program Logics à la Carte*. -/
@[reducible] def angelic : StateMachine ChoiceEffect where
  State := Unit
  handle a s C := ∃ x : a, C ⟨x⟩ s
  handle_mono := by rintro a s C C' hC ⟨x, hOutcome⟩; exact ⟨x, hC _ _ hOutcome⟩

/-- The **demonic** reading: the machine answers a demand only when *every*
element of `a` meets it.  The event must still have an answer, or the machine
would meet every demand, including the impossible one. -/
@[reducible] def demonic : StateMachine ChoiceEffect where
  State := Unit
  handle a s C := Nonempty a ∧ ∀ x : a, C ⟨x⟩ s
  handle_mono := by
    rintro a s C C' hC ⟨hNonempty, hAll⟩
    exact ⟨hNonempty, fun x => hC _ _ (hAll x)⟩

/-- The program the two machines disagree about: it chooses a boolean and
returns `0` or `1` accordingly. -/
def flip : ITree ChoiceEffect Nat :=
  .vis Bool fun b => .ret (if b.down then 0 else 1)

/-! ## What the angel has: total correctness

An angelic machine resolves its transitions, which is all total correctness is
adequate against.  So `spec`-style reasoning survives angelic choice intact:
a program proved totally correct still *has* a run, and the run returns what
was proved of it. -/

theorem angelic_resolves : angelic.Resolves := by
  rintro a s C ⟨x, hOutcome⟩
  exact ⟨⟨x⟩, s, hOutcome, x, rfl, rfl⟩

theorem angelic_feasible : angelic.Feasible := angelic_resolves.feasible

/-- The angel picks the branch that meets the specification. -/
theorem angelic_flip_total : TotalSpec angelic (fun value _ => value = 0) flip () :=
  .vis ⟨true, .ret rfl⟩

/-- And the run it justifies exists: `TotalSpec.evaluates` applies unchanged. -/
example : ∃ value s', angelic.Evaluates flip () value s' ∧ value = 0 :=
  angelic_flip_total.evaluates angelic_resolves

/-! ## What the angel breaks: two demands on one event

Partial correctness compares what the machine does to *several* demands on the
same event — the demands of the approximations of a recursive program against
those of its limit, and the demand a run makes against the one a specification
justified.  An angel answers each demand by choosing the element that suits it,
and no single element need suit them all. -/

theorem not_angelic_conjunctive : ¬ angelic.Conjunctive := by
  intro hConj
  obtain ⟨b, hTrue, hFalse⟩ :=
    hConj.handle_and (event := Bool) (s := ())
      (C := fun answer _ => answer.down = true)
      (C' := fun answer _ => answer.down = false) ⟨true, rfl⟩ ⟨false, rfl⟩
  simp_all

/-- What the angel does have: a choice from a *subsingleton* is no choice, so
the machine is conjunctive at such an event however angelically it is read.

This is exactly the situation of `RustEffect.machine`: `EventSpec` answers a
heap event by `∃ hPre : pre h, …`, and `pre h` being a `Prop` there is only one
`hPre` to be had.  It is what `RustEffect.machine_conjunctive` proves, and the
only reason the machine of `Result` gets to be both angelic and conjunctive. -/
theorem angelic_conjunctive_of_subsingleton (a : Type) [Subsingleton a]
    (s : Unit) (Demands : (ChoiceEffect.O a → Unit → Prop) → Prop)
    (hNonempty : ∃ C, Demands C)
    (hAll : ∀ C, Demands C → angelic.handle a s C) :
    angelic.handle a s fun answer s' => ∀ C, Demands C → C answer s' := by
  obtain ⟨C₀, hC₀⟩ := hNonempty
  obtain ⟨x₀, -⟩ := hAll C₀ hC₀
  refine ⟨x₀, fun C hC => ?_⟩
  obtain ⟨x, hOutcome⟩ := hAll C hC
  rwa [Subsingleton.elim x₀ x]

/-- A guard is such an event: this is `pre` of a heap event, as a choice. -/
example (p : Prop) : Subsingleton (PLift p) := ⟨fun a b => by cases a; cases b; rfl⟩

/-! ## What the angel breaks: partial correctness is not preserved by runs

On an angelic machine a run is a run *the angel may steer*, and the branch it
takes need not be the branch the specification was proved of.  So
`PartialSpec.runs` — which asks for `Conjunctive` and `Feasible` — is not merely
unproven here but false. -/

theorem angelic_flip_partial : PartialSpec angelic (fun value _ => value = 0) flip () :=
  angelic_flip_total.toPartial

/-- The angel is free to take the other branch. -/
theorem angelic_flip_runs : angelic.Runs flip () (.ret 1) () := by
  apply Exec.event (M := angelic) (event := Bool)
  exact ⟨false, Exec.stop ⟨rfl, rfl⟩⟩

theorem not_angelic_partialSpec_runs :
    ¬ ∀ {α : Type} {Q : α → Unit → Prop} {m m' : ITree ChoiceEffect α} {s s' : Unit},
        PartialSpec angelic Q m s → angelic.Runs m s m' s' → PartialSpec angelic Q m' s' := by
  intro hRuns
  have hSpec := hRuns angelic_flip_partial angelic_flip_runs
  exact absurd hSpec.ret_post (by decide)

/-! ## What the angel breaks: admissibility

`partial_fixpoint` defines a recursive program as the supremum of the chain of
its approximations, so partial correctness has to be closed under such suprema
for `fix_induct` to prove anything of one.  It is not, on an angelic machine.

The chain below returns `1` on the first `i` answers of the event and diverges
on the rest.  Every approximation is partially correct for the postcondition
`value = 0`, the angel answering with a `n` the approximation diverges on —
divergence owes nothing.  But the answers the angel escapes to run out in the
limit, which returns `1` on every one of them. -/

/-- The `i`-th approximation. -/
def approx (i : Nat) : ITree ChoiceEffect Nat :=
  .vis Nat fun n => if n.down < i then .ret 1 else .div

def approxChain : ITree ChoiceEffect Nat → Prop := fun m => ∃ i, m = approx i

theorem approx_mono {i j : Nat} (hLe : i ≤ j) : approx i ⊑ approx j := by
  rw [ITree.le_unfold]
  refine Or.inr (Or.inr ⟨Nat, _, _, rfl, rfl, fun n => ?_⟩)
  by_cases hLt : n.down < i
  · simp only [hLt, Nat.lt_of_lt_of_le hLt hLe, if_pos]
    exact PartialOrder.rel_refl
  · simp only [hLt, if_false]
    rw [ITree.le_unfold]
    exact Or.inl rfl

theorem approxChain_chain : chain approxChain := by
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  exact (Nat.le_total i j).imp approx_mono approx_mono

/-- Every approximation diverges on some answer, and the angel takes it. -/
theorem approx_partial (i : Nat) :
    PartialSpec angelic (fun value _ => value = 0) (approx i) () := by
  refine .vis ⟨i, ?_⟩
  simp only [Nat.lt_irrefl, if_false]
  exact .div

/-- The limit has run out of answers to escape to. -/
theorem csup_approxChain :
    CCPO.csup approxChain_chain = .vis Nat fun _ => .ret 1 := by
  have hChild : ∀ answer,
      CCPO.csup (ITree.visChain_chain approxChain_chain Nat answer) = ITree.ret 1 := by
    intro answer
    refine PartialOrder.rel_antisymm (csup_le _ ?_) (le_csup _ ⟨_, ⟨answer.down + 1, rfl⟩, ?_⟩)
    · rintro _ ⟨k, ⟨i, hEq⟩, rfl⟩
      obtain ⟨-, hCont⟩ := vis_inj hEq
      obtain rfl := eq_of_heq hCont
      by_cases hLt : answer.down < i
      · simp only [hLt, if_pos]
        exact PartialOrder.rel_refl
      · simp only [hLt, if_false]
        rw [ITree.le_unfold]
        exact Or.inl rfl
    · simp only [Nat.lt_succ_self, if_pos]
  rw [ITree.csup_vis approxChain_chain (k' := fun n => if n.down < 0 then .ret 1 else .div)
    ⟨0, rfl⟩]
  simp only [hChild]

theorem not_admissible :
    ¬ Lean.Order.admissible fun m : ITree ChoiceEffect Nat =>
        PartialSpec angelic (fun value _ => value = 0) m () := by
  intro hAdmissible
  have hLimit := hAdmissible approxChain approxChain_chain (by rintro _ ⟨i, rfl⟩; exact approx_partial i)
  rw [csup_approxChain] at hLimit
  obtain ⟨-, hSpec⟩ := hLimit.vis_view
  exact absurd hSpec.ret_post (by decide)

/-! ## The demon has the other half

Demonic choice is the ordinary reading of a nondeterministic operational
semantics — the machine must be prepared for every answer — and it is
conjunctive and feasible without being deterministic and without resolving its
transitions.  So it keeps everything partial correctness has and loses the
adequacy of total correctness, exactly the mirror image of the angel. -/

theorem demonic_conjunctive : demonic.Conjunctive := by
  rintro a s Demands ⟨C₀, hC₀⟩ hAll
  exact ⟨(hAll C₀ hC₀).1, fun x C hC => (hAll C hC).2 x⟩

theorem demonic_feasible : demonic.Feasible := by
  rintro a s C ⟨⟨x⟩, hAll⟩
  exact ⟨⟨x⟩, s, hAll x⟩

/-- The demon has no single transition to offer: a run of it is a run of every
branch at once, which is why `TotalSpec.evaluates` is unavailable. -/
theorem not_demonic_resolves : ¬ demonic.Resolves := by
  intro hResolves
  obtain ⟨answer, s', -, -, hAll⟩ :=
    hResolves Bool () (fun _ _ => True) ⟨⟨true⟩, fun _ => trivial⟩
  have hTrue := (hAll true).1
  have hFalse := (hAll false).1
  simp only [← hTrue, ULift.up.injEq] at hFalse
  exact Bool.noConfusion hFalse

/-- Both halves of the theory partial correctness has are available, with no
determinism anywhere: admissibility, so `partial_fixpoint` programs can be
reasoned about, and preservation by runs. -/
example (Q : Nat → Unit → Prop) :
    Lean.Order.admissible fun m : ITree ChoiceEffect Nat => PartialSpec demonic Q m () :=
  PartialSpec.admissible demonic_conjunctive Q ()

example {Q : Nat → Unit → Prop} {m m' : ITree ChoiceEffect Nat} {s s' : Unit}
    (hSpec : PartialSpec demonic Q m s) (hRuns : demonic.Runs m s m' s') :
    PartialSpec demonic Q m' s' :=
  hSpec.runs demonic_conjunctive demonic_feasible hRuns

end Aeneas.Data.Coinductive.ChoiceTest
