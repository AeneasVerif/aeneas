import Aeneas.Data.Coinductive.ITreeWP

/-!
# A choice event, angelic and demonic

The generic judgments interpret a single event `choice a`, "produce an element
of `a`", once angelically and once demonically. These tests exercise the resulting
postconditions, conjunctivity, and admissibility. Execution and adequacy tests
belong with the operational semantics on `cezar/sm-semantics`.

The angelic machine is the interesting one, because it is the reading
`Aeneas.Std.WP.effectWP` already uses — a heap event is answered by
an existential. `effectWP` is nevertheless conjunctive, and
`angelic_conjunctive_of_subsingleton` is why: the guard of a heap event is a
*proposition*, so the machine chooses from a subsingleton, which is no choice at
all.  Widen that guard to a real type — add `choice` to `RustEffect.Input` — and
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
element of `a` meets it. This is the reading of
`Aeneas.Std.WP.effectWP`, and the choice operator of
*Program Logics à la Carte*. -/
@[reducible] def angelic : EffectWP ChoiceEffect where
  State := Unit
  wp a C s := ∃ x : a, C ⟨x⟩ s

instance : EffectWP.Monotone angelic where
  wp_mono {_ _ _} hC {_} := fun ⟨x, hOutcome⟩ => ⟨x, hC _ _ hOutcome⟩

/-- The **demonic** reading: the machine answers a demand only when *every*
element of `a` meets it.  The event must still have an answer, or the machine
would meet every demand, including the impossible one. -/
@[reducible] def demonic : EffectWP ChoiceEffect where
  State := Unit
  wp a C s := Nonempty a ∧ ∀ x : a, C ⟨x⟩ s

instance : EffectWP.Monotone demonic where
  wp_mono {_ _ _} hC {_} := fun ⟨hNonempty, hAll⟩ => ⟨hNonempty, fun x => hC _ _ (hAll x)⟩

/-- The program the two machines disagree about: it chooses a boolean and
returns `0` or `1` accordingly. -/
def flip : ITree ChoiceEffect Nat :=
  .vis Bool fun b => .ret (if b.down then 0 else 1)

/-! ## Angelic total and partial correctness -/

/-- The angel picks the branch that meets the specification. -/
theorem angelic_flip_total : DWP angelic flip (fun value _ => value = 0) () :=
  .vis ⟨true, DWP.ret_iff.mpr rfl⟩

theorem angelic_flip_partial : DWLP angelic flip (fun value _ => value = 0) () :=
  angelic_flip_total.toPartial

/-! ## What the angel breaks: two demands on one event

Partial correctness compares what the machine does to *several* demands on the
same event — in particular, the demands of the approximations of a recursive
program against those of its limit. An angel answers each demand by choosing
the element that suits it,
and no single element need suit them all. -/

theorem not_angelic_conjunctive : ¬ angelic.Conjunctive := by
  intro hConj
  obtain ⟨b, hTrue, hFalse⟩ :=
    EffectWP.wp_and (θ := angelic) (effect := Bool) (s := ())
      (C₁ := fun answer _ => answer.down = true)
      (C₂ := fun answer _ => answer.down = false) ⟨true, rfl⟩ ⟨false, rfl⟩
  simp_all

/-- What the angel does have: a choice from a *subsingleton* is no choice, so
the machine is conjunctive at such an event however angelically it is read.

This is exactly the situation of `effectWP`: it answers a heap event
by `∃ hPre : pre h, …`, and `pre h` being a `Prop` there is only one `hPre` to
be had. It is what the `Conjunctive` instance of `effectWP` proves, and the
only reason the machine of `Result` gets to be both angelic and conjunctive. -/
theorem angelic_conjunctive_of_subsingleton (a : Type) [Subsingleton a]
    (s : Unit) (Demands : (ChoiceEffect.O a → Unit → Prop) → Prop)
    (hNonempty : ∃ C, Demands C)
    (hAll : ∀ C, Demands C → angelic.wp a C s) :
    angelic.wp a (fun answer s' => ∀ C, Demands C → C answer s') s := by
  obtain ⟨C₀, hC₀⟩ := hNonempty
  obtain ⟨x₀, -⟩ := hAll C₀ hC₀
  refine ⟨x₀, fun C hC => ?_⟩
  obtain ⟨x, hOutcome⟩ := hAll C hC
  rwa [Subsingleton.elim x₀ x]

/-- A guard is such an event: this is `pre` of a heap event, as a choice. -/
example (p : Prop) : Subsingleton (PLift p) := ⟨fun a b => by cases a; cases b; rfl⟩

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
    DWLP angelic (approx i) (fun value _ => value = 0) () := by
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
        DWLP angelic m (fun value _ => value = 0) () := by
  intro hAdmissible
  have hLimit := hAdmissible approxChain approxChain_chain (by rintro _ ⟨i, rfl⟩; exact approx_partial i)
  rw [csup_approxChain] at hLimit
  obtain ⟨-, hSpec⟩ := hLimit.vis_view
  exact absurd (DWLP.ret_iff.mp hSpec) (by decide)

/-! ## Demonic choice is conjunctive

The postcondition must hold for every answer, so the handler can combine
demands and partial correctness is admissible. -/

instance demonic_conjunctive : demonic.Conjunctive where
  wp_conj {_ _} _ := by
    rintro ⟨C₀, hC₀⟩ hAll
    exact ⟨(hAll C₀ hC₀).1, fun x C hC => (hAll C hC).2 x⟩

theorem not_demonic_flip_total :
    ¬ DWP demonic flip (fun value _ => value = 0) () := by
  intro hSpec
  exact absurd (DWP.ret_iff.mp ((hSpec.vis_view).2 false)) (by decide)

theorem not_demonic_flip_partial :
    ¬ DWLP demonic flip (fun value _ => value = 0) () := by
  intro hSpec
  exact absurd (DWLP.ret_iff.mp ((hSpec.vis_view).2 false)) (by decide)

example (Q : Nat → Unit → Prop) :
    Lean.Order.admissible fun m : ITree ChoiceEffect Nat => DWLP demonic m Q () :=
  DWLP.admissible demonic Q ()

end Aeneas.Data.Coinductive.ChoiceTest
