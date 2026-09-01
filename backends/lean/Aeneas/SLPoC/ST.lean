import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.WP
import Aeneas.Tactic.Step.StepStar

/-!
# The state monad `St` and its program logic

`St` is the freer monad over heap events. This file defines it, gives it an
operational semantics and a certified interpreter, derives its
separation-logic triples, and wires those triples to the `step`/`step*` tactics.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## The state monad, its operations and operational semantics -/

universe u v

/-! The type of partially defined stateful operations. -/
inductive StEvents (Heap : Type u) : Type v → Type (max u v) where
  | GuardedModify {α : Type v} (pre : Heap → Prop)
      (modify : (h : Heap) → pre h → α × Heap) : StEvents Heap α

abbrev St := FFree (StEvents Heap)

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree (StEvents Heap)))

/-- The operational semantics of `St`.
`StEvents.Step e h result h'` holds when the guard of `e` holds on `h`, and its
modifier returns `result` and `h'`.  An event whose guard does not hold is
stuck. -/
inductive StEvents.Step :
    {β : Type} → StEvents Heap β → Heap → β → Heap → Prop where
  | guardedModify {β : Type} {pre : Heap → Prop}
      {modify : (h : Heap) → pre h → β × Heap} {h : Heap}
      (hPre : pre h) :
      Step (.GuardedModify pre modify) h (modify h hPre).1 (modify h hPre).2

@[reducible]
def StEvents.machine : StateMachine (StEvents Heap) :=
  .ofStep Heap StEvents.Step

theorem StEvents.machine_resolves : StEvents.machine.Resolves :=
  StateMachine.ofStep_resolves Heap StEvents.Step

/-- Big-step relation -/
def Evaluates (m : St α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  StEvents.machine.Evaluates m h value h'

/-! ## Denotation into the weakest-precondition monad -/

/-- A guarded modification is local when, for every disjoint frame, its guard
holds and its output can be split into an owned result and the unchanged frame.
Quantifying over frames here makes the denotation upward-closed and validates
the frame rule for arbitrary guarded modifications. -/
def theta_ev : StEvents Heap α → Wp α
  | .GuardedModify pre modify =>
      { run := fun Q =>
          { holds := fun h =>
              ∀ frame, PartialCommMonoid.Compatible h frame →
                ∃ hPre : pre (h ∪ frame), ∃ h',
                  PartialCommMonoid.Compatible h' frame ∧
                  (modify (h ∪ frame) hPre).2 = h' ∪ frame ∧
                  Q (modify (h ∪ frame) hPre).1 h'
            up_closed := by
              rintro h hBig hWp ⟨rest, hDisjointRest, rfl⟩ frame hDisjointFrame
              obtain ⟨hDisjointRestFrame, hDisjointCombined⟩ :=
                (PartialCommMonoid.compatible_assoc h rest frame).mp
                  ⟨hDisjointRest, hDisjointFrame⟩
              have hWp' := hWp (rest ∪ frame) hDisjointCombined
              rw [← PartialCommMonoid.union_assoc
                hDisjointRest hDisjointFrame] at hWp'
              obtain ⟨hPre, h', hDisjoint', hModify, hQ⟩ := hWp'
              obtain ⟨hDisjoint'Rest, hDisjoint'Frame⟩ :=
                (PartialCommMonoid.compatible_assoc h' rest frame).mpr
                  ⟨hDisjointRestFrame, hDisjoint'⟩
              refine ⟨?_, h' ∪ rest, ?_, ?_, ?_⟩
              · exact hPre
              · exact hDisjoint'Frame
              · simpa only [PartialCommMonoid.union_assoc
                  hDisjoint'Rest hDisjoint'Frame] using hModify
              · exact (Q _).up_closed hQ (Heap.Sub.union_left hDisjoint'Rest)
          }
        monotone := by
          intro Q₁ Q₂ hQ h hWp frame hDisjoint
          obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ :=
            hWp frame hDisjoint
          exact ⟨hPre, h', hDisjoint', hModify,
            hQ _ h' hPost⟩
      }

theorem theta_ev_elim {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap}
    {R : SLPost α} {h : Heap}
    (hWp : theta_ev (.GuardedModify pre modify) R h) :
    ∃ hPre : pre h,
      R (modify h hPre).1 (modify h hPre).2 := by
  have hWp' := hWp empty (PartialCommMonoid.compatible_comm
    (PartialCommMonoid.compatible_empty_left h))
  simp only [Heap.union_empty] at hWp'
  obtain ⟨hPre, h', -, hModify, hPost⟩ := hWp'
  subst h'
  exact ⟨hPre, hPost⟩

def theta : St α → Wp α
  | .ok value => Wp.pure value
  | .event event next =>
      Wp.bind (theta_ev event) (fun value => theta (next value))

theorem theta_ev_frame (event : StEvents Heap α) (Q : SLPost α)
    (H : SLProp) :
    theta_ev event Q ∗ H ⊢ theta_ev event (Q ∗+ H) := by
  cases event with
  | GuardedModify pre modify =>
      rintro h ⟨h₁, h₂, hDisjoint, rfl, hWp, hH⟩ frame hDisjointFrame
      obtain ⟨hDisjoint₂Frame, hDisjointCombined⟩ :=
        (PartialCommMonoid.compatible_assoc h₁ h₂ frame).mp
          ⟨hDisjoint, hDisjointFrame⟩
      have hWp' := hWp (h₂ ∪ frame) hDisjointCombined
      rw [← PartialCommMonoid.union_assoc
        hDisjoint hDisjointFrame] at hWp'
      obtain ⟨hPre, h', hDisjoint', hModify, hQ⟩ := hWp'
      obtain ⟨hDisjoint'H₂, hDisjoint'Frame⟩ :=
        (PartialCommMonoid.compatible_assoc h' h₂ frame).mpr
          ⟨hDisjoint₂Frame, hDisjoint'⟩
      refine ⟨?_, h' ∪ h₂, ?_, ?_, ?_⟩
      · exact hPre
      · exact hDisjoint'Frame
      · simpa only [PartialCommMonoid.union_assoc
          hDisjoint'H₂ hDisjoint'Frame] using hModify
      · exact ⟨h', h₂, hDisjoint'H₂, rfl, hQ, hH⟩

theorem theta_frame (m : St α) (Q : SLPost α) (H : SLProp) :
    theta m Q ∗ H ⊢ theta m (Q ∗+ H) := by
  induction m with
  | ok value =>
      intro h hPre
      exact hPre
  | event event next ih =>
      intro h hPre
      apply (theta_ev event).monotone (fun value => ih value) h
      exact theta_ev_frame event (fun value => theta (next value) Q) H h hPre

/-- `theta` preserves the monad operations up to `Wp` equivalence. -/
def thetaMorphism : MonadMorphism St Wp where
  toFun := theta
  map_pure := by
    intro α value
    rfl
  map_bind := by
    intro α β m next
    induction m
    · rfl
    · rename_i γ event k ih
      change
        Wp.bind (theta_ev event) (fun value => theta (k value >>= next)) ≈
          Wp.bind (theta_ev event) (fun value =>
            Wp.bind (theta (k value)) (fun result => theta (next result)))
      exact Wp.bind_congr (by rfl) ih

/-! ## Hoare triples -/

/-- A Hoare triple interpreted by embedding its precondition and its
postcondition into the ordered weakest-precondition monad.

The triple is affine because the *assertions* are: a postcondition holds of any
heap that extends the resources it describes, so a computation may leak.  No
explicit affine top is needed for that, unlike in SLF. -/
def triple (P : SLPre) (m : St α) (Q : SLPost α) : Prop :=
  theta m ≤ pp2wp P Q

namespace SepLogic

scoped syntax:lead (name := specSyntax)
  "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := specSyntaxPred)
  "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntax)
  " ⦃" term " ⦄" term:lead
  " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntaxPred)
  " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

scoped macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) =>
      `(triple emp $m (fun $result => ⌜$Q⌝))
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(triple emp $m (fun _ => ⌜$Q⌝))
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄) =>
      `(triple iprop($P) $m (fun $result => iprop($Q)))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄) =>
      `(triple iprop($P) $m (fun _ => iprop($Q)))

end SepLogic

/-- The definition of `triple`, spelled out.

This form is known as a **Texan triple**: it is how Iris states specifications,
```
{{{ P }}} e {{{ RET v; Q }}}  ≜  □ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP e {{ Φ }}
```
the postcondition being passed to the continuation `R` through a wand rather
than asserted directly.  The name is due to the "big" `{{{ … }}}` braces.

Two differences with Iris, both inessential here: the outer entailment is left
at the meta level instead of being internalised as a second wand, and there is
no `□`, since this model has no invariants, no step-indexing and no
higher-order specifications to store a triple in. -/
theorem triple_texan (P : SLPre) (m : St α) (Q : SLPost α) :
    triple P m Q ↔
      ∀ R : SLPost α, P ∗ (Q -∗+ R) ⊢ theta m R :=
  Iff.rfl

theorem triple_iff (P : SLPre) (m : St α) (Q : SLPost α) :
    triple P m Q ↔ P ⊢ theta m Q := by
  constructor
  · intro hTriple h hP
    exact hTriple Q h (pp2wp_conseq (fun _ => himpl_refl _) h hP)
  · intro hTriple R h hPre
    apply (theta m).monotone (qwand_cancel Q R) h
    exact theta_frame m Q (Q -∗+ R) h
      (hstar_mono hTriple (himpl_refl _) h hPre)

theorem triple_frame {P : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) (H : SLProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hP, hH⟩
  apply theta_frame m Q H h
  exact ⟨h₁, h₂, hDisjoint, hEq,
    (triple_iff P m Q).mp hTriple h₁ hP, hH⟩

theorem triple_conseq {P' P : SLPre} {m : St α}
    {Q' Q : SLPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  apply (theta m).monotone hQ h
  exact (triple_iff P' m Q').mp hTriple h (hP h hPre)

/-- An arbitrary postcondition resource may be discarded.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem triple_hany_post {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m (Q ∗+ H)) :
    triple P m Q :=
  triple_conseq hTriple (himpl_refl P)
    (fun value => hstar_elim_right (Q value) H)

/-- An arbitrary precondition resource may be discarded. -/
theorem triple_hany_pre {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ H) m Q :=
  triple_hany_post (triple_frame hTriple H)

theorem triple_hpure {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : P → triple H m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, hH⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff H m Q).mp (hTriple hP) h hH

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `triple_hpure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem triple_hpure_keep {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : P → triple (⌜P⌝ ∗ H) m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, _⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff _ m Q).mp (hTriple hP) h hPre

theorem triple_hexists {ι : Sort _} {J : ι → SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : ∀ x, triple (J x) m Q) :
    triple iprop(∃ x, J x) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨x, hJ⟩
  exact (triple_iff (J x) m Q).mp (hTriple x) h hJ

theorem triple_conseq_frame {H₂ : SLProp} {H₁ H : SLPre}
    {Q₁ Q : SLPost α}
    {m : St α}
    (hTriple : triple H₁ m Q₁)
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    triple H m Q :=
  triple_conseq (triple_frame hTriple H₂) hPre hPost

theorem triple_hpure' {P : Prop} {m : St α} {Q : SLPost α}
    (hTriple : P → triple emp m Q) :
    triple ⌜P⌝ m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  exact (triple_iff hempty m Q).mp (hTriple hPre) h trivial

theorem triple_pure {P : SLPre} {Q : SLPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : St α) Q :=
  (triple_iff _ _ _).mpr hPost

theorem triple_bind {P : SLPre} {Q₁ : SLPost α}
    {Q : SLPost β} {m : St α} {next : α → St β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have hBind :
      Wp.bind (theta m) (fun value => theta (next value)) Q h := by
    apply (theta m).monotone
      (fun value => (triple_iff (Q₁ value) (next value) Q).mp (hNext value))
      h
    exact (triple_iff P m Q₁).mp hFirst h hPre
  exact (thetaMorphism.map_bind m next).1 Q h hBind

theorem triple_seq {P H : SLPre} {Q : SLPost β}
    {m₁ : St α} {m₂ : St β}
    (hFirst : triple P m₁ (fun _ => H))
    (hSecond : triple H m₂ Q) :
    triple P (m₁ >>= fun _ => m₂) Q :=
  triple_bind hFirst (fun _ => hSecond)

/-! ## Ramified rules -/

/-- SLF's `triple_ramified_frame`. SLF puts an affine top on the right of the
wand so that the leftovers may be discarded; here the wand's own conclusion is
affine, so `Q` alone will do. -/
theorem triple_ramified_frame {α : Type} {P Pm : SLPre} {Q Qm : SLPost α}
    {m : St α} (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_conseq_frame hStep hPre (qwand_cancel Qm Q)

/-- The ramified frame rule for a call followed by a continuation. -/
theorem triple_ramified_bind {α β : Type} {P Pm F : SLPre} {Qm : SLPost α}
    {next : α → St β} {Q : SLPost β} {m : St α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_bind (triple_conseq (triple_frame hStep F) hPre (fun _ => himpl_refl _))
    hNext

/-- Rewrite part of a triple's precondition using an entailment. -/
theorem triple_xchange {α : Type} {H₁ H₂ H₃ : SLPre} {Q : SLPost α} {m : St α}
    (hPart : H₁ ⊢ H₂) (hRest : triple (H₂ ∗ H₃) m Q) : triple (H₁ ∗ H₃) m Q :=
  triple_conseq hRest (hstar_mono hPart (himpl_refl H₃)) (fun _ => himpl_refl _)

/-! ## Wiring of `step` to separation-logic triples -/

open Lean Elab Meta Tactic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation. -/
theorem triple_step_bind {α β : Type} {P Pm F : SLPre}
    {next : α → St β} {Q : SLPost β}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_ramified_bind hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call. -/
theorem triple_step_mono {α : Type} {P Pm : SLPre} {Q : SLPost α}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- The tactic `step` runs on the goals it prepares. A no-op on a goal which is
not a triple. -/
macro "intro_triple" : tactic =>
  `(tactic| (sl_norm; sl_pull_shallow))

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
    discharge_tactic := SpecInfo.tac `(tactic| sl_frame)
    to_mvcgen := none
    liftings := #[]
  }

@[step]
theorem ok.spec (value : α) :
    ⦃ emp ⦄ (FFree.ok value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  triple_pure fun _ _ => rfl

@[step]
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ok.spec value

/-! ## Certified execution -/

/-- What running `m` from `h` produces: the returned value and final heap,
together with the postcondition they satisfy and the evaluation that reaches
them. -/
def Outcome (m : St α) (Q : SLPost α) (h : Heap) : Type 1 :=
  { outcome : α × Heap //
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 }

/-- Run `m` from `h`. The weakest-precondition proof supplies the guard of each
event and guarantees the postcondition. -/
def run : (m : St α) → (h : Heap) → (Q : SLPost α) → theta m Q h → Outcome m Q h
  | .ok value, h, _, hWp =>
      ⟨(value, h), hWp,
        StateMachine.Evaluates.ok (M := StEvents.machine) value h⟩
  | .event event next, h, Q, hWp =>
      have hEvent : theta_ev event (fun result => theta (next result) Q) h := hWp
      match event, hEvent with
      | .GuardedModify _ modify, hWp =>
          let hPre := (theta_ev_elim hWp).choose
          let result := (modify h hPre).1
          let modified := (modify h hPre).2
          let outcome :=
            run (next result) modified Q (theta_ev_elim hWp).choose_spec
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.guardedModify hPre) outcome.property.2⟩

/-- The value and heap produced by `run`. -/
def exec (m : St α) (h : Heap) (Q : SLPost α) (hWp : theta m Q h) : α × Heap :=
  (run m h Q hWp).val

theorem exec_post (m : St α) (h : Heap) (Q : SLPost α) (hWp : theta m Q h) :
    Q (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.1

theorem exec_evaluates (m : St α) (h : Heap) (Q : SLPost α)
    (hWp : theta m Q h) :
    Evaluates m h (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.2

/-! ## Executing a specified program -/

/-- Run a program from a heap satisfying the precondition of a proved triple. -/
def runTriple {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q ((triple_iff P m Q).mp hTriple h hPre)

/-- The value and heap produced by a specified program. -/
def execTriple {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : α × Heap :=
  (runTriple m h hTriple hPre).val

theorem execTriple_post {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Q (execTriple m h hTriple hPre).1 (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.1

theorem execTriple_evaluates {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Evaluates m h (execTriple m h hTriple hPre).1
      (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.2

/-- Run a program proved from `emp` on the empty heap. -/
def execClosed {Q : SLPost α} (m : St α) (hTriple : triple emp m Q) : α × Heap :=
  execTriple m empty hTriple trivial

theorem execClosed_post {Q : SLPost α} (m : St α) (hTriple : triple emp m Q) :
    Q (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_post m empty hTriple trivial

theorem execClosed_evaluates {Q : SLPost α} (m : St α)
    (hTriple : triple emp m Q) :
    Evaluates m empty (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_evaluates m empty hTriple trivial

end Aeneas.SLPoC
