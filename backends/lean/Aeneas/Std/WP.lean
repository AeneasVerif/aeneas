module
public import Aeneas.Std.WPDef
public import Aeneas.SepLogic.Local
public import Mathlib.Data.Nat.Notation
public import Aeneas.Std.Primitives
public import Aeneas.Std.Delab
public import Std.Do
public meta import AeneasMeta.Simp
public import Aeneas.Tactic.Solver.Grind.Init
public import Aeneas.Tactic.Step.DspecInduction
public meta import Aeneas.Std.Spec
public meta import Aeneas.Std.Delab
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public import Aeneas.Data.Coinductive.ITreeWP
public import Aeneas.SepLogic.Lemmas
public import Aeneas.SepLogic.Delab
public import Aeneas.SepLogic.Tactic.IFrame
public import Aeneas.SepLogic.Tactic.IIntro
public import Aeneas.SepLogic.Tactic.IRewrite
public import Aeneas.SepLogic.Tactic.ISimp
import all Init.Internal.Order.Basic
public section

namespace Aeneas.Std.WP

open Aeneas.Std Result
open Aeneas.Data.Coinductive
open Lean.Order
open Aeneas.SepLogic

section ResultImplementation

unseal Result

@[expose] section

instance : EffectWP.Conjunctive effectWP where
  wp_conj {effect} _ _ := by
    rintro ⟨C₀, hC₀⟩ hAll
    cases effect with
    | guardedModify =>
        exact ⟨(hAll C₀ hC₀).1, fun x s' hx C hC => (hAll C hC).2 x s' hx⟩
    | fail => exact hAll C₀ hC₀

/-! ### Realization of assertions by heaps -/

theorem realizes_emp_empty : Realizes emp Heap.empty :=
  ⟨Heap.inv_empty, ∅, trivial, Fragment.matches_empty _, fun _ _ _ h => h.elim⟩

theorem realizes_sep_emp {H : IProp} {s : Heap} : Realizes (H ∗ emp) s ↔ Realizes H s := by
  rw [sep_emp_r_eq]

theorem Realizes.pure {P : Prop} {s : Heap} (h : Realizes ⌜P⌝ s) : P :=
  let ⟨_, _, hP, _⟩ := h; hP

/-- Two resources of the same key which hold in the same heap are equal. -/
theorem Resource.Holds.unique {s : Heap} {r r' : Resource}
    (h : r.Holds s) (h' : r'.Holds s) (hIncompatible : ¬ r.Compatible r') : r = r' := by
  simp only [Resource.Compatible, not_or, Decidable.not_not] at hIncompatible
  obtain ⟨hBase, hKey⟩ := hIncompatible
  cases r <;> cases r' <;>
    simp only [Resource.base, Resource.key, reduceCtorEq, Option.some.injEq] at hBase hKey
  · obtain ⟨b, hb, _, hbptr, hc⟩ := h
    obtain ⟨b', hb', _, hbptr', hc'⟩ := h'
    subst hBase hKey
    rw [hb] at hb'; cases hb'
    rw [hc] at hc'; cases hc'
    subst hbptr hbptr'; rfl
  · obtain ⟨b, hb, hlen, _, hbptr, hown⟩ := h
    obtain ⟨b', hb', hlen', _, hbptr', hown'⟩ := h'
    subst hBase
    rw [hb] at hb'; cases hb'
    subst hlen hlen' hbptr hbptr' hown hown'; rfl

/-- The union of the parts of two fragments which hold in the same heap, and which are
disjoint from the same fragment. -/
theorem Fragment.join_of_matches {s : Heap} {o₁ o₂ frame : Fragment}
    (hMatches₁ : Fragment.Matches s o₁) (hMatches₂ : Fragment.Matches s o₂)
    (hDisjoint₁ : o₁.Disjoint frame) (hDisjoint₂ : o₂.Disjoint frame) :
    ∃ o, o = o₁ ∪ o₂ ∧ o.Disjoint frame ∧ Fragment.Matches s o ∧
      PartialCommMonoid.Subheap o₁ o ∧ PartialCommMonoid.Subheap o₂ o := by
  classical
  -- The resources of `o₂` which are not in `o₁`
  let rest₂ : Fragment := fun r => o₂ r ∧ ¬ o₁ r
  let rest₁ : Fragment := fun r => o₁ r ∧ ¬ o₂ r
  have hCompat {a b : Fragment} (ha : Fragment.Matches s a) (hb : Fragment.Matches s b) :
      a.Disjoint (fun r => b r ∧ ¬ a r) := by
    intro r hr r' ⟨hr', hNot⟩
    refine Classical.byContradiction fun hInc => ?_
    exact hNot (Resource.Holds.unique (ha r hr) (hb r' hr') hInc ▸ hr)
  have hEq₁ : o₁ ∪ rest₂ = o₁ ∪ o₂ := by
    funext r; apply propext
    show (o₁ r ∨ (o₂ r ∧ ¬ o₁ r)) ↔ (o₁ r ∨ o₂ r)
    by_cases h : o₁ r <;> simp [h]
  have hEq₂ : o₂ ∪ rest₁ = o₁ ∪ o₂ := by
    funext r; apply propext
    show (o₂ r ∨ (o₁ r ∧ ¬ o₂ r)) ↔ (o₁ r ∨ o₂ r)
    by_cases h : o₂ r <;> simp [h]
  refine ⟨o₁ ∪ o₂, rfl, Fragment.disjoint_union_left.mpr ⟨hDisjoint₁, hDisjoint₂⟩,
    (Fragment.matches_union _ _ _).mpr ⟨hMatches₁, hMatches₂⟩,
    PartialCommMonoid.subheap_iff.mpr ⟨rest₂, hCompat hMatches₁ hMatches₂, hEq₁.symm⟩,
    PartialCommMonoid.subheap_iff.mpr ⟨rest₁, hCompat hMatches₂ hMatches₁, hEq₂.symm⟩⟩

theorem ispec_iff {P : IPre} {m : Result α} {Q : IPost α} :
    ispec P m Q ↔
      ∀ F s, Realizes (P ∗ F) s →
        DWP effectWP m (fun value s' => Realizes ((Q ∗+ F) value) s') s := by
  constructor
  · rintro hSpec F s ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, hP, hF⟩, hMatches, hAuth⟩
    exact hSpec h₁ hP F s
      ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, PartialCommMonoid.Subheap.refl _, hF⟩, hMatches, hAuth⟩
  · intro hSpec owned hP F s
    rintro ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, hOwned, hF⟩, hMatches, hAuth⟩
    exact hSpec F s ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, P.up_closed hP hOwned, hF⟩, hMatches, hAuth⟩

theorem dispec_iff {P : IPre} {m : Result α} {Q : IPost α} :
    dispec P m Q ↔
      ∀ F s, Realizes (P ∗ F) s →
        DWLP effectWP m (fun value s' => Realizes ((Q ∗+ F) value) s') s := by
  constructor
  · rintro hSpec F s ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, hP, hF⟩, hMatches, hAuth⟩
    exact hSpec h₁ hP F s
      ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, PartialCommMonoid.Subheap.refl _, hF⟩, hMatches, hAuth⟩
  · intro hSpec owned hP F s
    rintro ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, hOwned, hF⟩, hMatches, hAuth⟩
    exact hSpec F s ⟨hInv, _, ⟨h₁, h₂, hDisjoint, rfl, P.up_closed hP hOwned, hF⟩, hMatches, hAuth⟩

theorem ispec_dispec {α : Type u} {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) : dispec P m Q := by
  rw [ispec_iff] at hTriple
  rw [dispec_iff]
  intro F s hPre
  exact (hTriple F s hPre).toPartial

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

private theorem rawIwp_admissible (Q : IPost α) (s : Heap) :
    admissible (fun m : Result α => rawIwp false m Q s) :=
  DWLP.admissible effectWP _ s

theorem dispec_admissible {α : Type u} (P : IPre) (Q : IPost α) :
    admissible (fun m : Result α => dispec P m Q) := by
  simp only [dispec_iff]
  intro c hc hAll F s hPre
  exact rawIwp_admissible (Q ∗+ F) s c hc fun x hx => hAll x hx F s hPre

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

@[simp] theorem uncurry'_pair x y (p : α → β → γ) : uncurry' p (x, y) = p x y := by simp [uncurry']
@[defeq] theorem uncurry'_eq x (p : α → β → γ) : uncurry' p x = p x.fst x.snd := by simp [uncurry']

/-- The spatial counterparts of `Std.uncurry_eq_prop` and `Std.uncurry_eq_prop_arrow`,
for postconditions of the separation logic judgments applied to a returned tuple
which is not a literal. -/
theorem uncurry_eq_iprop {α β} (x : α × β) (p : α → β → IProp) :
    Std.uncurry p x = p x.fst x.snd := by cases x; rfl

theorem uncurry_eq_iprop_arrow {α β σ} (x : α × β) (p : α → β → σ → IProp) :
    Std.uncurry p x = p x.fst x.snd := by cases x; rfl

/-- A value satisfies the postcondition if the precondition entails it. (The converse doesn't hold:
the precondition may only hold of fragments which no heap realizes.) -/
theorem ispec_ok (x : α) (hPost : P ⊢ Q x) : ispec P (ok x) Q := by
  rw [ispec_iff]
  intro F s hPre
  exact DWP.ret_iff.mpr (Realizes.mono (sep_mono hPost (entails_refl F)) hPre)

/-- A heap operation, given as a relation between the initial heap, the result and the final heap,
is correct iff it is local: from every heap which realizes the precondition with a frame fragment,
it is enabled, and it keeps the frame and establishes the postcondition. -/
theorem ispec_guardedModify {α : Type} {modify : Heap → α → Heap → Prop} {P : IPre} {Q : IPost α}
    (hLocal : ∀ s h frame, P h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) →
      (∃ x s', modify s x s') ∧
      ∀ x s', modify s x s' →
        ∃ h', h'.Disjoint frame ∧ Fragment.Matches s' (h' ∪ frame) ∧ s'.Inv ∧
          AuthOK s' (h' ∪ frame) ∧ Q x h') :
    ispec P (Result.guardedModify modify) Q := by
  rw [ispec_iff]
  rintro F s ⟨hInv, _, ⟨owned, framed, hDisjoint, rfl, hP, hF⟩, hMatches, hAuth⟩
  obtain ⟨hEnabled, hPost⟩ := hLocal s owned framed hP hDisjoint hMatches hInv hAuth
  refine DWP.vis (θ := effectWP)
    (effect := RustEffect.Input.guardedModify _ modify) ⟨hEnabled, fun x s' hx => ?_⟩
  obtain ⟨h', hDisjoint', hMatches', hInv', hAuth', hQ⟩ := hPost x s' hx
  exact DWP.ret_iff.mpr ⟨hInv', h' ∪ framed, ⟨h', framed, hDisjoint', rfl, hQ, hF⟩, hMatches', hAuth'⟩

/-- The heap operation `op` keeps the authority of the owned exclusive blocks (see `AuthOK`), from
the fragments of `A` to those of `B`, for every frame. -/
@[expose] def Bytes.AuthPres {α : Type} (A : Fragment → Prop) (op : Heap → α → Heap → Prop)
    (B : α → Fragment → Prop) : Prop :=
  ∀ a F s, A a → a.Disjoint F → Fragment.Matches s (a ∪ F) → s.Inv → AuthOK s (a ∪ F) →
    ∀ x s' a', op s x s' → a'.Disjoint F → Fragment.Matches s' (a' ∪ F) → s'.Inv → B x a' →
      AuthOK s' (a' ∪ F)

/-- A local heap operation on fragments, which keeps the authority of the owned exclusive blocks, is
local on the upward closures. -/
theorem Bytes.LocalOp.upClose {α : Type} {A : Fragment → Prop} {op : Heap → α → Heap → Prop}
    {B : α → Fragment → Prop} (hLocal : Bytes.LocalOp A op B) (hAuthPres : Bytes.AuthPres A op B) :
    ∀ s h frame, upClose A h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) →
      (∃ x s', op s x s') ∧
      ∀ x s', op s x s' →
        ∃ h', h'.Disjoint frame ∧ Fragment.Matches s' (h' ∪ frame) ∧ s'.Inv ∧
          AuthOK s' (h' ∪ frame) ∧ upClose (B x) h' := by
  rintro s _ frame ⟨a, hA, hSub⟩ hd hm hInv hAuth
  obtain ⟨rest, hRest, rfl⟩ := PartialCommMonoid.subheap_iff.mp hSub
  have hdParts := Fragment.disjoint_union_left.mp hd
  have hdA : a.Disjoint (rest ∪ frame) := Fragment.disjoint_union_right.mpr ⟨hRest, hdParts.1⟩
  have hmA : Fragment.Matches s (a ∪ (rest ∪ frame)) := by
    rwa [← Fragment.union_assoc]
  have hAuthA : AuthOK s (a ∪ (rest ∪ frame)) := by
    rwa [← Fragment.union_assoc]
  obtain ⟨hEnabled, hPost⟩ := hLocal a (rest ∪ frame) s hA hdA hmA hInv
  refine ⟨hEnabled, fun x s' hx => ?_⟩
  obtain ⟨a', hdNew, hmNew, hInv', hB⟩ := hPost x s' hx
  have hAuth' := hAuthPres a (rest ∪ frame) s hA hdA hmA hInv hAuthA x s' a' hx hdNew hmNew hInv' hB
  have hdNewParts := Fragment.disjoint_union_right.mp hdNew
  refine ⟨a' ∪ rest, Fragment.disjoint_union_left.mpr ⟨hdNewParts.2, hdParts.2⟩, ?_, hInv', ?_,
    a', hB, PartialCommMonoid.Subheap.union_left hdNewParts.1⟩
  · rwa [Fragment.union_assoc]
  · rwa [Fragment.union_assoc]

/-- A heap operation, totalized: it fails with undefined behavior if it is not enabled. It is
correct if it is local (in which case it is enabled). -/
theorem ispec_checkedModify {α : Type} {modify : Heap → α → Heap → Prop} {P : IPre} {Q : IPost α}
    (hLocal : ∀ s h frame, P h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) →
      (∃ x s', modify s x s') ∧
      ∀ x s', modify s x s' →
        ∃ h', h'.Disjoint frame ∧ Fragment.Matches s' (h' ∪ frame) ∧ s'.Inv ∧
          AuthOK s' (h' ∪ frame) ∧ Q x h') :
    ispec P (Result.checkedModify modify) Q := by
  rw [ispec_iff]
  rintro F s ⟨hInv, _, ⟨owned, framed, hDisjoint, rfl, hP, hF⟩, hMatches, hAuth⟩
  obtain ⟨⟨x₀, s₀, hx₀⟩, hPost⟩ := hLocal s owned framed hP hDisjoint hMatches hInv hAuth
  unfold Result.checkedModify
  refine DWP.vis (θ := effectWP)
    (effect := RustEffect.Input.guardedModify _ (State.checked modify))
    ⟨⟨some x₀, s₀, hx₀⟩, fun answer s' hAnswer => ?_⟩
  cases answer with
  | none => exact (hAnswer.1 ⟨x₀, s₀, hx₀⟩).elim
  | some x =>
    obtain ⟨h', hDisjoint', hMatches', hInv', hAuth', hQ⟩ := hPost x s' hAnswer
    exact DWP.ret_iff.mpr ⟨hInv', h' ∪ framed, ⟨h', framed, hDisjoint', rfl, hQ, hF⟩, hMatches', hAuth'⟩

/-- An allocation: it aborts with out-of-memory if it is not enabled. -/
theorem ispec_allocatingModify {α : Type} {modify : Heap → α → Heap → Prop} {P : IPre}
    {Q : IPost α}
    (hLocal : ∀ s h frame, P h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) →
      ∀ x s', modify s x s' →
        ∃ h', h'.Disjoint frame ∧ Fragment.Matches s' (h' ∪ frame) ∧ s'.Inv ∧
          AuthOK s' (h' ∪ frame) ∧ Q x h') :
    ispec P (Result.allocatingModify modify) Q := by
  classical
  rw [ispec_iff]
  rintro F s ⟨hInv, _, ⟨owned, framed, hDisjoint, rfl, hP, hF⟩, hMatches, hAuth⟩
  have hPost := hLocal s owned framed hP hDisjoint hMatches hInv hAuth
  unfold Result.allocatingModify
  refine DWP.vis (θ := effectWP)
    (effect := RustEffect.Input.guardedModify _ (State.checked modify))
    ⟨?_, fun answer s' hAnswer => ?_⟩
  · by_cases h : ∃ x s', modify s x s'
    · obtain ⟨x, s', hx⟩ := h
      exact ⟨some x, s', hx⟩
    · exact ⟨none, s, h, rfl⟩
  · cases answer with
    | none => exact DWP.vis (θ := effectWP) (effect := RustEffect.Input.fail .oom) rfl
    | some x =>
      obtain ⟨h', hDisjoint', hMatches', hInv', hAuth', hQ⟩ := hPost x s' hAnswer
      exact DWP.ret_iff.mpr ⟨hInv', h' ∪ framed, ⟨h', framed, hDisjoint', rfl, hQ, hF⟩, hMatches', hAuth'⟩

/-- Out-of-memory aborts are accepted. -/
@[simp]
theorem ispec_oom : ispec P (Result.oom : Result α) Q := by
  rw [ispec_iff]
  intro F s _
  exact DWP.vis (θ := effectWP) (effect := RustEffect.Input.fail .oom) rfl

theorem ispec_fail (e : Error) (hFalse : P ⊢ ⌜False⌝) : ispec P (fail e) Q :=
  fun h hP => (hFalse h hP).elim

theorem ispec_div (hFalse : P ⊢ ⌜False⌝) : ispec P (div : Result α) Q :=
  fun h hP => (hFalse h hP).elim

theorem ispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (P ∗ H) m (Q ∗+ H) := by
  rw [ispec_iff] at hTriple ⊢
  intro F s hPre
  have hSpec := hTriple (H ∗ F) s (Realizes.mono (entails_of_eq (sep_assoc_eq P H F)) hPre)
  exact hSpec.mono fun value _ =>
    Realizes.mono (entails_of_eq (sep_assoc_eq (Q value) H F).symm)

theorem ispec_frame_left {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) (H : IProp) :
    ispec (H ∗ P) m (fun value => H ∗ Q value) := by
  rw [ispec_iff] at hTriple ⊢
  intro F s hPre
  have hSwapped : Realizes (P ∗ (H ∗ F)) s :=
    Realizes.mono (entails_trans
      (sep_mono (entails_of_eq (sep_comm_eq H P)) (entails_refl F))
      (entails_of_eq (sep_assoc_eq P H F))) hPre
  refine (hTriple (H ∗ F) s hSwapped).mono fun value _ hPost => ?_
  exact Realizes.mono (entails_trans (entails_of_eq (sep_assoc_eq (Q value) H F).symm)
    (sep_mono (entails_of_eq (sep_comm_eq (Q value) H)) (entails_refl F))) hPost

/-- Mono rule used by `step`. -/
theorem ispec_mono {α : Type u} {P Pm F : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : ispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hPost : F ⊢ Qm -∗+ Q) :
    ispec P m Q := by
  have hFramed := ispec_frame hStep F
  rw [ispec_iff] at hFramed ⊢
  intro F' s hP
  have hSpec := hFramed F' s (Realizes.mono (sep_mono hPre (entails_refl F')) hP)
  exact hSpec.mono fun value _ => Realizes.mono (sep_mono
    (entails_trans (sep_mono (entails_refl _) hPost) (postWand_cancel Qm Q value)) (entails_refl F'))

/-- The rule of consequence. -/
theorem ispec_conseq {P P' : IPre} {m : Result α} {Q Q' : IPost α}
    (hTriple : ispec P' m Q') (hPre : P ⊢ P') (hPost : ∀ x, Q' x ⊢ Q x) : ispec P m Q :=
  ispec_mono hTriple (entails_trans hPre (entails_of_eq (sep_emp_r_eq _).symm))
    (postWand_intro fun x => entails_trans (entails_of_eq (sep_emp_r_eq _)) (hPost x))

/-- The conjunction of two postconditions which are realized by the same heap with the same frame
fragment. -/
private theorem realizes_iand_owns {Q₁ Q₂ F : IProp} {framed : Fragment} {s : Heap}
    (hF : F framed)
    (h₁ : Realizes (Q₁ ∗ owns framed) s) (h₂ : Realizes (Q₂ ∗ owns framed) s) :
    Realizes (iprop(Q₁ ∧ Q₂) ∗ F) s := by
  obtain ⟨hInv, _, ⟨o₁, f₁, hd₁, rfl, hQ₁, hf₁⟩, hm₁, hAuth₁⟩ := h₁
  obtain ⟨_, _, ⟨o₂, f₂, hd₂, rfl, hQ₂, hf₂⟩, hm₂, hAuth₂⟩ := h₂
  obtain ⟨r₁, hr₁, rfl⟩ := PartialCommMonoid.subheap_iff.mp hf₁
  obtain ⟨r₂, hr₂, rfl⟩ := PartialCommMonoid.subheap_iff.mp hf₂
  have hm₁' := (Fragment.matches_union _ _ _).mp hm₁
  have hm₂' := (Fragment.matches_union _ _ _).mp hm₂
  -- The owned parts, extended with the extra resources of the frames
  have hd₁' : (o₁ ∪ r₁).Disjoint framed := by
    have := (PartialCommMonoid.compatible_assoc o₁ framed r₁)
    exact Fragment.disjoint_union_left.mpr ⟨
      (Fragment.disjoint_union_right.mp hd₁).1, (hr₁.symm)⟩
  have hd₂' : (o₂ ∪ r₂).Disjoint framed :=
    Fragment.disjoint_union_left.mpr ⟨(Fragment.disjoint_union_right.mp hd₂).1, hr₂.symm⟩
  have hmo₁ : Fragment.Matches s (o₁ ∪ r₁) :=
    (Fragment.matches_union _ _ _).mpr ⟨hm₁'.1, ((Fragment.matches_union _ _ _).mp hm₁'.2).2⟩
  have hmo₂ : Fragment.Matches s (o₂ ∪ r₂) :=
    (Fragment.matches_union _ _ _).mpr ⟨hm₂'.1, ((Fragment.matches_union _ _ _).mp hm₂'.2).2⟩
  have hdo₁ : o₁.Disjoint r₁ := (Fragment.disjoint_union_right.mp hd₁).2
  have hdo₂ : o₂.Disjoint r₂ := (Fragment.disjoint_union_right.mp hd₂).2
  obtain ⟨o, ho, hdo, hmo, hsub₁, hsub₂⟩ := Fragment.join_of_matches hmo₁ hmo₂ hd₁' hd₂'
  refine ⟨hInv, o ∪ framed, ⟨o, framed, hdo, rfl,
    ⟨Q₁.up_closed hQ₁ ((PartialCommMonoid.Subheap.union_left hdo₁).trans hsub₁),
     Q₂.up_closed hQ₂ ((PartialCommMonoid.Subheap.union_left hdo₂).trans hsub₂)⟩, hF⟩,
    (Fragment.matches_union _ _ _).mpr ⟨hmo, ((Fragment.matches_union _ _ _).mp hm₁'.2).1⟩, ?_⟩
  intro base size bptr hc
  rw [ho] at hc
  rcases hc with ((hc | hc) | (hc | hc)) | hc
  · exact hAuth₁ base size bptr (Or.inl hc)
  · exact hAuth₁ base size bptr (Or.inr (Or.inr hc))
  · exact hAuth₂ base size bptr (Or.inl hc)
  · exact hAuth₂ base size bptr (Or.inr (Or.inr hc))
  · exact hAuth₁ base size bptr (Or.inr (Or.inl hc))

theorem ispec_and {α : Type u} {P : IPre} {m : Result α} {Q₁ Q₂ : IPost α}
    (h₁ : ispec P m Q₁) (h₂ : ispec P m Q₂) :
    ispec P m (fun value => iprop(Q₁ value ∧ Q₂ value)) := by
  rw [ispec_iff] at h₁ h₂ ⊢
  rintro F s ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, hF⟩, hMatches, hAuth⟩
  have hPre : Realizes (P ∗ owns framed) s :=
    ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, PartialCommMonoid.Subheap.refl framed⟩, hMatches, hAuth⟩
  have hBoth := DWP.and_iff.mpr ⟨h₁ (owns framed) s hPre, h₂ (owns framed) s hPre⟩
  exact hBoth.mono fun _ _ hPost => realizes_iand_owns hF hPost.1 hPost.2

theorem ispec_and_dispec {α : Type u} {P : IPre} {m : Result α} {Q₁ Q₂ : IPost α}
    (h₁ : ispec P m Q₁) (h₂ : dispec P m Q₂) :
    ispec P m (fun value => iprop(Q₁ value ∧ Q₂ value)) := by
  rw [ispec_iff] at h₁ ⊢
  rw [dispec_iff] at h₂
  rintro F s ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, hF⟩, hMatches, hAuth⟩
  have hPre : Realizes (P ∗ owns framed) s :=
    ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, PartialCommMonoid.Subheap.refl framed⟩, hMatches, hAuth⟩
  have hBoth := DWP.and_partial (h₁ (owns framed) s hPre) (h₂ (owns framed) s hPre)
  exact hBoth.mono fun _ _ hPost => realizes_iand_owns hF hPost.1 hPost.2

/-- Bind rule used by `step`. -/
theorem ispec_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β} {m : Result α} {Qm : IPost α}
    (hStep : ispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, ispec (Qm value ∗ F) (next value) Q) :
    ispec P (Aeneas.Std.bind m next) Q := by
  have hFirst : ispec P m (Qm ∗+ F) :=
    ispec_mono hStep hPre (postWand_intro fun _ => entails_refl _)
  simp only [ispec_iff] at hFirst hNext ⊢
  intro frame s hP
  apply (hFirst frame s hP).bind
  intro value s' hPost
  exact hNext value frame s' (Realizes.mono (entails_of_eq rfl) hPost)

/-! ### Failure

`ifails P m`: `m` never succeeds from a heap which realizes `P` with some frame (it fails, or
diverges), so that it has no total-correctness specification with precondition `P`
(`not_ispec_of_ifails`), provided that `P` is realizable.

As running out of memory satisfies every specification, a program which may run out of memory
(i.e., which allocates) can't be shown to fail with `ifails`: its heap may be full. The rule for
`bind` with a specification of the prefix (`ifails_bind`) thus requires that the prefix does not
satisfy its postconditions vacuously (by running out of memory). To show that an allocating
program fails, exhibit a failing execution instead (see `tests/lean/SafeUnsafe`). -/

def ifails {α : Type u} (P : IPre) (m : Result α) : Prop :=
  ∀ F s (Q : α → Heap → Prop), Realizes (P ∗ F) s → ¬ DWP effectWP m Q s

theorem not_ispec_of_ifails {α : Type u} {P : IPre} {m : Result α} {Q : IPost α} {s : Heap}
    (hFails : ifails P m) (hP : Realizes P s) : ¬ ispec P m Q := fun hTriple =>
  hFails emp s _ (realizes_sep_emp.mpr hP) ((ispec_iff.mp hTriple) emp s (realizes_sep_emp.mpr hP))

/-- A program which fails from `emp` has no specification from `emp`. -/
theorem not_ispec_of_ifails_emp {α : Type u} {m : Result α} {Q : IPost α}
    (hFails : ifails emp m) : ¬ ispec emp m Q :=
  not_ispec_of_ifails hFails realizes_emp_empty

/-- Sequencing: the prefix `m` has a specification, which it does not satisfy vacuously
(`hProgress`: it does not run out of memory in every execution), and the continuation fails from its
postcondition. -/
theorem ifails_bind {α : Type u} {β : Type v} {P : IPre} {m : Result α} {R : IPost α}
    {k : α → Result β} (hm : ispec P m R)
    (hProgress : ∀ F s (Q : α → Heap → Prop), Realizes (P ∗ F) s → DWP effectWP m Q s →
      ∃ x s', Q x s')
    (hk : ∀ x, ifails (R x) (k x)) :
    ifails P (Aeneas.Std.bind m k) := by
  intro F s Q hPre hDwp
  obtain ⟨x, s', hR, hK⟩ := hProgress F s _ hPre
    (DWP.and_iff.mpr ⟨(ispec_iff.mp hm) F s hPre, DWP.bind_inv hDwp⟩)
  exact hk x F s' Q hR hK

theorem ifails_bind_left {α : Type u} {β : Type v} {P : IPre} {m : Result α}
    {k : α → Result β} (hm : ifails P m) : ifails P (Aeneas.Std.bind m k) :=
  fun F s _ hPre hDwp => hm F s _ hPre (DWP.bind_inv hDwp)

theorem ifails_mono {α : Type u} {P P' : IPre} {m : Result α} (hPre : P ⊢ P')
    (hFails : ifails P' m) : ifails P m :=
  fun F s Q hP => hFails F s Q (Realizes.mono (sep_mono hPre (entails_refl F)) hP)

theorem ifails_ipure {α : Type u} {p : Prop} {H : IPre} {m : Result α}
    (hFails : p → ifails H m) : ifails (⌜p⌝ ∗ H) m := fun F s Q hPre => by
  obtain ⟨hInv, h, hH, hMatches, hAuth⟩ := hPre
  have ⟨hp, hHF⟩ := (sep_pure_l p (H ∗ F) h).mp ((entails_of_eq (sep_assoc_eq _ _ _)) h hH)
  exact hFails hp F s Q ⟨hInv, h, hHF, hMatches, hAuth⟩

/-- Failures other than running out of memory. -/
theorem ifails_fail {α : Type u} {P : IPre} {e : Error} (he : e ≠ .oom) :
    ifails P (fail e : Result α) :=
  fun _ _ _ _ hDwp => he hDwp.vis_view

/-- A heap operation which is never enabled from the heaps which realize the precondition (with any
frame) fails. -/
theorem ifails_guardedModify {α : Type} {modify : Heap → α → Heap → Prop} {P : IPre}
    (hNot : ∀ s h frame, P h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) → ¬ ∃ x s', modify s x s') :
    ifails P (Result.guardedModify modify) := by
  rintro F s Q ⟨hInv, _, ⟨owned, framed, hDisjoint, rfl, hP, -⟩, hMatches, hAuth⟩ hDwp
  exact hNot s owned framed hP hDisjoint hMatches hInv hAuth hDwp.vis_view.1

/-- A checked heap operation which is never enabled from the heaps which realize the precondition
(with any frame) fails with undefined behavior. -/
theorem ifails_checkedModify {α : Type} {modify : Heap → α → Heap → Prop} {P : IPre}
    (hNot : ∀ s h frame, P h → h.Disjoint frame → Fragment.Matches s (h ∪ frame) → s.Inv →
      AuthOK s (h ∪ frame) → ¬ ∃ x s', modify s x s') :
    ifails P (Result.checkedModify modify) := by
  rintro F s Q ⟨hInv, _, ⟨owned, framed, hDisjoint, rfl, hP, -⟩, hMatches, hAuth⟩ hDwp
  unfold Result.checkedModify at hDwp
  have hNone : State.checked modify s none s :=
    ⟨hNot s owned framed hP hDisjoint hMatches hInv hAuth, rfl⟩
  have hNext := hDwp.vis_view.2 none s hNone
  exact Error.noConfusion (hNext.vis_view : Error.undef = Error.oom)

theorem ispec_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    ispec (⌜P⌝ ∗ H) m Q ↔ (P → ispec H m Q) := by
  constructor
  · intro hTriple hP
    exact ispec_mono hTriple (entails_trans (pure_sep_intro H hP) (entails_of_eq (sep_emp_r_eq _).symm))
      (postWand_intro fun _ => (entails_of_eq (sep_emp_r_eq _)))
  · intro hTriple owned hOwned
    have ⟨hP, hH⟩ := (sep_pure_l P H owned).mp hOwned
    exact hTriple hP owned hH

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
  · intro hTriple h ⟨x, hJ⟩
    exact hTriple x h hJ

/-- Case split on an `if` program. `split` (and `split_ifs`) run `simp` on the whole goal and can
exceed the maximum number of steps on large programs (for instance the twenty-branch case analysis
of `ryu::pretty::format32`); `repeat' (apply ispec_ite <;> intro)` splits them without traversing
the branches. -/
theorem ispec_ite {P : IPre} {c : Prop} [Decidable c] {a b : Result α} {Q : IPost α}
    (h1 : c → ispec P a Q) (h2 : ¬c → ispec P b Q) : ispec P (if c then a else b) Q := by
  by_cases h : c
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 h

private theorem dispec_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) {s : Heap} (hPre : Realizes P s) :
    rawIwp false m Q s := by
  rw [dispec_iff] at hTriple
  have hSpec := hTriple emp s (realizes_sep_emp.mpr hPre)
  exact hSpec.mono fun value _ => Realizes.mono (sep_elim_right (Q value) emp)

private theorem ispec_apply {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : ispec P m Q) {s : Heap} (hPre : Realizes P s) :
    rawIwp true m Q s := by
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp s (realizes_sep_emp.mpr hPre)
  exact hSpec.mono fun value _ => Realizes.mono (sep_elim_right (Q value) emp)

theorem dispec_ok {α : Type u} {P : IPre} {Q : IPost α} (x : α) (hPost : P ⊢ Q x) :
    dispec P (ok x) Q := by
  rw [dispec_iff]
  intro F s hPre
  exact DWLP.ret_iff.mpr (Realizes.mono (sep_mono hPost (entails_refl F)) hPre)

@[simp]
theorem dispec_oom : dispec P (Result.oom : Result α) Q :=
  ispec_dispec ispec_oom

theorem dispec_fail {P : IPre} {Q : IPost α} (e : Error) (hFalse : P ⊢ ⌜False⌝) :
    dispec P (fail e) Q :=
  fun h hP => (hFalse h hP).elim

theorem dispec_div {P : IPre} {Q : IPost α} :
    dispec P (div : Result α) Q := by
  rw [dispec_iff]
  intro _ _ _
  exact DWLP.div

theorem dispec_frame {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) (H : IProp) : dispec (P ∗ H) m (Q ∗+ H) := by
  rw [dispec_iff] at hTriple ⊢
  intro F s hPre
  have hSpec := hTriple (H ∗ F) s (Realizes.mono (entails_of_eq (sep_assoc_eq P H F)) hPre)
  exact hSpec.mono fun value _ =>
    Realizes.mono (entails_of_eq (sep_assoc_eq (Q value) H F).symm)

/-- Mono rule used by `step`. -/
theorem dispec_mono {α : Type u} {P Pm F : IPre} {Q : IPost α} {m : Result α} {Qm : IPost α}
    (hStep : dispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hPost : F ⊢ Qm -∗+ Q) :
    dispec P m Q := by
  have hFramed := dispec_frame hStep F
  rw [dispec_iff] at hFramed ⊢
  intro F' s hP
  have hSpec := hFramed F' s (Realizes.mono (sep_mono hPre (entails_refl F')) hP)
  exact hSpec.mono fun value _ => Realizes.mono (sep_mono
    (entails_trans (sep_mono (entails_refl _) hPost) (postWand_cancel Qm Q value)) (entails_refl F'))

theorem dispec_and {α : Type u} {P : IPre} {m : Result α} {Q₁ Q₂ : IPost α}
    (h₁ : dispec P m Q₁) (h₂ : dispec P m Q₂) :
    dispec P m (fun value => iprop(Q₁ value ∧ Q₂ value)) := by
  rw [dispec_iff] at h₁ h₂ ⊢
  rintro F s ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, hF⟩, hMatches, hAuth⟩
  have hPre : Realizes (P ∗ owns framed) s :=
    ⟨hInv, _, ⟨owned, framed, hCompatible, rfl, hP, PartialCommMonoid.Subheap.refl framed⟩, hMatches, hAuth⟩
  have hBoth := DWLP.and_iff.mpr ⟨h₁ (owns framed) s hPre, h₂ (owns framed) s hPre⟩
  exact hBoth.mono fun _ _ hPost => realizes_iand_owns hF hPost.1 hPost.2

theorem dispec_bind {α : Type u} {β : Type v} {P Pm F : IPre}
    {next : α → Result β} {Q : IPost β} {m : Result α} {Qm : IPost α}
    (hStep : dispec Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, dispec (Qm value ∗ F) (next value) Q) :
    dispec P (Aeneas.Std.bind m next) Q := by
  have hFirst : dispec P m (Qm ∗+ F) :=
    dispec_mono hStep hPre (postWand_intro fun _ => entails_refl _)
  simp only [dispec_iff] at hFirst hNext ⊢
  intro frame s hP
  apply (hFirst frame s hP).bind
  intro value s' hPost
  exact hNext value frame s' (Realizes.mono (entails_of_eq rfl) hPost)

theorem dispec_ipure {P : Prop} {H : IPre} {m : Result α} {Q : IPost α} :
    dispec (⌜P⌝ ∗ H) m Q ↔ (P → dispec H m Q) := by
  constructor
  · intro hTriple hP
    exact dispec_mono hTriple (entails_trans (pure_sep_intro H hP) (entails_of_eq (sep_emp_r_eq _).symm))
      (postWand_intro fun _ => (entails_of_eq (sep_emp_r_eq _)))
  · intro hTriple owned hOwned
    have ⟨hP, hH⟩ := (sep_pure_l P H owned).mp hOwned
    exact hTriple hP owned hH

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
  · intro hTriple h ⟨x, hJ⟩
    exact hTriple x h hJ

theorem dispec_admissible_pi {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible
      (fun f : ι → Result α => ∀ x, dispec (P x) (f x) (Q x)) :=
  Lean.Order.admissible_pi_apply (fun x m => dispec (P x) m (Q x))
    fun x => dispec_admissible (P x) (Q x)

theorem dispec_admissible_forall {ι : Type v} {α : Type u} (P : ι → IPre) (Q : ι → IPost α) :
    Lean.Order.admissible (fun m : Result α => ∀ x, dispec (P x) m (Q x)) :=
  Lean.Order.admissible_pi _ fun x => dispec_admissible (P x) (Q x)

attribute [simp] entails_emp_ipure_iff

/-! ### Pure specifications

The empty heap realizes `emp`: the pure specifications are characterized exactly. -/

private theorem spec_apply {m : Result α} {p : Post α} (h : spec m p) :
    DWP effectWP m (fun value s' => Realizes ⌜p value⌝ s') Heap.empty :=
  ispec_apply h realizes_emp_empty

private theorem dspec_apply {m : Result α} {p : Post α} (h : dspec m p) :
    DWLP effectWP m (fun value s' => Realizes ⌜p value⌝ s') Heap.empty :=
  dispec_apply h realizes_emp_empty

@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x :=
  ⟨fun h => (DWP.ret_iff.mp (spec_apply h)).pure,
   fun hp => ispec_ok x ((entails_emp_ipure_iff (p x)).mpr hp)⟩

@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ e = .oom := by
  constructor
  · intro h
    exact DWP.vis_view (spec_apply h)
  · rintro rfl
    exact ispec_oom

@[simp]
theorem spec_oom : spec (Result.oom : Result α) p := ispec_oom

@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False :=
  ⟨fun h => DWP.div_false (spec_apply h), False.elim⟩

/-! ### `spec_*` for tuple posts

Needed now with the new `uncurry`-based pattern matching. -/

@[simp, grind =, agrind =]
theorem spec_ok_pair {α β} (a : α) (b : β) (f : α → β → Prop) :
    spec (ok (a, b)) (uncurry f) ↔ f a b := by
  simp [spec_ok]

@[simp, grind =, agrind =]
theorem spec_fail_pair (e : Error) (f : α → β → Prop) :
    spec (fail e) (uncurry f) ↔ e = .oom := spec_fail e

@[simp, grind =, agrind =]
theorem spec_div_pair (f : α → β → Prop) :
    spec div (uncurry f) ↔ False := by simp

/-- Mono rule used by `step`. -/
theorem spec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
    (∀ x, P₀ x → P₁ x) → spec m P₁ :=
  fun hMonPost => ispec_mono h (entails_of_eq (sep_emp_r_eq _).symm)
    (postWand_intro fun value => entails_trans (entails_of_eq (sep_emp_r_eq _)) fun _ => hMonPost value)

theorem spec_and {m : Result α} {p q : Post α} (h₁ : spec m p) (h₂ : spec m q) :
    spec m (fun value => p value ∧ q value) :=
  ispec_and h₁ h₂

theorem spec_and_dspec {m : Result α} {p q : Post α} (h₁ : spec m p) (h₂ : dspec m q) :
    spec m (fun value => p value ∧ q value) :=
  ispec_and_dispec h₁ h₂

/-- Bind rule used by `step`. It is stated on `Std.bind` rather than on `>>=`, which is
what a translated program binds with. -/
theorem spec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    spec m Pₘ →
    (∀ x, Pₘ x → spec (k x) Pₖ) →
    spec (Std.bind m k) Pₖ :=
  fun hm hk =>
    ispec_bind hm (entails_of_eq (sep_emp_r_eq emp).symm) fun value =>
      ispec_mono (ispec_ipure_iff.mpr (hk value)) (entails_refl _)
        (postWand_intro fun _ => (entails_of_eq (sep_emp_r_eq _)))

-- `dspec` theorems
@[simp, grind =, agrind =]
theorem dspec_ok (x : α) : dspec (ok x) p ↔ p x :=
  ⟨fun h => (DWLP.ret_iff.mp (dspec_apply h)).pure,
   fun hp => dispec_ok x ((entails_emp_ipure_iff (p x)).mpr hp)⟩

@[simp, grind =, agrind =]
theorem dspec_fail (e : Error) : dspec (fail e) p ↔ e = .oom := by
  constructor
  · intro h
    exact DWLP.vis_view (dspec_apply h)
  · rintro rfl
    exact dispec_oom

@[simp, grind =, agrind =]
theorem dspec_div : dspec (div : Result α) p ↔ True :=
  iff_true_intro dispec_div

theorem dspec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : dspec m P₀):
    (∀ x, P₀ x → P₁ x) → dspec m P₁ :=
  fun hMonPost => dispec_mono h (entails_of_eq (sep_emp_r_eq _).symm)
    (postWand_intro fun value => entails_trans (entails_of_eq (sep_emp_r_eq _)) fun _ => hMonPost value)

theorem dspec_and {m : Result α} {p q : Post α} (h₁ : dspec m p) (h₂ : dspec m q) :
    dspec m (fun value => p value ∧ q value) :=
  dispec_and h₁ h₂

theorem dspec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
    dspec m Pₘ →
    (∀ x, Pₘ x → dspec (k x) Pₖ) →
    dspec (Std.bind m k) Pₖ :=
  fun hm hk =>
    dispec_bind hm (entails_of_eq (sep_emp_r_eq emp).symm) fun value =>
      dispec_mono (dispec_ipure_iff.mpr (hk value)) (entails_refl _)
        (postWand_intro fun _ => (entails_of_eq (sep_emp_r_eq _)))

end ResultImplementation

end Aeneas.Std.WP

namespace Aeneas

open Aeneas.Std WP Result

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

/-- `⦃P⦄ m ⦃ binders => Q ⦄`, or `⦃P⦄ m ⦃ Q ⦄` for a constant postcondition `fun _ => Q`. Any
other postcondition (e.g. a variable `Q : IPost α`) is left to the default `ispec P m Q`: the
binder-less notation would read it back as `fun _ => Q`. -/
private meta def delabSLISpecPost (pre monadExpr : Term) (isPartial : Bool) :
    DelabM Term := do
  let post := (← getExpr).consumeMData
  let (binders, body) ←
    if post.isLambda && !post.bindingBody!.hasLooseBVars then
      pure (#[], ← withBindingBodyUnusedName fun _ => delab)
    else if post.isLambda || isPostBinderWrapper post then
      delabPostBinders
    else failure
  if h : binders.size > 0 then
    if isPartial then
      `(⦃$pre⦄ $monadExpr ⦃ $(binders[0]) $(binders.drop 1)* => $body⦄div)
    else
      `(⦃$pre⦄ $monadExpr ⦃ $(binders[0]) $(binders.drop 1)* => $body⦄)
  else if isPartial then
    `(⦃$pre⦄ $monadExpr ⦃ $body⦄div)
  else
    `(⦃$pre⦄ $monadExpr ⦃ $body⦄)

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

/-! ### Separation-logic postconditions without binders -/

-- not a lambda: printed as an application, since `⦃ P ⦄ m ⦃ Q ⦄` would mean `fun _ => Q`
/-- error: unsolved goals
P : SepLogic.IProp
m : Result ℕ
Q : SepLogic.IPost ℕ
⊢ ispec P m Q -/
#guard_msgs in
example (P : SepLogic.IProp) (m : Result Nat) (Q : SepLogic.IPost Nat) : Std.WP.ispec P m Q := by
  done

/-- error: unsolved goals
P Q : SepLogic.IProp
m : Result ℕ
⊢ ⦃ P ⦄
    m
    ⦃ Q ⦄ -/
#guard_msgs in example (P Q : SepLogic.IProp) (m : Result Nat) : ⦃ P ⦄ m ⦃ Q ⦄ := by done

/-- error: unsolved goals
P Q : SepLogic.IProp
m : Result ℕ
⊢ ⦃ P ⦄
    m
    ⦃ Q ⦄div -/
#guard_msgs in example (P Q : SepLogic.IProp) (m : Result Nat) : ⦃ P ⦄ m ⦃ Q ⦄div := by done
end Aeneas

namespace Aeneas.Std.WP

open Std Result
open Aeneas.Data.Coinductive
open Lean.Order
open Aeneas.SepLogic

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- Keeps pure returns in the pure judgment, so `step` introduces no spatial entailment for them. -/
theorem ok_spec (value : α) :
    spec (Result.ok value) (fun result => result = value) :=
  ispec_ok value fun _ _ => rfl

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

namespace Aeneas.Std.WP

/-!
# mvcgen
-/

open Std Result
open Std.Do

def _root_.Aeneas.Std.Result.terminates {α : Type u} (x : Result α) : Prop :=
  spec x (fun _ => True)

/-- The `Std.Do` view of `Result` used by `mvcgen`: `x` satisfies `Q` when it terminates in `Q.1`
(`spec`), or, if `Q.2.1` holds, when its terminating runs end in `Q.1` (`dspec`, which allows
divergence). The exception layer is `PUnit`, so postconditions cannot mention which `Error` was
raised. There is no `WPMonad` instance (hence no `Result.of_wp`, nor the `Std.Do` lemmas that
require one): `spec` quantifies over all heaps, so `wp (x >>= f)` is not `wp x` followed by
`wp (f ·)`. For example `into_raw v >>= read` satisfies `spec`, but `read p` does not for every `p`. -/
instance Result.instWP : WP Result.{u} (.except PUnit .pure) where
  wp x := {
    trans Q := ⟨spec x (fun a => (Q.1 a).down) ∨
      ((Q.2.1 ⟨⟩).down ∧ dspec x (fun a => (Q.1 a).down))⟩
    conjunctiveRaw Q₁ Q₂ := by
      simp only [SPred.bientails_nil, SPred.and_nil, ExceptConds.and]
      constructor
      · rintro (h | ⟨⟨d₁, d₂⟩, h⟩)
        · exact ⟨.inl (spec_mono h fun _ h => h.1), .inl (spec_mono h fun _ h => h.2)⟩
        · exact ⟨.inr ⟨d₁, dspec_mono h fun _ h => h.1⟩, .inr ⟨d₂, dspec_mono h fun _ h => h.2⟩⟩
      · rintro ⟨h₁ | ⟨d₁, h₁⟩, h₂ | ⟨d₂, h₂⟩⟩
        · exact .inl (spec_and h₁ h₂)
        · exact .inl (spec_and_dspec h₁ h₂)
        · exact .inl (spec_mono (spec_and_dspec h₂ h₁) fun _ h => ⟨h.2, h.1⟩)
        · exact .inr ⟨⟨d₁, d₂⟩, dspec_and h₁ h₂⟩
  }

@[spec]
theorem Result.ok_mvcgen_spec {α : Type u} {a : α} {Q : PostCond α (.except PUnit .pure)} :
    Triple (Result.ok a) (Q.1 a) Q :=
  fun h => .inl ((spec_ok a).mpr h)

@[spec]
theorem Result.pure_mvcgen_spec {α : Type u} {a : α} {Q : PostCond α (.except PUnit .pure)} :
    Triple (pure a : Result α) (Q.1 a) Q :=
  Result.ok_mvcgen_spec

@[spec]
theorem Result.fail_mvcgen_spec {α : Type u} {e : Error} {Q : PostCond α (.except PUnit .pure)} :
    Triple (Result.fail e : Result α) ⌜False⌝ Q :=
  False.elim

@[spec]
theorem Result.div_mvcgen_spec {α : Type u} {Q : PostCond α (.except PUnit .pure)} :
    Triple (ps := .except PUnit .pure) (Result.div : Result α) (Q.2.1 ⟨⟩) Q :=
  fun h => .inr ⟨h, dspec_div.mpr trivial⟩

theorem Result.bind_wp {α β : Type u} {x : Result α} {f : α → Result β}
    {Q : PostCond β (.except PUnit .pure)} :
    (wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)).down → (wp⟦Std.bind x f⟧ Q).down := by
  rintro (h | ⟨d, h⟩)
  · by_cases d : (Q.2.1 ⟨⟩).down
    · refine .inr ⟨d, dspec_bind (spec_dspec _ _ _ h) fun _ h => ?_⟩
      exact h.elim (spec_dspec _ _ _) And.right
    · exact .inl (spec_bind h fun _ h => h.resolve_right fun h => d h.1)
  · exact .inr ⟨d, dspec_bind h fun _ h => h.elim (spec_dspec _ _ _) And.right⟩

@[spec]
theorem Result.std_bind_mvcgen_spec {α β : Type u} {x : Result α} {f : α → Result β}
    {Q : PostCond β (.except PUnit .pure)} :
    Triple (Std.bind x f) (wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)) Q :=
  Result.bind_wp

@[spec]
theorem Result.bind_mvcgen_spec {α β : Type u} {x : Result α} {f : α → Result β}
    {Q : PostCond β (.except PUnit .pure)} :
    Triple (x >>= f) (wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)) Q :=
  Result.bind_wp


/-- Lift an Aeneas step spec to an mvcgen-compatible `Triple`. -/
theorem spec_to_mvcgen {α : Type u} {x : Result α} {Q : α → Prop}
    (h : spec x Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ :=
  fun _ => .inl h

theorem dspec_to_mvcgen {α : Type u} {x : Result α} {Q : α → Prop}
    (h : dspec x Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ (fun r => ⌜ Q r ⌝, fun _ => ⌜ ¬ x.terminates ⌝, ⟨⟩) ⦄ := by
  intro _
  by_cases hTerm : x.terminates
  · exact .inl (spec_mono (spec_and_dspec hTerm h) fun _ h => h.2)
  · exact .inr ⟨hTerm, h⟩

end Aeneas.Std.WP
