module

public import Aeneas.Std.Heap.Allocation
public import Aeneas.Std.Primitives
public import Aeneas.Data.Coinductive.ITreeWP.DWP
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Primitives

@[expose] public section

namespace Aeneas.Std.HeapWP

open Aeneas.Data.Coinductive SepLogic

unseal Result

/-- Heap effects require an enabled transition and accept every possible successor.
Failure is rejected; the ordinary effect-free WP is unchanged. -/
def effectWP : EffectWP RustEffect where
  State := State.{0}
  wp effect C s :=
    match effect with
    | .guardedModify _ modify =>
      (∃ x s', modify s x s') ∧ ∀ x s', modify s x s' → C ⟨x⟩ s'
    | .fail _ => False

instance : effectWP.Monotonic where
  wp_monotonic := by
    intro effect C C' h s he
    cases effect
    · exact ⟨he.1, fun x s' hx => h _ _ (he.2 x s' hx)⟩
    · exact he

instance : effectWP.Conjunctive where
  wp_conj := by
    intro effect s demands hne hall
    cases effect
    · obtain ⟨C, hC⟩ := hne
      exact ⟨(hall C hC).1, fun x s' hx C' hC' => (hall C' hC').2 x s' hx⟩
    · obtain ⟨C, hC⟩ := hne
      exact hall C hC

instance : effectWP.ExcludedMiracle where
  wp_excludedMiracle := by
    intro effect s he
    cases effect
    · obtain ⟨x, s', hx⟩ := he.1
      exact he.2 x s' hx
    · exact he

/-- Successful termination of an actual `Result` computation with a heap postcondition. -/
def Spec (c : Result α) (Q : α → State.{0} → Prop) (s : State.{0}) : Prop :=
  DWP effectWP c Q s

theorem Spec.pure (x : α) (Q : α → State.{0} → Prop) (s : State.{0}) :
    Spec (pure x) Q s ↔ Q x s :=
  DWP.ret_iff

theorem Spec.bind {c : Result α} {k : α → Result β}
    (hc : Spec c Q s) (hk : ∀ x s', Q x s' → Spec (k x) R s') :
    Spec (c >>= k) R s :=
  DWP.bind hc hk

theorem Spec.exists (hc : Spec c Q s) : ∃ x s', Q x s' :=
  DWP.exists hc

theorem Spec.fail (e : Error) : ¬ Spec (Result.fail e : Result α) Q s := by
  intro h
  exact DWP.vis_view h

theorem Spec.div : ¬ Spec (Result.div : Result α) Q s :=
  DWP.div_false

theorem Spec.guardedModify {modify : State.{0} → α → State.{0} → Prop} :
    Spec (Result.guardedModify modify) Q s ↔
      (∃ x s', modify s x s') ∧ ∀ x s', modify s x s' → Q x s' := by
  constructor
  · intro h
    obtain ⟨hsafe, hpost⟩ := DWP.vis_view h
    exact ⟨hsafe, fun x s' hx => DWP.ret_iff.mp (hpost x s' hx)⟩
  · rintro ⟨hsafe, hpost⟩
    exact DWP.vis ⟨hsafe, fun x s' hx => DWP.ret_iff.mpr (hpost x s' hx)⟩

/-- A framed separation contract for the generated computation itself. -/
def Triple (P : Assertion.{0}) (c : Result α) (Q : α → Assertion.{0}) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    Spec c (fun x s' => ∃ h', h'.Disjoint F ∧
      Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h') s

theorem Triple.guardedModify {modify : State.{0} → α → State.{0} → Prop}
    (ht : SepLogic.Triple P modify Q) :
    Triple P (Result.guardedModify modify) Q := by
  intro h F s hp hd hm hi
  exact Spec.guardedModify.mpr (ht h F s hp hd hm hi)

theorem Triple.pure (P : Assertion.{0}) (x : α) :
    Triple P (pure x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi
  exact Spec.pure _ _ _ |>.mpr ⟨h, hd, hm, hi, rfl, hp⟩

theorem Triple.bind {c : Result α} {k : α → Result β}
    (hc : Triple P c Q) (hk : ∀ x, Triple (Q x) (k x) R) :
    Triple P (c >>= k) R := by
  intro h F s hp hd hm hi
  apply Spec.bind (hc h F s hp hd hm hi)
  rintro x s' ⟨h', hd', hm', hi', hq⟩
  exact hk x h' F s' hq hd' hm' hi'

theorem Triple.conseq (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : Triple P' c Q') : Triple P c Q := by
  intro h F s hP hd hm hi
  exact DWP.mono (ht h F s (hp h hP) hd hm hi) fun x s' ⟨h', hd', hm', hi', hQ⟩ =>
    ⟨h', hd', hm', hi', hq x h' hQ⟩

theorem Triple.pure_pre (ht : A → Triple P c Q) :
    Triple (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi
  exact ht ha h F s hp hd hm hi

theorem frame (ht : Triple P c Q) :
    Triple (sep P R) c (fun x => sep (Q x) R) := by
  intro h F s ⟨a, b, hab, he, hp, hr⟩ hf hm hi
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  have ht' := ht a (b ∪ F) s hp (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi
  apply DWP.mono ht'
  rintro x s' ⟨a', hd, hm', hi', hq⟩
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

end Aeneas.Std.HeapWP
