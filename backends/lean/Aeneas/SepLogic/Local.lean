module

public import Aeneas.SepLogic.Bytes
public import Aeneas.Std.Heap

/-! Local heap operations: the operations which, from every heap which matches a fragment of the
precondition together with a frame fragment, are enabled and keep the frame. These are the facts
about the operations of the byte heap from which the specifications of the raw-pointer functions are
proved (see `LocalOp.ispec_checkedModify`). -/

@[expose] public section

namespace Aeneas.Std.Bytes

open Aeneas.SepLogic

universe w

def empty : (Fragment → Prop) := fun h => h = ∅

def sep (P Q : (Fragment → Prop)) : (Fragment → Prop) :=
  fun h => ∃ a b, a.Disjoint b ∧ h = a ∪ b ∧ P a ∧ Q b

/-- The separating conjunction of predicates on fragments (they hold of disjoint parts). -/
infixr:35 " ∗ᵇ " => sep

theorem sep_comm (P Q : (Fragment → Prop)) (h : Fragment) : sep P Q h ↔ sep Q P h := by
  constructor
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩

theorem sep_assoc (P Q R : (Fragment → Prop)) (h : Fragment) :
    sep (sep P Q) R h ↔ sep P (sep Q R) h := by
  constructor
  · rintro ⟨ab, c, hd, rfl, ⟨a, b, hab, rfl, hp, hq⟩, hr⟩
    obtain ⟨hac, hbc⟩ := Fragment.disjoint_union_left.mp hd
    exact ⟨a, b ∪ c, Fragment.disjoint_union_right.mpr ⟨hab, hac⟩,
      Fragment.union_assoc _ _ _, hp, b, c, hbc, rfl, hq, hr⟩
  · rintro ⟨a, bc, hd, rfl, hp, ⟨b, c, hbc, rfl, hq, hr⟩⟩
    obtain ⟨hab, hac⟩ := Fragment.disjoint_union_right.mp hd
    exact ⟨a ∪ b, c, Fragment.disjoint_union_left.mpr ⟨hac, hbc⟩,
      (Fragment.union_assoc _ _ _).symm, ⟨a, b, hab, rfl, hp, hq⟩, hr⟩

theorem sep_mono {P P' Q Q' : (Fragment → Prop)}
    (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) {h : Fragment} :
    sep P Q h → sep P' Q' h := by
  rintro ⟨a, b, hd, he, ha, hb⟩
  exact ⟨a, b, hd, he, hp _ ha, hq _ hb⟩

theorem sep_and_left (A : Prop) (P Q : (Fragment → Prop)) (h : Fragment) :
    sep (fun a => A ∧ P a) Q h ↔ A ∧ sep P Q h := by
  constructor
  · rintro ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩
    exact ⟨ha, a, b, hd, he, hp, hq⟩
  · rintro ⟨ha, a, b, hd, he, hp, hq⟩
    exact ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩

theorem sep_empty_left (P : (Fragment → Prop)) (h : Fragment) :
    sep empty P h ↔ P h := by
  constructor
  · rintro ⟨a, b, _, he, rfl, hp⟩
    have he' : h = b := by simpa using he
    simpa [he'] using hp
  · intro hp
    exact ⟨∅, h, Fragment.disjoint_empty_left h, by simp, rfl, hp⟩

theorem sep_empty_right (P : (Fragment → Prop)) (h : Fragment) :
    sep P empty h ↔ P h :=
  (sep_comm P empty h).trans (sep_empty_left P h)

abbrev Cmd (α : Type w) := Heap → α → Heap → Prop

def Cmd.pure (x : α) : Cmd α := fun s y s' => y = x ∧ s' = s
def Cmd.bind (c : Cmd α) (k : α → Cmd β) : Cmd β :=
  fun s y s'' => ∃ x s', c s x s' ∧ k x s' y s''

/-- Successor existence plus demonic safety, for every matching disjoint frame.
Dropped resources remain in the physical heap but are no longer owned. -/
def LocalOp (P : (Fragment → Prop)) (c : Cmd α)
    (Q : α → (Fragment → Prop)) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    (∃ x s', c s x s') ∧
    ∀ x s', c s x s' →
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h'

/-- Input-state contract for operations whose enabledness depends on compatible
placement, symbolic pointer metadata, or return authority. It still quantifies
over every matching indexed frame and every permitted successor. -/
def LocalAt (P : (Fragment → Prop)) (c : Cmd α) (Q : α → (Fragment → Prop)) (s : Heap) : Prop :=
  ∀ h F, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    (∃ x s', c s x s') ∧
    ∀ x s', c s x s' →
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h'

theorem LocalOp.at {P : (Fragment → Prop)} {c : Cmd α} {Q : α → (Fragment → Prop)}
    (ht : LocalOp P c Q) (s : Heap) : LocalAt P c Q s :=
  fun h F hp hd hm hi => ht h F s hp hd hm hi

theorem LocalAt.frame {P R : (Fragment → Prop)} {c : Cmd α} {Q : α → (Fragment → Prop)} {s : Heap}
    (ht : LocalAt P c Q s) :
    LocalAt (sep P R) c (fun x => sep (Q x) R) s := by
  intro h F ⟨a, b, hab, he, hp, hr⟩ hf hm hi
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  obtain ⟨hsafe, hpost⟩ :=
    ht a (b ∪ F) hp (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨a', hd, hm', hi', hq⟩ := hpost x s' hrun
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

theorem LocalOp.frame {P R : (Fragment → Prop)} {c : Cmd α}
    {Q : α → (Fragment → Prop)} (ht : LocalOp P c Q) :
    LocalOp (sep P R) c (fun x => sep (Q x) R) := by
  intro h F s ⟨a, b, hab, he, hp, hr⟩ hf hm hi
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  obtain ⟨hsafe, hpost⟩ :=
    ht a (b ∪ F) s hp (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨a', hd, hm', hi', hq⟩ := hpost x s' hrun
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

theorem LocalOp.drop {P R : (Fragment → Prop)} {c : Cmd α}
    {Q : α → (Fragment → Prop)} (ht : LocalOp P c (fun x => sep (Q x) R)) :
    LocalOp P c Q := by
  intro h F s hp hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s hp hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨_, hd', hm', hi', a, b, _, rfl, hq, _⟩ := hpost x s' hrun
  obtain ⟨haF, _⟩ := Fragment.disjoint_union_left.mp hd'
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _).mp hm'
  exact ⟨a, haF, (Fragment.matches_union _ _ _).mpr
    ⟨(Fragment.matches_union _ _ _).mp hab |>.1, hF⟩, hi', hq⟩

theorem LocalOp.conseq {P P' : (Fragment → Prop)} {c : Cmd α}
    {Q Q' : α → (Fragment → Prop)} (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : LocalOp P' c Q') : LocalOp P c Q := by
  intro h F s hP hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s (hp h hP) hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hQ⟩ := hpost x s' hrun
  exact ⟨h', hd', hm', hi', hq x h' hQ⟩

theorem LocalOp.pure_pre {A : Prop} {P : (Fragment → Prop)}
    {c : Cmd α} {Q : α → (Fragment → Prop)} (ht : A → LocalOp P c Q) :
    LocalOp (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi
  exact ht ha h F s hp hd hm hi

theorem LocalOp.pure (P : (Fragment → Prop)) (x : α) :
    LocalOp P (Cmd.pure x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi
  refine ⟨⟨x, s, rfl, rfl⟩, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨h, hd, hm, hi, rfl, hp⟩

theorem LocalOp.bind {P : (Fragment → Prop)} {c : Cmd α}
    {k : α → Cmd β} {Q : α → (Fragment → Prop)} {R : β → (Fragment → Prop)}
    (hc : LocalOp P c Q) (hk : ∀ x, LocalOp (Q x) (k x) R) :
    LocalOp P (c.bind k) R := by
  intro h F s hp hd hm hi
  obtain ⟨⟨x, s', hrun⟩, hpost⟩ := hc h F s hp hd hm hi
  have hnext : ∀ x s', c s x s' →
      (∃ y s'', k x s' y s'') ∧
      ∀ y s'', k x s' y s'' →
        ∃ h'', h''.Disjoint F ∧ Fragment.Matches s'' (h'' ∪ F) ∧ s''.Inv ∧ R y h'' := by
    intro x s' hx
    obtain ⟨h', hd', hm', hi', hq⟩ := hpost x s' hx
    exact hk x h' F s' hq hd' hm' hi'
  obtain ⟨⟨y, s'', hy⟩, _⟩ := hnext x s' hrun
  refine ⟨⟨y, s'', x, s', hrun, hy⟩, ?_⟩
  rintro y s'' ⟨x, s', hx, hy⟩
  exact (hnext x s' hx).2 y s'' hy

end Aeneas.Std.Bytes
