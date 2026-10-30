module

public import Aeneas.Std.Heap.Lemmas

/-! Logical ownership of individual byte cells and allocation cleanup authority.
Compatibility is byte-disjointness, independently of the types used to access the
bytes. Shared cells are not duplicated by separating conjunction. The global
freshness counter is never split. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

universe w w'

inductive Resource where
  | cell (base : BasePtr) (index : Nat) (alignment : Alignment) (value : Cell U8)
  | cleanup (base : BasePtr) (size : Nat) (alignment : Alignment) (owned : Bool)

namespace Resource

def base : Resource → BasePtr
  | .cell base _ _ _ | .cleanup base _ _ _ => base

def key : Resource → Option Nat
  | .cell _ index _ _ => some index
  | .cleanup _ _ _ _ => none

def Compatible (a b : Resource) : Prop :=
  a.base ≠ b.base ∨ a.key ≠ b.key

theorem Compatible.symm {a b : Resource} (h : a.Compatible b) : b.Compatible a := by
  unfold Compatible at *
  grind

theorem not_compatible_self (a : Resource) : ¬ a.Compatible a := by
  simp [Compatible]

def Holds (s : Heap) : Resource → Prop
  | .cell base index alignment c =>
    ∃ block, s.allocations base = some block ∧ alignment.val ∣ block.alignment.val ∧
      block.repr[index]? = some c
  | .cleanup base size alignment own =>
    ∃ block, s.allocations base = some block ∧ block.repr.length = size ∧
      block.alignment = alignment ∧ block.owned = own

theorem Holds.live {s : Heap} {r : Resource}
    (h : r.Holds s) : ∃ block, s.allocations r.base = some block := by
  cases r
  · exact h.imp fun _ hc => hc.1
  · exact h.imp fun _ hc => hc.1

end Resource

abbrev Fragment := Resource → Prop

namespace Fragment

def empty : Fragment := fun _ => False
def union (a b : Fragment) : Fragment := fun r => a r ∨ b r
def single (r : Resource) : Fragment := fun r' => r' = r

instance : EmptyCollection Fragment := ⟨empty⟩
instance : Union Fragment := ⟨union⟩

def Disjoint (a b : Fragment) : Prop :=
  ∀ r, a r → ∀ r', b r' → r.Compatible r'

def Matches (s : Heap) (h : Fragment) : Prop :=
  ∀ r, h r → r.Holds s

@[simp] theorem empty_union (h : Fragment) : ∅ ∪ h = h := by
  funext r
  exact false_or _

@[simp] theorem union_empty (h : Fragment) : h ∪ ∅ = h := by
  funext r
  exact or_false _

theorem union_assoc (a b c : Fragment) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  funext r
  exact propext or_assoc

theorem union_comm (a b : Fragment) : a ∪ b = b ∪ a := by
  funext r
  exact propext or_comm

theorem Disjoint.symm {a b : Fragment} (h : a.Disjoint b) : b.Disjoint a :=
  fun _ hb _ ha => (h _ ha _ hb).symm

@[simp] theorem disjoint_empty_left (h : Fragment) : (∅ : Fragment).Disjoint h :=
  fun _ hf => hf.elim

@[simp] theorem disjoint_empty_right (h : Fragment) : h.Disjoint ∅ :=
  (disjoint_empty_left h).symm

theorem disjoint_union_left {a b c : Fragment} :
    (a ∪ b).Disjoint c ↔ a.Disjoint c ∧ b.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

theorem disjoint_union_right {a b c : Fragment} :
    a.Disjoint (b ∪ c) ↔ a.Disjoint b ∧ a.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha _ hb => h _ ha _ (.inl hb),
      fun _ ha _ hc => h _ ha _ (.inr hc)⟩
  · rintro ⟨hb, hc⟩ r hr r' (hr' | hr')
    · exact hb r hr r' hr'
    · exact hc r hr r' hr'

@[simp] theorem matches_empty (s : Heap) :
    Matches s ∅ := fun _ h => h.elim

@[simp] theorem matches_union (s : Heap)
    (a b : Fragment) : Matches s (a ∪ b) ↔ Matches s a ∧ Matches s b := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

@[simp] theorem matches_single (s : Heap) (r : Resource) :
    Matches s (single r) ↔ r.Holds s := by
  constructor
  · exact fun h => h r rfl
  · rintro h _ rfl
    exact h

end Fragment

abbrev Assertion := Fragment → Prop

def emp : Assertion := fun h => h = ∅

def sep (P Q : Assertion) : Assertion :=
  fun h => ∃ a b, a.Disjoint b ∧ h = a ∪ b ∧ P a ∧ Q b

theorem sep_comm (P Q : Assertion) (h : Fragment) : sep P Q h ↔ sep Q P h := by
  constructor
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩

theorem sep_mono {P P' Q Q' : Assertion}
    (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) {h : Fragment} :
    sep P Q h → sep P' Q' h := by
  rintro ⟨a, b, hd, he, ha, hb⟩
  exact ⟨a, b, hd, he, hp _ ha, hq _ hb⟩

theorem sep_and_left (A : Prop) (P Q : Assertion) (h : Fragment) :
    sep (fun a => A ∧ P a) Q h ↔ A ∧ sep P Q h := by
  constructor
  · rintro ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩
    exact ⟨ha, a, b, hd, he, hp, hq⟩
  · rintro ⟨ha, a, b, hd, he, hp, hq⟩
    exact ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩

theorem sep_emp_left (P : Assertion) (h : Fragment) :
    sep emp P h ↔ P h := by
  constructor
  · rintro ⟨a, b, _, he, rfl, hp⟩
    have he' : h = b := by simpa using he
    simpa [he'] using hp
  · intro hp
    exact ⟨∅, h, Fragment.disjoint_empty_left h, by simp, rfl, hp⟩

abbrev Cmd (α : Type w) := Heap → α → Heap → Prop

def Cmd.pure (x : α) : Cmd α := fun s y s' => y = x ∧ s' = s
def Cmd.bind (c : Cmd α) (k : α → Cmd β) : Cmd β :=
  fun s y s'' => ∃ x s', c s x s' ∧ k x s' y s''

/-- Successor existence plus demonic safety, for every matching disjoint frame.
Dropped resources remain in the physical heap but are no longer owned. -/
def Triple (P : Assertion) (c : Cmd α)
    (Q : α → Assertion) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    (∃ x s', c s x s') ∧
    ∀ x s', c s x s' →
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h'

theorem frame {P R : Assertion} {c : Cmd α}
    {Q : α → Assertion} (ht : Triple P c Q) :
    Triple (sep P R) c (fun x => sep (Q x) R) := by
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

theorem Triple.drop {P R : Assertion} {c : Cmd α}
    {Q : α → Assertion} (ht : Triple P c (fun x => sep (Q x) R)) :
    Triple P c Q := by
  intro h F s hp hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s hp hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨_, hd', hm', hi', a, b, _, rfl, hq, _⟩ := hpost x s' hrun
  obtain ⟨haF, _⟩ := Fragment.disjoint_union_left.mp hd'
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _).mp hm'
  exact ⟨a, haF, (Fragment.matches_union _ _ _).mpr
    ⟨(Fragment.matches_union _ _ _).mp hab |>.1, hF⟩, hi', hq⟩

theorem Triple.conseq {P P' : Assertion} {c : Cmd α}
    {Q Q' : α → Assertion} (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : Triple P' c Q') : Triple P c Q := by
  intro h F s hP hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s (hp h hP) hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hQ⟩ := hpost x s' hrun
  exact ⟨h', hd', hm', hi', hq x h' hQ⟩

theorem Triple.pure_pre {A : Prop} {P : Assertion}
    {c : Cmd α} {Q : α → Assertion} (ht : A → Triple P c Q) :
    Triple (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi
  exact ht ha h F s hp hd hm hi

theorem Triple.pure (P : Assertion) (x : α) :
    Triple P (Cmd.pure x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi
  refine ⟨⟨x, s, rfl, rfl⟩, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨h, hd, hm, hi, rfl, hp⟩

theorem Triple.bind {P : Assertion} {c : Cmd α}
    {k : α → Cmd β} {Q : α → Assertion} {R : β → Assertion}
    (hc : Triple P c Q) (hk : ∀ x, Triple (Q x) (k x) R) :
    Triple P (c.bind k) R := by
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

end Aeneas.Std.SepLogic
