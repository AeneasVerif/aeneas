module

public import Aeneas.Std.Heap.Lemmas

/-! Logical fragments, not fragments of `Repr`.

A cell resource observes one typed cell; a cleanup resource observes cleanup authority and
the current typed extent. The extent is a logical fact, not extra allocation metadata.
Disjoint resources at one base must agree on their type. This is the single-type-view
discipline: round-trip alone cannot justify framing across unrelated interpretations.
This restricts compatible logical resources, not the physical representation: a model
may admit several interpretations of one representation.

Cell permissions are part of the observed cell. Separating conjunction does not duplicate
shared cells; splitting and rejoining safe borrows are explicit memory operations.
The global freshness counter is never split. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u w w'

inductive Resource where
  | cell (ty : Type u) (p : RawPtr ty) (value : Cell ty)
  | cleanup (ty : Type u) (base : BasePtr) (count : Nat) (allocated : Bool)

namespace Resource

def ty : Resource.{u} → Type u
  | .cell ty _ _ | .cleanup ty _ _ _ => ty

def base : Resource → BasePtr
  | .cell _ p _ => p.base
  | .cleanup _ base _ _ => base

def key : Resource → Option Nat
  | .cell _ p _ => some p.offset
  | .cleanup _ _ _ _ => none

def Compatible (a b : Resource.{u}) : Prop :=
  a.base ≠ b.base ∨ (a.ty = b.ty ∧ a.key ≠ b.key)

theorem Compatible.symm {a b : Resource.{u}} (h : a.Compatible b) : b.Compatible a := by
  unfold Compatible at *
  grind

theorem not_compatible_self (a : Resource.{u}) : ¬ a.Compatible a := by
  simp [Compatible]

def Holds (m : Layout.{u}) (s : Heap m.Repr) : Resource.{u} → Prop
  | .cell ty p c =>
    ∃ cs, s.load m.interpret ty p.base = some cs ∧ cs[p.offset]? = some c
  | .cleanup ty base count own =>
    s.allocated base = own ∧
      ∃ cs, s.load m.interpret ty base = some cs ∧ cs.length = count

theorem Holds.live {m : Layout.{u}} {s : Heap m.Repr} {r : Resource.{u}}
    (h : r.Holds m s) : ∃ cs, s.load m.interpret r.ty r.base = some cs := by
  cases r
  · exact h.imp fun _ hc => hc.1
  · exact h.2.imp fun _ hc => hc.1

end Resource

abbrev Fragment := Resource.{u} → Prop

namespace Fragment

def empty : Fragment.{u} := fun _ => False
def union (a b : Fragment.{u}) : Fragment.{u} := fun r => a r ∨ b r
def single (r : Resource.{u}) : Fragment.{u} := fun r' => r' = r

instance : EmptyCollection Fragment.{u} := ⟨empty⟩
instance : Union Fragment.{u} := ⟨union⟩

def Disjoint (a b : Fragment.{u}) : Prop :=
  ∀ r, a r → ∀ r', b r' → r.Compatible r'

def Matches (m : Layout.{u}) (s : Heap m.Repr) (h : Fragment.{u}) : Prop :=
  ∀ r, h r → r.Holds m s

@[simp] theorem empty_union (h : Fragment.{u}) : ∅ ∪ h = h := by
  funext r
  exact false_or _

@[simp] theorem union_empty (h : Fragment.{u}) : h ∪ ∅ = h := by
  funext r
  exact or_false _

theorem union_assoc (a b c : Fragment.{u}) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  funext r
  exact propext or_assoc

theorem union_comm (a b : Fragment.{u}) : a ∪ b = b ∪ a := by
  funext r
  exact propext or_comm

theorem Disjoint.symm {a b : Fragment.{u}} (h : a.Disjoint b) : b.Disjoint a :=
  fun _ hb _ ha => (h _ ha _ hb).symm

@[simp] theorem disjoint_empty_left (h : Fragment.{u}) : (∅ : Fragment).Disjoint h :=
  fun _ hf => hf.elim

@[simp] theorem disjoint_empty_right (h : Fragment.{u}) : h.Disjoint ∅ :=
  (disjoint_empty_left h).symm

theorem disjoint_union_left {a b c : Fragment.{u}} :
    (a ∪ b).Disjoint c ↔ a.Disjoint c ∧ b.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

theorem disjoint_union_right {a b c : Fragment.{u}} :
    a.Disjoint (b ∪ c) ↔ a.Disjoint b ∧ a.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha _ hb => h _ ha _ (.inl hb),
      fun _ ha _ hc => h _ ha _ (.inr hc)⟩
  · rintro ⟨hb, hc⟩ r hr r' (hr' | hr')
    · exact hb r hr r' hr'
    · exact hc r hr r' hr'

@[simp] theorem matches_empty (m : Layout.{u}) (s : Heap m.Repr) :
    Matches m s ∅ := fun _ h => h.elim

@[simp] theorem matches_union (m : Layout.{u}) (s : Heap m.Repr)
    (a b : Fragment.{u}) : Matches m s (a ∪ b) ↔ Matches m s a ∧ Matches m s b := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

@[simp] theorem matches_single (m : Layout.{u}) (s : Heap m.Repr) (r : Resource.{u}) :
    Matches m s (single r) ↔ r.Holds m s := by
  constructor
  · exact fun h => h r rfl
  · rintro h _ rfl
    exact h

end Fragment

abbrev Assertion := Fragment.{u} → Prop

def emp : Assertion.{u} := fun h => h = ∅

def sep (P Q : Assertion.{u}) : Assertion.{u} :=
  fun h => ∃ a b, a.Disjoint b ∧ h = a ∪ b ∧ P a ∧ Q b

theorem sep_comm (P Q : Assertion.{u}) (h : Fragment.{u}) : sep P Q h ↔ sep Q P h := by
  constructor
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩
  · rintro ⟨a, b, hd, he, hp, hq⟩
    exact ⟨b, a, hd.symm, he.trans (Fragment.union_comm _ _), hq, hp⟩

theorem sep_mono {P P' Q Q' : Assertion.{u}}
    (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) {h : Fragment.{u}} :
    sep P Q h → sep P' Q' h := by
  rintro ⟨a, b, hd, he, ha, hb⟩
  exact ⟨a, b, hd, he, hp _ ha, hq _ hb⟩

theorem sep_and_left (A : Prop) (P Q : Assertion.{u}) (h : Fragment.{u}) :
    sep (fun a => A ∧ P a) Q h ↔ A ∧ sep P Q h := by
  constructor
  · rintro ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩
    exact ⟨ha, a, b, hd, he, hp, hq⟩
  · rintro ⟨ha, a, b, hd, he, hp, hq⟩
    exact ⟨a, b, hd, he, ⟨ha, hp⟩, hq⟩

theorem sep_emp_left (P : Assertion.{u}) (h : Fragment.{u}) :
    sep emp P h ↔ P h := by
  constructor
  · rintro ⟨a, b, _, he, rfl, hp⟩
    have he' : h = b := by simpa using he
    simpa [he'] using hp
  · intro hp
    exact ⟨∅, h, Fragment.disjoint_empty_left h, by simp, rfl, hp⟩

abbrev Cmd (m : Layout.{u}) (α : Type w) := Heap m.Repr → α → Heap m.Repr → Prop

def Cmd.pure (m : Layout.{u}) (x : α) : Cmd m α := fun s y s' => y = x ∧ s' = s
def Cmd.bind {m : Layout.{u}} (c : Cmd m α) (k : α → Cmd m β) : Cmd m β :=
  fun s y s'' => ∃ x s', c s x s' ∧ k x s' y s''

/-- Successor existence plus demonic safety, for every matching disjoint frame.
Dropped resources remain in the physical heap but are no longer owned. -/
def Triple (m : Layout.{u}) (P : Assertion.{u}) (c : Cmd m α)
    (Q : α → Assertion.{u}) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches m s (h ∪ F) → s.Inv →
    (∃ x s', c s x s') ∧
    ∀ x s', c s x s' →
      ∃ h', h'.Disjoint F ∧ Fragment.Matches m s' (h' ∪ F) ∧ s'.Inv ∧ Q x h'

theorem frame {m : Layout.{u}} {P R : Assertion.{u}} {c : Cmd m α}
    {Q : α → Assertion.{u}} (ht : Triple m P c Q) :
    Triple m (sep P R) c (fun x => sep (Q x) R) := by
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

theorem Triple.drop {m : Layout.{u}} {P R : Assertion.{u}} {c : Cmd m α}
    {Q : α → Assertion.{u}} (ht : Triple m P c (fun x => sep (Q x) R)) :
    Triple m P c Q := by
  intro h F s hp hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s hp hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨_, hd', hm', hi', a, b, _, rfl, hq, _⟩ := hpost x s' hrun
  obtain ⟨haF, _⟩ := Fragment.disjoint_union_left.mp hd'
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _ _).mp hm'
  exact ⟨a, haF, (Fragment.matches_union _ _ _ _).mpr
    ⟨(Fragment.matches_union _ _ _ _).mp hab |>.1, hF⟩, hi', hq⟩

theorem Triple.conseq {m : Layout.{u}} {P P' : Assertion.{u}} {c : Cmd m α}
    {Q Q' : α → Assertion.{u}} (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : Triple m P' c Q') : Triple m P c Q := by
  intro h F s hP hd hm hi
  obtain ⟨hsafe, hpost⟩ := ht h F s (hp h hP) hd hm hi
  refine ⟨hsafe, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hQ⟩ := hpost x s' hrun
  exact ⟨h', hd', hm', hi', hq x h' hQ⟩

theorem Triple.pure_pre {m : Layout.{u}} {A : Prop} {P : Assertion.{u}}
    {c : Cmd m α} {Q : α → Assertion.{u}} (ht : A → Triple m P c Q) :
    Triple m (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi
  exact ht ha h F s hp hd hm hi

theorem Triple.pure (m : Layout.{u}) (P : Assertion.{u}) (x : α) :
    Triple m P (Cmd.pure m x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi
  refine ⟨⟨x, s, rfl, rfl⟩, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨h, hd, hm, hi, rfl, hp⟩

theorem Triple.bind {m : Layout.{u}} {P : Assertion.{u}} {c : Cmd m α}
    {k : α → Cmd m β} {Q : α → Assertion.{u}} {R : β → Assertion.{u}}
    (hc : Triple m P c Q) (hk : ∀ x, Triple m (Q x) (k x) R) :
    Triple m P (c.bind k) R := by
  intro h F s hp hd hm hi
  obtain ⟨⟨x, s', hrun⟩, hpost⟩ := hc h F s hp hd hm hi
  have hnext : ∀ x s', c s x s' →
      (∃ y s'', k x s' y s'') ∧
      ∀ y s'', k x s' y s'' →
        ∃ h'', h''.Disjoint F ∧ Fragment.Matches m s'' (h'' ∪ F) ∧ s''.Inv ∧ R y h'' := by
    intro x s' hx
    obtain ⟨h', hd', hm', hi', hq⟩ := hpost x s' hx
    exact hk x h' F s' hq hd' hm' hi'
  obtain ⟨⟨y, s'', hy⟩, _⟩ := hnext x s' hrun
  refine ⟨⟨y, s'', x, s', hrun, hy⟩, ?_⟩
  rintro y s'' ⟨x, s', hx, hy⟩
  exact (hnext x s' hx).2 y s'' hy

end Aeneas.Std.SepLogic
