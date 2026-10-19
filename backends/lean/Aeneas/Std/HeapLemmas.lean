module

public import Aeneas.Std.Heap
import all Aeneas.Std.Heap

public section

namespace Aeneas

/-- A partial commutative monoid: a total `∪`, meaningful on `Compatible` inputs. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

end Aeneas

namespace Aeneas.Std

namespace RawPtr

@[simp] theorem allocId_shift (q : RawPtr T M) (i : Nat) : (q.shift i).allocId = q.allocId := by
  simp [RawPtr.shift]

@[simp] theorem offset_shift (q : RawPtr T M) (i : Nat) : (q.shift i).offset = q.offset + i := by
  simp [RawPtr.shift]

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := by
  simp [RawPtr.shift]

theorem shift_shift (q : RawPtr T M) (i j : Nat) :
    (q.shift i).shift j = q.shift (i + j) := by
  simp [RawPtr.shift, Nat.add_assoc]

end RawPtr

/-! ### Cells -/

namespace Cell

private theorem compatible_symm {x y : Cell α} (h : Compatible x y) : Compatible y x := by
  cases x <;> cases y <;> simp_all [Compatible]

private theorem join_comm {x y : Cell α} (h : Compatible x y) : join x y = join y x := by
  cases x <;> cases y <;> simp_all [Compatible, join]

private theorem join_assoc (x y z : Cell α) : join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> rfl

private theorem compatible_assoc' (x y z : Cell α) :
    Compatible x y ∧ Compatible (join x y) z ↔ Compatible y z ∧ Compatible x (join y z) := by
  cases x <;> cases y <;> cases z <;> simp [Compatible, join]

private theorem forall₂_symm {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂) :
    List.Forall₂ Compatible l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons (compatible_symm hxy) ih

private theorem zipWith_join_comm {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂) :
    List.zipWith join l₁ l₂ = List.zipWith join l₂ l₁ := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => rw [List.zipWith_cons_cons, List.zipWith_cons_cons, join_comm hxy, ih]

private theorem zipWith_join_assoc :
    ∀ l₁ l₂ l₃ : List (Cell α),
      List.zipWith join (List.zipWith join l₁ l₂) l₃ =
        List.zipWith join l₁ (List.zipWith join l₂ l₃)
  | x :: l₁, y :: l₂, z :: l₃ => by
    simp only [List.zipWith_cons_cons, join_assoc, zipWith_join_assoc l₁ l₂ l₃]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl

private theorem forall₂_zipWith_assoc :
    ∀ l₁ l₂ l₃ : List (Cell α),
      (List.Forall₂ Compatible l₁ l₂ ∧ List.Forall₂ Compatible (List.zipWith join l₁ l₂) l₃) ↔
        (List.Forall₂ Compatible l₂ l₃ ∧ List.Forall₂ Compatible l₁ (List.zipWith join l₂ l₃))
  | x :: l₁, y :: l₂, z :: l₃ => by
    have hCell := compatible_assoc' x y z
    have hRest := forall₂_zipWith_assoc l₁ l₂ l₃
    simp only [List.zipWith_cons_cons, List.forall₂_cons]
    constructor
    · rintro ⟨⟨hxy, h₁₂⟩, hxyz, h₁₂₃⟩
      obtain ⟨hyz, hx⟩ := hCell.mp ⟨hxy, hxyz⟩
      obtain ⟨h₂₃, h₁⟩ := hRest.mp ⟨h₁₂, h₁₂₃⟩
      exact ⟨⟨hyz, h₂₃⟩, hx, h₁⟩
    · rintro ⟨⟨hyz, h₂₃⟩, hx, h₁⟩
      obtain ⟨hxy, hxyz⟩ := hCell.mpr ⟨hyz, hx⟩
      obtain ⟨h₁₂, h₁₂₃⟩ := hRest.mpr ⟨h₂₃, h₁⟩
      exact ⟨⟨hxy, h₁₂⟩, hxyz, h₁₂₃⟩
  | [], [], [] => by simp
  | [], [], _ :: _ => by simp
  | [], _ :: _, [] => by simp
  | [], _ :: _, _ :: _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp

private theorem joinList_of_forall₂ {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂) :
    joinList l₁ l₂ = List.zipWith join l₁ l₂ :=
  ite_eq_left h.length_eq

private theorem joinList_comm {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂) :
    joinList l₁ l₂ = joinList l₂ l₁ := by
  rw [joinList_of_forall₂ h, joinList_of_forall₂ (forall₂_symm h), zipWith_join_comm h]

private theorem forall₂_joinList_assoc (l₁ l₂ l₃ : List (Cell α)) :
    (List.Forall₂ Compatible l₁ l₂ ∧ List.Forall₂ Compatible (joinList l₁ l₂) l₃) ↔
      (List.Forall₂ Compatible l₂ l₃ ∧ List.Forall₂ Compatible l₁ (joinList l₂ l₃)) := by
  constructor
  · rintro ⟨h₁₂, h₁₂₃⟩
    rw [joinList_of_forall₂ h₁₂] at h₁₂₃
    have ⟨h₂₃, h₁⟩ := (forall₂_zipWith_assoc l₁ l₂ l₃).mp ⟨h₁₂, h₁₂₃⟩
    exact ⟨h₂₃, joinList_of_forall₂ h₂₃ ▸ h₁⟩
  · rintro ⟨h₂₃, h₁⟩
    rw [joinList_of_forall₂ h₂₃] at h₁
    have ⟨h₁₂, h₁₂₃⟩ := (forall₂_zipWith_assoc l₁ l₂ l₃).mpr ⟨h₂₃, h₁⟩
    exact ⟨h₁₂, joinList_of_forall₂ h₁₂ ▸ h₁₂₃⟩

private theorem joinList_assoc {l₁ l₂ l₃ : List (Cell α)} (h₁₂ : List.Forall₂ Compatible l₁ l₂)
    (h₁₂₃ : List.Forall₂ Compatible (joinList l₁ l₂) l₃) :
    joinList (joinList l₁ l₂) l₃ = joinList l₁ (joinList l₂ l₃) := by
  have ⟨h₂₃, h₁⟩ := (forall₂_joinList_assoc l₁ l₂ l₃).mp ⟨h₁₂, h₁₂₃⟩
  rw [joinList_of_forall₂ h₁₂₃, joinList_of_forall₂ h₁, joinList_of_forall₂ h₁₂,
    joinList_of_forall₂ h₂₃, zipWith_join_assoc]

private theorem joinList_nil_right (l : List (Cell α)) : joinList l [] = l := by
  unfold joinList
  split
  · rename_i hLen
    rw [List.length_eq_zero_iff.mp hLen]
    rfl
  · rfl

private theorem length_joinList (l₁ l₂ : List (Cell α)) : (joinList l₁ l₂).length = l₁.length := by
  unfold joinList
  split <;> simp_all

private theorem getElem?_joinList (l₁ l₂ : List (Cell α)) (i : Nat) :
    (joinList l₁ l₂)[i]? =
      if l₁.length = l₂.length then (l₁[i]?.map join).bind fun f => l₂[i]?.map f else l₁[i]? := by
  unfold joinList
  split
  · exact List.getElem?_zipWith'
  · rfl

/-- An owned cell stays owned, whatever the other fragment holds. -/
private theorem getElem?_joinList_owned {l₁ l₂ : List (Cell α)} {i : Nat} {x : α}
    (h : l₁[i]? = some (.owned x)) : (joinList l₁ l₂)[i]? = some (.owned x) := by
  rw [getElem?_joinList]
  split
  · rename_i hLen
    have hi : i < l₂.length := hLen ▸ (List.getElem?_eq_some_iff.mp h).1
    simp [h, List.getElem?_eq_getElem hi, join]
  · exact h

private theorem joinList_set_owned (l₁ l₂ : List (Cell α)) (i : Nat) (x : α) :
    joinList (l₁.set i (.owned x)) l₂ = (joinList l₁ l₂).set i (.owned x) := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_joinList, List.length_set, List.getElem?_set, List.getElem?_set,
    getElem?_joinList, length_joinList]
  by_cases hLen : l₁.length = l₂.length
  · simp only [hLen, ite_true]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i < l₂.length
      · simp [hi, join]
      · simp [hi]
    · simp [hij]
  · simp [hLen]

private theorem joinList_set_borrowed (l₁ l₂ : List (Cell α)) (i : Nat) :
    joinList (l₁.set i .borrowed) l₂ = (joinList l₁ l₂).set i .borrowed := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_joinList, List.length_set, List.getElem?_set, List.getElem?_set,
    getElem?_joinList, length_joinList]
  by_cases hLen : l₁.length = l₂.length
  · simp only [hLen, ite_true]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i < l₂.length
      · simp [hi, join]
      · simp [hi]
    · simp [hij]
  · simp [hLen]

/-- A fragment compatible with an owned or borrowed cell does not own or borrow it. -/
private theorem eq_notOwned_of_compatible {x y : Cell α} (h : Compatible x y)
    (hx : x ≠ .notOwned) : y = .notOwned := by
  cases x <;> cases y <;> simp_all [Compatible]

private theorem forall₂_iff_getElem? {l₁ l₂ : List (Cell α)} :
    List.Forall₂ Compatible l₁ l₂ ↔
      l₁.length = l₂.length ∧
        ∀ (i : Nat) (x y : Cell α), l₁[i]? = some x → l₂[i]? = some y → Compatible x y := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨hLen, h⟩
    refine ⟨hLen, fun i x y hx hy => ?_⟩
    obtain ⟨hi₁, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hi₂, rfl⟩ := List.getElem?_eq_some_iff.mp hy
    exact h i hi₁ hi₂
  · rintro ⟨hLen, h⟩
    exact ⟨hLen, fun i hi₁ hi₂ =>
      h i _ _ (List.getElem?_eq_getElem hi₁) (List.getElem?_eq_getElem hi₂)⟩

end Cell

/-! ### Blocks and slots -/

namespace Block

@[simp] private theorem cellsAs_mk (k : AllocKind) (t : Type) (c : List (Cell t)) :
    (⟨k, t, c⟩ : Block).cellsAs t = c := by
  simp [cellsAs]

private theorem compatible_mk_iff (k₁ k₂ : AllocKind) (t : Type) (c₁ c₂ : List (Cell t)) :
    Compatible ⟨k₁, t, c₁⟩ ⟨k₂, t, c₂⟩ ↔ k₁ = k₂ ∧ List.Forall₂ Cell.Compatible c₁ c₂ := by
  simp [Compatible]

@[simp] private theorem join_mk (k₁ k₂ : AllocKind) (t : Type) (c₁ c₂ : List (Cell t)) :
    join ⟨k₁, t, c₁⟩ ⟨k₂, t, c₂⟩ = ⟨k₁, t, Cell.joinList c₁ c₂⟩ := by
  simp [join]

/-- Compatible blocks have the same type. -/
private theorem eq_mk_of_compatible {b₁ b₂ : Block} (h : Compatible b₁ b₂) :
    ∃ k₂ c₂, b₂ = ⟨k₂, b₁.ty, c₂⟩ := by
  obtain ⟨k₂, t₂, c₂⟩ := b₂
  obtain ⟨-, hTy, -⟩ := h
  dsimp only at hTy
  subst hTy
  exact ⟨k₂, c₂, rfl⟩

private theorem compatible_symm {b₁ b₂ : Block} (h : Compatible b₁ b₂) : Compatible b₂ b₁ := by
  obtain ⟨k₁, t, c₁⟩ := b₁
  obtain ⟨k₂, c₂, rfl⟩ := eq_mk_of_compatible h
  dsimp only at h ⊢
  rw [compatible_mk_iff] at h ⊢
  exact ⟨h.1.symm, Cell.forall₂_symm h.2⟩

private theorem join_comm {b₁ b₂ : Block} (h : Compatible b₁ b₂) : join b₁ b₂ = join b₂ b₁ := by
  obtain ⟨k₁, t, c₁⟩ := b₁
  obtain ⟨k₂, c₂, rfl⟩ := eq_mk_of_compatible h
  dsimp only at h ⊢
  rw [compatible_mk_iff] at h
  rw [join_mk, join_mk, h.1, Cell.joinList_comm h.2]

private theorem compatible_assoc' (a b c : Block) :
    Compatible a b ∧ Compatible (join a b) c ↔ Compatible b c ∧ Compatible a (join b c) := by
  obtain ⟨ka, t, ca⟩ := a
  constructor
  · rintro ⟨hab, habc⟩
    obtain ⟨kb, cb, rfl⟩ := eq_mk_of_compatible hab
    dsimp only at hab habc ⊢
    rw [join_mk] at habc
    obtain ⟨kc, cc, rfl⟩ := eq_mk_of_compatible habc
    dsimp only at habc ⊢
    rw [join_mk]
    simp only [compatible_mk_iff] at hab habc ⊢
    have ⟨hbc, ha⟩ := (Cell.forall₂_joinList_assoc _ _ _).mp ⟨hab.2, habc.2⟩
    exact ⟨⟨hab.1.symm.trans habc.1, hbc⟩, hab.1, ha⟩
  · rintro ⟨hbc, habc⟩
    obtain ⟨kb, tb, cb⟩ := b
    obtain ⟨kc, cc, rfl⟩ := eq_mk_of_compatible hbc
    dsimp only at hbc habc ⊢
    rw [join_mk] at habc
    have hTy : tb = t := habc.2.1
    subst hTy
    rw [join_mk]
    simp only [compatible_mk_iff] at hbc habc ⊢
    have ⟨hab, ha⟩ := (Cell.forall₂_joinList_assoc _ _ _).mpr ⟨hbc.2, habc.2⟩
    exact ⟨⟨habc.1, hab⟩, habc.1.trans hbc.1, ha⟩

private theorem join_assoc {a b c : Block} (hab : Compatible a b)
    (habc : Compatible (join a b) c) : join (join a b) c = join a (join b c) := by
  obtain ⟨ka, t, ca⟩ := a
  obtain ⟨kb, cb, rfl⟩ := eq_mk_of_compatible hab
  dsimp only at hab habc ⊢
  rw [join_mk] at habc
  obtain ⟨kc, cc, rfl⟩ := eq_mk_of_compatible habc
  dsimp only at habc ⊢
  simp only [compatible_mk_iff] at hab habc
  simp only [join_mk, Cell.joinList_assoc hab.2 habc.2]

end Block

namespace BlockSlot

private theorem compatible_symm {s₁ s₂ : BlockSlot} (h : Compatible s₁ s₂) : Compatible s₂ s₁ := by
  cases s₁ <;> cases s₂ <;> simp_all [Compatible, Block.compatible_symm]

private theorem join_comm {s₁ s₂ : BlockSlot} (h : Compatible s₁ s₂) : join s₁ s₂ = join s₂ s₁ := by
  match s₁, s₂, h with
  | .live _, .live _, h => exact congrArg BlockSlot.live (Block.join_comm h)
  | .live _, .freed, h => exact False.elim h
  | .freed, _, h => exact False.elim h

private theorem compatible_assoc' (a b c : BlockSlot) :
    Compatible a b ∧ Compatible (join a b) c ↔ Compatible b c ∧ Compatible a (join b c) := by
  cases a <;> cases b <;> cases c <;> simp [Compatible, join, Block.compatible_assoc']

private theorem join_assoc {a b c : BlockSlot} (hab : Compatible a b)
    (habc : Compatible (join a b) c) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [Compatible, join, Block.join_assoc]

end BlockSlot

private theorem optCompatible_symm {o₁ o₂ : Option BlockSlot} (h : OptCompatible o₁ o₂) :
    OptCompatible o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp_all [OptCompatible, BlockSlot.compatible_symm]

private theorem merge_join_comm {o₁ o₂ : Option BlockSlot} (h : OptCompatible o₁ o₂) :
    Option.merge BlockSlot.join o₁ o₂ = Option.merge BlockSlot.join o₂ o₁ := by
  match o₁, o₂, h with
  | some _, some _, h => exact congrArg some (BlockSlot.join_comm h)
  | some _, none, _ => rfl
  | none, some _, _ => rfl
  | none, none, _ => rfl

private theorem optCompatible_assoc (a b c : Option BlockSlot) :
    OptCompatible a b ∧ OptCompatible (Option.merge BlockSlot.join a b) c ↔
      OptCompatible b c ∧ OptCompatible a (Option.merge BlockSlot.join b c) := by
  cases a <;> cases b <;> cases c <;> simp [OptCompatible, Option.merge, BlockSlot.compatible_assoc']

private theorem merge_join_assoc {a b c : Option BlockSlot} (hab : OptCompatible a b)
    (habc : OptCompatible (Option.merge BlockSlot.join a b) c) :
    Option.merge BlockSlot.join (Option.merge BlockSlot.join a b) c =
      Option.merge BlockSlot.join a (Option.merge BlockSlot.join b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [OptCompatible, Option.merge, BlockSlot.join_assoc]

/-! ### Heaps -/

namespace Heap

private theorem ext {h₁ h₂ : Heap} (hEq : ∀ a, h₁.lookup a = h₂.lookup a) : h₁ = h₂ := by
  obtain ⟨m₁⟩ := h₁
  obtain ⟨m₂⟩ := h₂
  congr 1
  exact Finmap.ext_lookup hEq

private theorem lookup_foldr (h₁ h₂ : Heap) (a : AllocId) (m : Finmap fun _ : AllocId => BlockSlot)
    (s : Multiset AllocId) :
    (@Multiset.foldr _ _ (insertJoin h₁ h₂) (insertJoin_leftComm h₁ h₂) m s).lookup a =
      if a ∈ s then some (joinAt h₁ h₂ a) else m.lookup a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.foldr_cons]
    show Finmap.lookup a (Finmap.insert b _ _) = _
    by_cases hab : a = b
    · subst hab
      simp [Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hab, ih]
      simp [Multiset.mem_cons, hab]

private theorem lookup_union (h₁ h₂ : Heap) (a : AllocId) :
    (h₁ ∪ h₂).lookup a = Option.merge BlockSlot.join (h₁.lookup a) (h₂.lookup a) := by
  show (Heap.union h₁ h₂).allocs.lookup a = _
  unfold Heap.union
  rw [lookup_foldr]
  split
  · rename_i ha
    have hMem : a ∈ h₂.allocs := Finmap.mem_keys.mp (Finset.mem_val.mp ha)
    obtain ⟨s₂, hs₂⟩ := Finmap.mem_iff.mp hMem
    unfold joinAt
    simp only [lookup, hs₂]
    cases h₁.allocs.lookup a <;> rfl
  · rename_i ha
    have hNone : h₂.allocs.lookup a = none :=
      Finmap.lookup_eq_none.mpr fun hMem => ha (Finset.mem_val.mpr (Finmap.mem_keys.mpr hMem))
    simp only [lookup, hNone]
    cases h₁.allocs.lookup a <;> rfl

@[simp] private theorem lookup_empty (a : AllocId) : (∅ : Heap).lookup a = none :=
  Finmap.lookup_empty a

private theorem lookup_insert (h : Heap) (a : AllocId) (s : BlockSlot) :
    (h.insert a s).lookup a = some s :=
  Finmap.lookup_insert _

private theorem lookup_insert_ne (h : Heap) {a b : AllocId} (s : BlockSlot) (hNe : b ≠ a) :
    (h.insert a s).lookup b = h.lookup b :=
  Finmap.lookup_insert_of_ne _ hNe

private theorem mem_iff_lookup {a : AllocId} {h : Heap} : a ∈ h ↔ (h.lookup a).isSome :=
  Finmap.lookup_isSome.symm

private theorem lookup_eq_none {a : AllocId} {h : Heap} : h.lookup a = none ↔ a ∉ h :=
  Finmap.lookup_eq_none

@[simp]
theorem empty_union (h : Heap) : ∅ ∪ h = h :=
  ext fun a => by rw [lookup_union, lookup_empty, Option.merge_none_left]

@[simp]
theorem union_empty (h : Heap) : h ∪ ∅ = h :=
  ext fun a => by rw [lookup_union, lookup_empty, Option.merge_none_right]

private theorem compatible_symm {h₁ h₂ : Heap} (hCompatible : Heap.Compatible h₁ h₂) :
    Heap.Compatible h₂ h₁ :=
  fun a => optCompatible_symm (hCompatible a)

private theorem compatible_empty_left (h : Heap) : Heap.Compatible ∅ h := fun a => by
  show OptCompatible ((∅ : Heap).lookup a) _
  rw [lookup_empty]
  trivial

private theorem compatible_assoc (a b c : Heap) :
    Heap.Compatible a b ∧ Heap.Compatible (a ∪ b) c ↔
      Heap.Compatible b c ∧ Heap.Compatible a (b ∪ c) := by
  simp only [Heap.Compatible, lookup_union]
  constructor
  · rintro ⟨hab, habc⟩
    exact ⟨fun x => ((optCompatible_assoc _ _ _).mp ⟨hab x, habc x⟩).1,
      fun x => ((optCompatible_assoc _ _ _).mp ⟨hab x, habc x⟩).2⟩
  · rintro ⟨hbc, habc⟩
    exact ⟨fun x => ((optCompatible_assoc _ _ _).mpr ⟨hbc x, habc x⟩).1,
      fun x => ((optCompatible_assoc _ _ _).mpr ⟨hbc x, habc x⟩).2⟩

private theorem union_assoc {a b c : Heap} (hab : Heap.Compatible a b)
    (habc : Heap.Compatible (a ∪ b) c) : a ∪ b ∪ c = a ∪ (b ∪ c) := ext fun x => by
  have habc' := habc x
  rw [lookup_union] at habc'
  simp only [lookup_union, merge_join_assoc (hab x) habc']

private theorem union_comm_of_compatible {a b : Heap} (hCompatible : Heap.Compatible a b) :
    a ∪ b = b ∪ a := ext fun x => by
  simp only [lookup_union, merge_join_comm (hCompatible x)]

@[no_expose] instance instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.Compatible
  compatible_comm := compatible_symm
  compatible_empty_left := compatible_empty_left
  compatible_assoc := compatible_assoc
  union_assoc := union_assoc
  empty_union := empty_union
  union_empty := union_empty
  union_comm_of_compatible := union_comm_of_compatible

theorem mem_union {a : AllocId} {h₁ h₂ : Heap} : a ∈ h₁ ∪ h₂ ↔ a ∈ h₁ ∨ a ∈ h₂ := by
  simp only [mem_iff_lookup, lookup_union]
  cases h₁.lookup a <;> cases h₂.lookup a <;> simp [Option.merge]

/-- The cells of the block `a` of `h`, as cells of type `t`. -/
private noncomputable def cellsAt (h : Heap) (a : AllocId) (t : Type) : List (Cell t) :=
  match h.lookup a with
  | some (.live b) => b.cellsAs t
  | _ => []

/-- A live block of `h₁` stays live in `h₁ ∪ h₂`, with the same header: the cells of `h₂` are
joined into it. -/
private theorem lookup_union_live {h₁ h₂ : Heap} {a : AllocId} {b : Block}
    (hLookup : h₁.lookup a = some (.live b)) :
    (h₁ ∪ h₂).lookup a = some (.live ⟨b.kind, b.ty, Cell.joinList b.cells (h₂.cellsAt a b.ty)⟩) := by
  rw [lookup_union, hLookup]
  unfold cellsAt
  rcases hs : h₂.lookup a with _ | _ | _
  · simp [Option.merge, Cell.joinList_nil_right]
  · rfl
  · simp [Option.merge, BlockSlot.join, Cell.joinList_nil_right]

private theorem cell?_union_left {h₁ h₂ : Heap} {l : RawPtr T M} {c : Σ α : Type, α}
    (hCell : h₁.cell? l = some c) : (h₁ ∪ h₂).cell? l = some c := by
  unfold cell? at hCell ⊢
  split at hCell
  · rename_i b hLookup
    rw [lookup_union_live hLookup]
    dsimp only
    split at hCell
    · rename_i x hx
      rw [Cell.getElem?_joinList_owned hx]
      exact hCell
    · simp at hCell
  · simp at hCell

theorem mem_singleton {α : Type} {q : RawPtr α M} {value : α} {kind : AllocKind} {len : Nat}
    {a : AllocId} : a ∈ singleton q value kind len ↔ a = q.allocId :=
  Finmap.mem_singleton _ _ _

/-- The cell does not depend on the pointer's mutability. -/
theorem singleton_eq_of_addr {α : Type} {q : RawPtr α M} {r : RawPtr α M'}
    (hId : q.allocId = r.allocId) (hOffset : q.offset = r.offset) (value : α) (kind : AllocKind)
    (len : Nat) : singleton q value kind len = singleton r value kind len := by
  unfold singleton
  rw [hId, hOffset]

private theorem lookup_singleton {α : Type} (q : RawPtr α M) (value : α) (kind : AllocKind)
    (len : Nat) : (singleton q value kind len).lookup q.allocId =
      some (.live ⟨kind, α, (List.replicate len .notOwned).set q.offset (.owned value)⟩) :=
  Finmap.lookup_singleton_eq

private theorem lookup_singleton_ne {α : Type} {q : RawPtr α M} {value : α} {kind : AllocKind}
    {len : Nat} {a : AllocId} (hNe : a ≠ q.allocId) :
    (singleton q value kind len).lookup a = none :=
  lookup_eq_none.mpr fun hMem => hNe (mem_singleton.mp hMem)

@[simp]
theorem not_isValid_empty {α : Type} (q : RawPtr α M) :
    ¬ IsValid (∅ : Heap) q := by
  simp [IsValid, cell?]

theorem notMem_freshAllocId {h : Heap} {a : AllocId}
    (hBase : a = freshAllocId h) : a ∉ h := by
  intro hMem
  have hLe : a ≤ h.allocs.keys.sup id := Finset.le_sup (f := id) (Finmap.mem_keys.mpr hMem)
  rw [hBase, freshAllocId] at hLe
  exact Nat.not_succ_le_self _ hLe

private theorem lookup_allocation {α : Type} (a : AllocId) (values : List α) (kind : AllocKind) :
    (allocation a values kind).lookup a = some (.live ⟨kind, α, values.map .owned⟩) :=
  Finmap.lookup_singleton_eq

private theorem lookup_allocation_ne {α : Type} {a b : AllocId} {values : List α}
    {kind : AllocKind} (hNe : b ≠ a) : (allocation a values kind).lookup b = none :=
  lookup_eq_none.mpr fun hMem => hNe ((Finmap.mem_singleton _ _ _).mp hMem)

/-- A fresh allocation sits next to the heap it was allocated in. -/
theorem alloc_eq {α : Type} (h : Heap) (values : List α) (kind : AllocKind) :
    h.alloc values kind = (⟨freshAllocId h, 0⟩, allocation (freshAllocId h) values kind ∪ h) := by
  refine Prod.ext rfl (ext fun a => ?_)
  rw [lookup_union]
  by_cases ha : a = freshAllocId h
  · subst ha
    have hNone := lookup_eq_none.mpr (notMem_freshAllocId (h := h) rfl)
    simp only [alloc, lookup_insert, hNone, lookup_allocation]
    rfl
  · simp only [alloc, lookup_insert_ne _ _ ha, lookup_allocation_ne ha, Option.merge_none_left]

theorem compatible_freshAllocId {α : Type} (h : Heap) (values : List α) (kind : AllocKind) :
    PartialCommMonoid.Compatible (allocation (freshAllocId h) values kind) h := by
  intro a
  by_cases ha : a = freshAllocId h
  · rw [lookup_eq_none.mpr (notMem_freshAllocId ha)]
    cases (allocation (freshAllocId h) values kind).lookup a <;> trivial
  · rw [lookup_allocation_ne ha]
    trivial

theorem subheap_iff {h h' : Heap} :
    Heap.Subheap h h' ↔ ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest :=
  Iff.rfl

namespace Subheap

@[refl]
theorem refl (h : Heap) : Heap.Subheap h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Subheap h₁ h₂)
    (hSub₂₃ : Heap.Subheap h₂ h₃) : Heap.Subheap h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Subheap ∅ h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Subheap (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Subheap h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

theorem compatible {h h' frame : Heap} (hSub : Heap.Subheap h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Subheap h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Subheap (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

theorem union_mono {A B h₁ h₂ : Heap}
    (hSub₁ : Heap.Subheap A h₁) (hSub₂ : Heap.Subheap B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    hSub₁.compatible hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (hSub₂.compatible
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Heap.Subheap (B ∪ A) (h₂ ∪ A) :=
    Heap.Subheap.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Heap.Subheap (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Heap.Subheap.union_mono_left hSub₁ hCompatible)

end Subheap

/-! ### Reads and writes -/

private theorem lookup_of_cell? {h : Heap} {l : RawPtr T M} {c : Σ α : Type, α}
    (hCell : h.cell? l = some c) :
    ∃ b : Block, h.lookup l.allocId = some (.live b) ∧
      ∃ x, b.cells[l.offset]? = some (.owned x) ∧ c = ⟨b.ty, x⟩ := by
  unfold cell? at hCell
  split at hCell
  · rename_i b hLookup
    split at hCell
    · rename_i x hx
      exact ⟨b, hLookup, x, hx, (Option.some.inj hCell).symm⟩
    · simp at hCell
  · simp at hCell

private theorem cell?_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : ∃ x : α, h.cell? q = some ⟨α, x⟩ := by
  unfold IsValid at hValid
  split at hValid
  · contradiction
  · rename_i β x hCell
    subst hValid
    exact ⟨x, hCell⟩

private theorem lookup_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) :
    ∃ b : Block, h.lookup q.allocId = some (.live b) ∧ b.ty = α ∧
      ∃ x, b.cells[q.offset]? = some (.owned x) := by
  obtain ⟨_, hCell⟩ := cell?_of_isValid hValid
  obtain ⟨b, hLookup, x, hx, hEq⟩ := lookup_of_cell? hCell
  exact ⟨b, hLookup, (congrArg Sigma.fst hEq).symm, x, hx⟩

theorem mem_of_isLive {h : Heap} {l : RawPtr T M} (hLive : IsLive h l) : l.allocId ∈ h := by
  obtain ⟨c, hCell⟩ := Option.isSome_iff_exists.mp hLive
  obtain ⟨b, hLookup, -⟩ := lookup_of_cell? hCell
  exact mem_iff_lookup.mpr (by simp [hLookup])

theorem isLive_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : IsLive h q := by
  obtain ⟨x, hCell⟩ := cell?_of_isValid hValid
  simp [IsLive, hCell]

theorem mem_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : q.allocId ∈ h :=
  mem_of_isLive (isLive_of_isValid hValid)

theorem not_compatible_of_isValid {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid₁ : IsValid h₁ q) (hValid₂ : IsValid h₂ q) :
    ¬ PartialCommMonoid.Compatible h₁ h₂ := by
  intro hCompatible
  obtain ⟨b₁, hLookup₁, -, x₁, hx₁⟩ := lookup_of_isValid hValid₁
  obtain ⟨b₂, hLookup₂, -, x₂, hx₂⟩ := lookup_of_isValid hValid₂
  have hBlock := hCompatible q.allocId
  simp only [hLookup₁, hLookup₂, OptCompatible, BlockSlot.Compatible] at hBlock
  obtain ⟨k₁, t, c₁⟩ := b₁
  obtain ⟨k₂, c₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
  dsimp only at hBlock hx₂
  rw [Block.compatible_mk_iff] at hBlock
  have := (Cell.forall₂_iff_getElem?.mp hBlock.2).2 _ _ _ hx₁ hx₂
  simp [Cell.Compatible] at this

theorem isValid_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) : IsValid (h₁ ∪ h₂) q := by
  obtain ⟨x, hCell⟩ := cell?_of_isValid hValid
  simp [IsValid, cell?_union_left hCell]

theorem isLive_union_left {h₁ h₂ : Heap} {l : RawPtr T M}
    (hLive : IsLive h₁ l) : IsLive (h₁ ∪ h₂) l := by
  obtain ⟨c, hCell⟩ := Option.isSome_iff_exists.mp hLive
  simp [IsLive, cell?_union_left hCell]

/-- Framing: `read` on a bigger heap reads the same value and leaves the frame alone. -/
theorem read_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).read q (isValid_union_left hValid) = Prod.map id (· ∪ h₂) (h₁.read q hValid) := by
  unfold Heap.read
  split
  · rename_i hCell
    have hValidUnion := isValid_union_left (h₂ := h₂) hValid
    simp [IsValid, hCell] at hValidUnion
  · rename_i β value hCell
    split
    · rename_i hCell₁
      simp [IsValid, hCell₁] at hValid
    · rename_i β₁ value₁ hCell₁
      have hCells : (⟨β, value⟩ : Σ α : Type, α) = ⟨β₁, value₁⟩ :=
        Option.some.inj (hCell.symm.trans (cell?_union_left hCell₁))
      cases hCells
      rfl

/-- `setOwned` on a heap whose block at `q` is `b`. -/
private theorem setOwned_of_lookup {α : Type} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α} {b : Block}
    (hLookup : h.lookup q.allocId = some (.live b)) :
    h.setOwned q value hTy =
      h.insert q.allocId
        (.live ⟨b.kind, b.ty, b.cells.set q.offset (.owned (cast (hTy b hLookup).symm value))⟩) := by
  unfold setOwned
  split
  · rename_i b' hLookup'
    have hEq : b' = b := by
      rw [hLookup] at hLookup'
      cases hLookup'
      rfl
    subst hEq
    rfl
  · rename_i hNe
    exact absurd hLookup (hNe b)

/-- Framing for `setOwned`: owning a cell of `h₁` in `h₁ ∪ h₂` is owning it in `h₁`. -/
private theorem setOwned_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M} {value : α}
    {b : Block} (hLookup : h₁.lookup q.allocId = some (.live b)) (hTy : b.ty = α)
    (hTy₁ : ∀ b, h₁.lookup q.allocId = some (.live b) → b.ty = α)
    (hTyUnion : ∀ b, (h₁ ∪ h₂).lookup q.allocId = some (.live b) → b.ty = α) :
    (h₁ ∪ h₂).setOwned q value hTyUnion = h₁.setOwned q value hTy₁ ∪ h₂ := by
  rw [setOwned_of_lookup (lookup_union_live hLookup), setOwned_of_lookup hLookup]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    obtain ⟨k, t, c⟩ := b
    dsimp only at hTy ⊢
    subst hTy
    simp only [cast_eq]
    unfold cellsAt
    rcases hs : h₂.lookup q.allocId with _ | _ | _
    · simp [Option.merge, Cell.joinList_nil_right]
    · simp [Option.merge, BlockSlot.join, Block.join, Cell.joinList_set_owned]
    · simp [Option.merge, BlockSlot.join, Cell.joinList_nil_right]
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

theorem write_union_left {α : Type} {h₁ h₂ : Heap}
    (q : RawPtr α M) (value : α) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).write q value (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.write q value hValid) := by
  obtain ⟨b, hLookup, hTy, -⟩ := lookup_of_isValid hValid
  exact congrArg (Prod.mk ()) (setOwned_union_left hLookup hTy _ _)

/-- After `setOwned` at `q`, the block of `q` owns the cell of `q` and keeps its header. -/
private theorem lookup_setOwned {α : Type} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α} {b : Block}
    (hLookup : h.lookup q.allocId = some (.live b)) :
    ∃ x, (h.setOwned q value hTy).lookup q.allocId =
      some (.live ⟨b.kind, b.ty, b.cells.set q.offset (.owned x)⟩) :=
  ⟨_, by rw [setOwned_of_lookup hLookup, lookup_insert]⟩

private theorem lookup_setOwned_ne {α : Type} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α} {a : AllocId}
    (ha : a ≠ q.allocId) : (h.setOwned q value hTy).lookup a = h.lookup a := by
  unfold setOwned
  split
  · exact lookup_insert_ne _ _ ha
  · rfl

/-- Owning a cell that `h₁` owns or borrows keeps compatibility: a compatible frame does not own or
borrow it. -/
private theorem compatible_setOwned_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    {value : α} {hTy : ∀ b, h₁.lookup q.allocId = some (.live b) → b.ty = α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hExcl : ∀ b, h₁.lookup q.allocId = some (.live b) → b.cells[q.offset]? ≠ some .notOwned) :
    PartialCommMonoid.Compatible (h₁.setOwned q value hTy) h₂ := by
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    have hBlock := hCompatible q.allocId
    rcases hs₁ : h₁.lookup q.allocId with _ | (b₁ | _)
    · unfold setOwned
      split
      · rename_i b hLookup; simp [hs₁] at hLookup
      · show OptCompatible (h₁.lookup _) _
        rw [hs₁]; trivial
    · have hExcl₁ := hExcl b₁ hs₁
      obtain ⟨x, hx⟩ := lookup_setOwned (value := value) (hTy := hTy) hs₁
      show OptCompatible _ _
      rw [hx]
      rw [hs₁] at hBlock
      rcases hs₂ : h₂.lookup q.allocId with _ | (b₂ | _)
      · trivial
      · rw [hs₂] at hBlock
        simp only [OptCompatible, BlockSlot.Compatible] at hBlock ⊢
        obtain ⟨k₁, t, c₁⟩ := b₁
        dsimp only at hExcl₁
        obtain ⟨k₂, c₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
        dsimp only at hBlock hs₂ ⊢
        rw [Block.compatible_mk_iff] at hBlock ⊢
        refine ⟨hBlock.1, Cell.forall₂_iff_getElem?.mpr ⟨by simp [hBlock.2.length_eq], ?_⟩⟩
        intro i y z hy hz
        rw [List.getElem?_set] at hy
        split at hy
        · rename_i hi
          subst hi
          have hi₁ : q.offset < c₁.length := by
            have := hBlock.2.length_eq; have := (List.getElem?_eq_some_iff.mp hz).1; omega
          rw [List.getElem?_eq_getElem hi₁] at hExcl₁
          have hz' := Cell.eq_notOwned_of_compatible
            ((Cell.forall₂_iff_getElem?.mp hBlock.2).2 _ _ _ (List.getElem?_eq_getElem hi₁) hz)
            (fun h => hExcl₁ (congrArg some h))
          subst hz'
          cases y <;> trivial
        · exact (Cell.forall₂_iff_getElem?.mp hBlock.2).2 i y z hy hz
      · rw [hs₂] at hBlock; exact hBlock
    · unfold setOwned
      split
      · rename_i b hLookup; simp [hs₁] at hLookup
      · show OptCompatible (h₁.lookup _) _
        rw [hs₁] at hBlock ⊢; exact hBlock
  · show OptCompatible ((h₁.setOwned q value hTy).lookup a) _
    rw [lookup_setOwned_ne ha]
    exact hCompatible a

theorem compatible_write_left {α : Type} {q : RawPtr α M} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible (h₁.write q value hValid).2 h₂ :=
  compatible_setOwned_left (hTy := ty_of_isValid hValid) hCompatible fun b hLookup => by
    obtain ⟨b₁, hLookup₁, -, x, hx⟩ := lookup_of_isValid hValid
    rw [hLookup₁] at hLookup
    cases hLookup
    simp [hx]

/-! ### Deallocation -/

private theorem canDealloc_iff' {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind} :
    CanDealloc h q n kind ↔
      q.offset = 0 ∧ ∃ b, h.lookup q.allocId = some (.live b) ∧ b.kind = kind ∧
        b.cells.length = n ∧ ∀ i < n, IsLive h (q.shift i) := by
  unfold CanDealloc
  constructor
  · rintro ⟨hOffset, hBlock⟩
    refine ⟨hOffset, ?_⟩
    split at hBlock
    · rename_i b hLookup
      exact ⟨b, hLookup, hBlock⟩
    · contradiction
  · rintro ⟨hOffset, b, hLookup, hBlock⟩
    refine ⟨hOffset, ?_⟩
    rw [hLookup]
    exact hBlock

/-- Only the start of a block can be deallocated. -/
theorem offset_eq_zero_of_canDealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) : q.offset = 0 :=
  (canDealloc_iff'.mp hDealloc).1

/-- Every cell of a deallocated block must be owned. -/
theorem isLive_of_canDealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) {i : Nat} (hi : i < n) : IsLive h (q.shift i) := by
  obtain ⟨-, -, -, -, -, hLive⟩ := canDealloc_iff'.mp hDealloc
  exact hLive i hi

theorem canDealloc_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h₁ q n kind) : CanDealloc (h₁ ∪ h₂) q n kind := by
  obtain ⟨hOffset, b, hLookup, hKind, hLen, hLive⟩ := canDealloc_iff'.mp hDealloc
  exact canDealloc_iff'.mpr ⟨hOffset, _, lookup_union_live hLookup, hKind,
    by rw [Cell.length_joinList, hLen], fun i hi => isLive_union_left (hLive i hi)⟩

theorem compatible_dealloc_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : CanDealloc h₁ q n kind)
    (hNotMem : q.allocId ∉ h₂) :
    PartialCommMonoid.Compatible (h₁.dealloc q n kind hDealloc).2 h₂ := by
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    show OptCompatible _ _
    rw [lookup_eq_none.mpr hNotMem]
    cases (h₁.dealloc q n kind hDealloc).2.lookup q.allocId <;> trivial
  · show OptCompatible ((h₁.insert _ _).lookup a) _
    rw [lookup_insert_ne _ _ ha]
    exact hCompatible a

theorem dealloc_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h₁ q n kind) :
    (h₁ ∪ h₂).dealloc q n kind (canDealloc_union_left hDealloc) =
      Prod.map id (· ∪ h₂) (h₁.dealloc q n kind hDealloc) := by
  refine Prod.ext rfl (ext fun a => ?_)
  show ((h₁ ∪ h₂).insert _ _).lookup a = ((h₁.insert _ _) ∪ h₂).lookup a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    cases h₂.lookup q.allocId <;> rfl
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

private theorem lookup_dealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) :
    (h.dealloc q n kind hDealloc).2.lookup q.allocId = some .freed :=
  lookup_insert _ _ _

/-- Deallocated blocks stay in the heap, so their allocation id is never handed out again. -/
theorem mem_dealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) : q.allocId ∈ (h.dealloc q n kind hDealloc).2 :=
  mem_iff_lookup.mpr (by simp [lookup_dealloc hDealloc])

/-- No cell of a deallocated block can be read or written. -/
theorem not_isLive_dealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    {l : RawPtr T M'}
    (hDealloc : CanDealloc h q n kind) (hId : l.allocId = q.allocId) :
    ¬ IsLive (h.dealloc q n kind hDealloc).2 l := by
  simp [IsLive, cell?, hId, lookup_dealloc hDealloc]

/-- A deallocated block cannot be deallocated again. -/
theorem not_canDealloc_dealloc {h : Heap} {q : RawPtr α M} {r : RawPtr β M'} {n n' : Nat}
    {kind kind' : AllocKind} (hDealloc : CanDealloc h q n kind)
    (hId : r.allocId = q.allocId) :
    ¬ CanDealloc (h.dealloc q n kind hDealloc).2 r n' kind' := by
  rw [canDealloc_iff']
  rintro ⟨-, b, hLookup, -⟩
  rw [hId, lookup_dealloc hDealloc] at hLookup
  cases hLookup

/-- A cell of a deallocated block cannot be borrowed back to life. -/
theorem not_isBorrowed_dealloc {h : Heap} {q : RawPtr α M} {r : RawPtr β M'} {n : Nat}
    {kind : AllocKind} (hDealloc : CanDealloc h q n kind)
    (hId : r.allocId = q.allocId) :
    ¬ IsBorrowed (h.dealloc q n kind hDealloc).2 r := by
  simp [IsBorrowed, hId, lookup_dealloc hDealloc]

/-! ### Allocation -/

private theorem lookup_alloc {α : Type} (h : Heap) (values : List α) (kind : AllocKind) :
    (h.alloc values kind).2.lookup (freshAllocId h) =
      some (.live ⟨kind, α, values.map .owned⟩) :=
  lookup_insert _ _ _

/-- Allocation leaves the blocks already in the heap untouched. -/
theorem isLive_alloc_of_mem {β : Type} {h : Heap} {values : List β} {kind : AllocKind}
    {l : RawPtr T M} (hMem : l.allocId ∈ h) : IsLive (h.alloc values kind).2 l ↔ IsLive h l := by
  have hNe : l.allocId ≠ freshAllocId h := fun hEq => notMem_freshAllocId hEq hMem
  simp only [IsLive, cell?, alloc, lookup_insert_ne _ _ hNe]

/-- Even an empty allocation reserves its id. -/
theorem mem_alloc {α : Type} {kind : AllocKind} (h : Heap) (values : List α) :
    freshAllocId h ∈ (h.alloc values kind).2 :=
  mem_iff_lookup.mpr (by simp [lookup_alloc])

/-- The values of a fresh allocation are live, whatever the type of the pointer. -/
theorem isLive_alloc {α : Type} {h : Heap} {values : List α} {kind : AllocKind} {i : Nat}
    (hIndex : i < values.length) :
    IsLive (h.alloc values kind).2 (⟨freshAllocId h, i⟩ : RawPtr T M) := by
  simp [IsLive, cell?, lookup_alloc, hIndex]

/-- A fresh allocation has no cell past its values. -/
theorem not_isLive_alloc_of_le {α : Type} {h : Heap} {values : List α} {kind : AllocKind}
    {i : Nat} (hIndex : values.length ≤ i) :
    ¬ IsLive (h.alloc values kind).2 (⟨freshAllocId h, i⟩ : RawPtr T M) := by
  simp [IsLive, cell?, lookup_alloc, List.getElem?_eq_none hIndex]

/-- A fresh allocation can be deallocated whole, and only for its kind. -/
theorem canDealloc_alloc_iff {α : Type} {β : Type u} (h : Heap) (values : List α) (n : Nat)
    (kind kind' : AllocKind) :
    CanDealloc (h.alloc values kind).2 (⟨freshAllocId h, 0⟩ : MutRawPtr β) n kind' ↔
      kind = kind' ∧ values.length = n := by
  rw [canDealloc_iff']
  constructor
  · rintro ⟨-, b, hLookup, hKind, hLen, -⟩
    rw [lookup_alloc] at hLookup
    cases hLookup
    exact ⟨hKind, by simpa using hLen⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, _, by rw [lookup_alloc], rfl, by simp,
      fun i hi => by simpa [RawPtr.shift] using isLive_alloc hi⟩

/-! ### Singletons -/

/-- Singletons of different blocks are always compatible. -/
theorem compatible_singleton_of_allocId_ne {α β : Type} {q : RawPtr α M} {r : RawPtr β M'}
    {value₁ : α} {value₂ : β} {kind₁ kind₂ : AllocKind} {len₁ len₂ : Nat}
    (hNe : q.allocId ≠ r.allocId) :
    PartialCommMonoid.Compatible
      (singleton q value₁ kind₁ len₁) (singleton r value₂ kind₂ len₂) := by
  intro a
  show OptCompatible _ _
  by_cases ha : a = r.allocId
  · rw [lookup_singleton_ne fun hq => hNe (hq.symm.trans ha)]
    trivial
  · rw [lookup_singleton_ne ha]
    cases (singleton q value₁ kind₁ len₁).lookup a <;> trivial

/-- Singletons at different offsets are compatible. In the same block they must agree on the
type, the kind and the length. -/
theorem compatible_singleton {α : Type} {q : RawPtr α M} {r : RawPtr α M'} {value₁ value₂ : α}
    {kind : AllocKind} {len : Nat} (hOffset : q.offset ≠ r.offset) :
    PartialCommMonoid.Compatible
      (singleton q value₁ kind len) (singleton r value₂ kind len) := by
  by_cases hb : q.allocId = r.allocId
  swap
  · exact compatible_singleton_of_allocId_ne hb
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    show OptCompatible _ _
    rw [lookup_singleton, hb, lookup_singleton]
    simp only [OptCompatible, BlockSlot.Compatible, Block.compatible_mk_iff, true_and]
    refine Cell.forall₂_iff_getElem?.mpr ⟨by simp, fun i x y hx hy => ?_⟩
    simp only [List.getElem?_set, List.length_replicate, List.getElem?_replicate] at hx hy
    split at hx <;> split at hy <;> simp_all
    all_goals (try obtain ⟨-, rfl⟩ := hx); all_goals (try obtain ⟨-, rfl⟩ := hy)
    all_goals trivial
  · show OptCompatible _ _
    rw [lookup_singleton_ne ha]
    trivial

theorem isValid_singleton {α : Type} (q : RawPtr α M) (value : α) (kind : AllocKind) {len : Nat}
    (hOffset : q.offset < len) : IsValid (singleton q value kind len) q := by
  simp [IsValid, cell?, lookup_singleton, hOffset]

theorem read_singleton {α : Type} (q : RawPtr α M) (value : α) (kind : AllocKind) (len : Nat)
    (hValid : IsValid (singleton q value kind len) q) :
    (singleton q value kind len).read q hValid = (value, singleton q value kind len) := by
  unfold Heap.read
  split
  · rename_i hCell
    simp [IsValid, hCell] at hValid
  · rename_i β stored hCell
    have hOffset : q.offset < len := by
      by_contra hLe
      simp [cell?, lookup_singleton, hLe] at hCell
    simp [cell?, lookup_singleton, hOffset] at hCell
    obtain ⟨rfl, hStored⟩ := hCell
    cases hStored
    rfl

theorem write_singleton {α : Type} (q : RawPtr α M) (oldValue newValue : α) (kind : AllocKind)
    (len : Nat) (hValid : IsValid (singleton q oldValue kind len) q) :
    (singleton q oldValue kind len).write q newValue hValid =
      ((), singleton q newValue kind len) := by
  refine congrArg (Prod.mk ()) ?_
  show setOwned _ _ _ _ = _
  rw [setOwned_of_lookup (lookup_singleton q oldValue kind len)]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_singleton]
    simp [List.set_set]
  · rw [lookup_insert_ne _ _ ha, lookup_singleton_ne ha, lookup_singleton_ne ha]

theorem Subheap.isValid {α : Type} {A h : Heap} {q : RawPtr α M} (hSub : Heap.Subheap A h)
    (hValid : IsValid A q) : IsValid h q := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isValid_union_left hValid

theorem Subheap.isLive {A h : Heap} {l : RawPtr T M} (hSub : Heap.Subheap A h)
    (hLive : IsLive A l) : IsLive h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isLive_union_left hLive

theorem read_of_subheap {α : Type} {q : RawPtr α M} {value : α} {kind : AllocKind} {len : Nat}
    {h : Heap} (hSub : Heap.Subheap (singleton q value kind len) h)
    (hOffset : q.offset < len) (hValid : IsValid h q) : (h.read q hValid).1 = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hValidSingleton := isValid_singleton q value kind hOffset
  rw [show hValid = isValid_union_left hValidSingleton from
      Subsingleton.elim _ _,
    read_union_left hValidSingleton, read_singleton]
  rfl

/-- The block of a fresh allocation is the union of one singleton per value. -/
theorem Subheap.singleton_allocation {α : Type} (a : AllocId) (values : List α)
    (kind : AllocKind) {i : Nat} (hIndex : i < values.length) :
    Heap.Subheap (singleton (⟨a, i⟩ : MutRawPtr α) values[i] kind values.length)
      (allocation a values kind) := by
  let rest : Heap := ⟨Finmap.singleton a
    (.live ⟨kind, α, (values.map Cell.owned).set i .notOwned⟩)⟩
  have hRest : ∀ b, rest.lookup b = if b = a then
      some (.live ⟨kind, α, (values.map Cell.owned).set i .notOwned⟩) else none := by
    intro b
    split
    · subst_vars; exact Finmap.lookup_singleton_eq
    · rename_i hNe
      exact lookup_eq_none.mpr fun hMem => hNe ((Finmap.mem_singleton _ _ _).mp hMem)
  have hCells : List.Forall₂ Cell.Compatible
      ((List.replicate values.length Cell.notOwned).set i (Cell.owned values[i]))
      ((values.map Cell.owned).set i .notOwned) := by
    refine Cell.forall₂_iff_getElem?.mpr ⟨by simp, fun j x y hx hy => ?_⟩
    simp only [List.getElem?_set, List.length_replicate, List.getElem?_replicate,
      List.length_map, List.getElem?_map] at hx hy
    split at hx <;> split at hy <;> simp_all
    all_goals (try obtain ⟨-, rfl⟩ := hx); all_goals (try obtain ⟨-, rfl⟩ := hy)
    all_goals trivial
  refine ⟨rest, fun b => ?_, ext fun b => ?_⟩
  · by_cases hb : b = a
    · subst hb
      show OptCompatible ((singleton _ _ _ _).lookup _) _
      rw [lookup_singleton, hRest, ite_eq_left rfl]
      exact (Block.compatible_mk_iff _ _ _ _ _).mpr ⟨rfl, hCells⟩
    · show OptCompatible ((singleton _ _ _ _).lookup _) _
      rw [lookup_singleton_ne hb]
      trivial
  · rw [lookup_union]
    by_cases hb : b = a
    · subst hb
      rw [lookup_singleton, hRest, ite_eq_left rfl]
      rw [lookup_allocation]
      dsimp only
      simp only [Option.merge, BlockSlot.join, Block.join_mk, Cell.joinList_of_forall₂ hCells]
      congr 3
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_zipWith, List.getElem?_set, List.length_replicate,
        List.getElem?_replicate, List.length_map, List.getElem?_map]
      by_cases hj : j < values.length <;> by_cases hij : i = j <;>
        simp_all [Cell.join]
    · rw [lookup_singleton_ne hb, hRest, ite_eq_right hb]
      exact lookup_allocation_ne hb

/-! ### Borrows -/

/-- `borrow` on a heap whose block at `q` is `b`. -/
private theorem borrow_snd_of_lookup {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) {b : Block} (hLookup : h.lookup q.allocId = some (.live b)) :
    (h.borrow q hValid).2 =
      h.insert q.allocId (.live ⟨b.kind, b.ty, b.cells.set q.offset .borrowed⟩) := by
  simp only [borrow, hLookup]

theorem borrow_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).borrow q (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.borrow q hValid) := by
  obtain ⟨b, hLookup, hTy, x, hx⟩ := lookup_of_isValid hValid
  refine Prod.ext (congrArg Prod.fst (read_union_left (h₂ := h₂) hValid) :) ?_
  dsimp only [Prod.map]
  rw [borrow_snd_of_lookup _ (lookup_union_live hLookup), borrow_snd_of_lookup _ hLookup]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    have hBlock := hCompatible q.allocId
    rw [hLookup] at hBlock
    unfold cellsAt
    rcases hs : h₂.lookup q.allocId with _ | (b₂ | _)
    · simp [Option.merge, Cell.joinList_nil_right]
    · rw [hs] at hBlock
      simp only [OptCompatible, BlockSlot.Compatible] at hBlock
      obtain ⟨k, t, c⟩ := b
      obtain ⟨k₂, c₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
      dsimp only at hBlock hx ⊢
      rw [Block.compatible_mk_iff] at hBlock
      simp only [Option.merge, BlockSlot.join, Block.join_mk, Block.cellsAs_mk]
      rw [Cell.joinList_set_borrowed]
    · rw [hs] at hBlock; exact hBlock.elim
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

theorem compatible_borrow_left {α : Type} {q : RawPtr α M} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible (h₁.borrow q hValid).2 h₂ := by
  obtain ⟨b, hLookup, -, x, hx⟩ := lookup_of_isValid hValid
  rw [borrow_snd_of_lookup hValid hLookup]
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    show OptCompatible ((h₁.insert _ _).lookup _) _
    rw [lookup_insert]
    have hBlock := hCompatible q.allocId
    rw [hLookup] at hBlock
    rcases hs : h₂.lookup q.allocId with _ | (b₂ | _)
    · trivial
    · rw [hs] at hBlock
      simp only [OptCompatible, BlockSlot.Compatible] at hBlock ⊢
      obtain ⟨k, t, c⟩ := b
      obtain ⟨k₂, c₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
      dsimp only at hBlock hx ⊢
      rw [Block.compatible_mk_iff] at hBlock ⊢
      refine ⟨hBlock.1, Cell.forall₂_iff_getElem?.mpr ⟨by simp [hBlock.2.length_eq], ?_⟩⟩
      intro i y z hy hz
      rw [List.getElem?_set] at hy
      split at hy
      · rename_i hi
        subst hi
        simp at hy; obtain ⟨-, rfl⟩ := hy
        rw [Cell.eq_notOwned_of_compatible ((Cell.forall₂_iff_getElem?.mp hBlock.2).2 _ _ _ hx hz)
          (by simp)]
        trivial
      · exact (Cell.forall₂_iff_getElem?.mp hBlock.2).2 i y z hy hz
    · rw [hs] at hBlock; exact hBlock
  · show OptCompatible ((h₁.insert _ _).lookup a) _
    rw [lookup_insert_ne _ _ ha]
    exact hCompatible a

/-- A borrowed cell holds no value: no access goes through it until `endBorrow`. -/
theorem not_isLive_borrow {α : Type} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    ¬ IsLive (h.borrow q hValid).2 q := by
  obtain ⟨b, hLookup, -⟩ := lookup_of_isValid hValid
  rw [borrow_snd_of_lookup hValid hLookup]
  simp only [IsLive, cell?, lookup_insert, List.getElem?_set]
  split <;> simp_all

/-- A borrowed cell can be given back. -/
theorem isBorrowed_borrow {α : Type} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    IsBorrowed (h.borrow q hValid).2 q := by
  obtain ⟨b, hLookup, hTy, x, hx⟩ := lookup_of_isValid hValid
  rw [borrow_snd_of_lookup hValid hLookup]
  have hi : q.offset < b.cells.length := (List.getElem?_eq_some_iff.mp hx).1
  simp [IsBorrowed, lookup_insert, hTy, hi]

private theorem lookup_borrowedBlock {α : Type} (q : RawPtr α M) (kind : AllocKind) (len : Nat) :
    (borrowedBlock q kind len).lookup q.allocId =
      some (.live ⟨kind, α, (List.replicate len .notOwned).set q.offset .borrowed⟩) :=
  Finmap.lookup_singleton_eq

private theorem lookup_header {α : Type} (q : RawPtr α M) (kind : AllocKind) (len : Nat) :
    (header q kind len).lookup q.allocId =
      some (.live ⟨kind, α, List.replicate len .notOwned⟩) :=
  Finmap.lookup_singleton_eq

theorem borrow_singleton {α : Type} (q : RawPtr α M) (value : α) (kind : AllocKind) (len : Nat)
    (hValid : IsValid (singleton q value kind len) q) :
    (singleton q value kind len).borrow q hValid = (value, borrowedBlock q kind len) := by
  refine Prod.ext (congrArg Prod.fst (read_singleton q value kind len hValid) :) ?_
  rw [borrow_snd_of_lookup hValid (lookup_singleton q value kind len)]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_borrowedBlock]
    simp only [List.set_set]
  · rw [lookup_insert_ne _ _ ha, lookup_singleton_ne ha]
    exact (lookup_eq_none.mpr fun hMem => ha ((Finmap.mem_singleton _ _ _).mp hMem)).symm

theorem isBorrowed_borrowedBlock {α : Type} (q : RawPtr α M) (kind : AllocKind) {len : Nat}
    (hOffset : q.offset < len) : IsBorrowed (borrowedBlock q kind len) q := by
  unfold IsBorrowed
  rw [lookup_borrowedBlock]
  simp [hOffset]

/-- The borrow of a cell wins over any other fragment of it. -/
theorem isBorrowed_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hBorrowed : IsBorrowed h₁ q) : IsBorrowed (h₁ ∪ h₂) q := by
  unfold IsBorrowed at hBorrowed ⊢
  split at hBorrowed
  · rename_i b hLookup
    rw [lookup_union_live hLookup]
    refine ⟨hBorrowed.1, ?_⟩
    rw [Cell.getElem?_joinList]
    split
    · rename_i hLen
      have hi : q.offset < (h₂.cellsAt q.allocId b.ty).length := by
        rw [← hLen]; exact (List.getElem?_eq_some_iff.mp hBorrowed.2).1
      simp [hBorrowed.2, List.getElem?_eq_getElem hi, Cell.join]
    · exact hBorrowed.2
  · exact hBorrowed.elim

/-- Framing for `endBorrow`. -/
theorem endBorrow_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M) (value : α)
    (hBorrowed : IsBorrowed h₁ q) :
    (h₁ ∪ h₂).endBorrow q value (isBorrowed_union_left hBorrowed) =
      Prod.map id (· ∪ h₂) (h₁.endBorrow q value hBorrowed) := by
  unfold IsBorrowed at hBorrowed
  split at hBorrowed
  · rename_i b hLookup
    exact congrArg (Prod.mk ()) (setOwned_union_left hLookup hBorrowed.1 _ _)
  · exact hBorrowed.elim

theorem compatible_endBorrow_left {α : Type} {q : RawPtr α M} {value : α} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hBorrowed : IsBorrowed h₁ q) :
    PartialCommMonoid.Compatible (h₁.endBorrow q value hBorrowed).2 h₂ :=
  compatible_setOwned_left (hTy := ty_of_isBorrowed hBorrowed) hCompatible fun b hLookup => by
    unfold IsBorrowed at hBorrowed
    rw [hLookup] at hBorrowed
    simp [hBorrowed.2]

theorem endBorrow_borrowedBlock {α : Type} (q : RawPtr α M) (value : α) (kind : AllocKind)
    (len : Nat) (hBorrowed : IsBorrowed (borrowedBlock q kind len) q) :
    (borrowedBlock q kind len).endBorrow q value hBorrowed = ((), singleton q value kind len) := by
  refine congrArg (Prod.mk ()) ?_
  show setOwned _ _ _ _ = _
  rw [setOwned_of_lookup (lookup_borrowedBlock q kind len)]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_singleton]
    simp [List.set_set]
  · rw [lookup_insert_ne _ _ ha, lookup_singleton_ne ha]
    exact lookup_eq_none.mpr fun hMem => ha ((Finmap.mem_singleton _ _ _).mp hMem)

end Heap

end Aeneas.Std
