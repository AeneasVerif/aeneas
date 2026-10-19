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

/-- A fragment compatible with owned or borrowed cells owns none of them. -/
private theorem eq_replicate_of_forall₂ {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂)
    (hOwned : ∀ (i : Nat) (x : Cell α), l₁[i]? = some x → x ≠ .notOwned) :
    l₂ = List.replicate l₂.length (.notOwned : Cell α) := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
    rw [List.length_cons, List.replicate_succ,
      eq_notOwned_of_compatible hc (hOwned 0 _ rfl), ← ih fun i x hx => hOwned (i + 1) x hx]

private theorem forall₂_replicate_notOwned (n : Nat) :
    List.Forall₂ Compatible (List.replicate n (.notOwned : Cell α)) (List.replicate n .notOwned) := by
  induction n <;> simp_all [List.replicate_succ, Compatible]

private theorem joinList_replicate_notOwned (n : Nat) :
    joinList (List.replicate n (.notOwned : Cell α)) (List.replicate n .notOwned) =
      List.replicate n .notOwned := by
  simp [joinList, join]

/-- The cells of `joinList l₁ l₂` are all `notOwned` iff the cells of both are. -/
private theorem notOwned_joinList {l₁ l₂ : List (Cell α)} (h : List.Forall₂ Compatible l₁ l₂) :
    (∀ x ∈ joinList l₁ l₂, x = .notOwned) ↔
      (∀ x ∈ l₁, x = .notOwned) ∧ (∀ x ∈ l₂, x = .notOwned) := by
  rw [joinList_of_forall₂ h]
  induction h with
  | nil => simp
  | @cons x y l₁ l₂ _ _ ih =>
    simp only [List.zipWith_cons_cons, List.forall_mem_cons, ih]
    cases x <;> cases y <;> simp [join] <;> tauto

/-- Setting a cell that is not `notOwned` (because it is out of range) keeps all cells `notOwned`. -/
private theorem forall_notOwned_set {l : List (Cell α)} {i : Nat} {c : Cell α}
    (hl : ∀ x ∈ l, x = .notOwned) (hi : l[i]? ≠ some .notOwned) :
    ∀ x ∈ l.set i c, x = .notOwned := by
  have hLen : l.length ≤ i := by
    refine Nat.le_of_not_lt fun h => hi ?_
    rw [List.getElem?_eq_getElem h, hl _ (List.getElem_mem h)]
  rwa [List.set_eq_of_length_le hLen]

end Cell

/-! ### Blocks -/

namespace DeallocRight


@[simp] private theorem join_none (r : DeallocRight) : r.join .none = r := by
  cases r <;> rfl
private theorem join_comm {r₁ r₂ : DeallocRight} (h : r₁ = .none ∨ r₂ = .none) :
    r₁.join r₂ = r₂.join r₁ := by
  cases r₁ <;> cases r₂ <;> simp_all [join]

private theorem join_assoc (r₁ r₂ r₃ : DeallocRight) :
    (r₁.join r₂).join r₃ = r₁.join (r₂.join r₃) := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> rfl

/-- The conditions on the rights in `Block.Compatible`, reassociated. `A`, `B` and `C` say that
the three fragments own no cell. -/
private theorem compatible_assoc (r₁ r₂ r₃ : DeallocRight) (A B C : Prop) :
    ((r₁ = .none ∨ r₂ = .none) ∧ (r₁ = .freed → B) ∧ (r₂ = .freed → A)) ∧
        ((r₁.join r₂ = .none ∨ r₃ = .none) ∧ (r₁.join r₂ = .freed → C) ∧ (r₃ = .freed → A ∧ B)) ↔
      ((r₂ = .none ∨ r₃ = .none) ∧ (r₂ = .freed → C) ∧ (r₃ = .freed → B)) ∧
        ((r₁ = .none ∨ r₂.join r₃ = .none) ∧ (r₁ = .freed → B ∧ C) ∧ (r₂.join r₃ = .freed → A)) := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp [join] <;> tauto

end DeallocRight

namespace Block

@[simp] private theorem cellsAs_mk (k : AllocKind) (t : Type v) (c : List (Cell t))
    (r : DeallocRight) : (⟨k, t, c, r⟩ : Block).cellsAs t = c := by
  simp [cellsAs]

private theorem compatible_mk_iff (k₁ k₂ : AllocKind) (t : Type v) (c₁ c₂ : List (Cell t))
    (r₁ r₂ : DeallocRight) :
    Compatible ⟨k₁, t, c₁, r₁⟩ ⟨k₂, t, c₂, r₂⟩ ↔
      k₁ = k₂ ∧ List.Forall₂ Cell.Compatible c₁ c₂ ∧ (r₁ = .none ∨ r₂ = .none) ∧
        (r₁ = .freed → ∀ x ∈ c₂, x = .notOwned) ∧ (r₂ = .freed → ∀ x ∈ c₁, x = .notOwned) := by
  simp only [Compatible, cellsAs_mk, true_and]

@[simp] private theorem join_mk (k₁ k₂ : AllocKind) (t : Type v) (c₁ c₂ : List (Cell t))
    (r₁ r₂ : DeallocRight) :
    join ⟨k₁, t, c₁, r₁⟩ ⟨k₂, t, c₂, r₂⟩ = ⟨k₁, t, Cell.joinList c₁ c₂, r₁.join r₂⟩ := by
  simp [join]

/-- Compatible blocks have the same type. -/
private theorem eq_mk_of_compatible {b₁ b₂ : Block} (h : Compatible b₁ b₂) :
    ∃ k₂ c₂ r₂, b₂ = ⟨k₂, b₁.ty, c₂, r₂⟩ := by
  obtain ⟨k₂, t₂, c₂, r₂⟩ := b₂
  obtain ⟨-, hTy, -⟩ := h
  dsimp only at hTy
  subst hTy
  exact ⟨k₂, c₂, r₂, rfl⟩

private theorem compatible_symm {b₁ b₂ : Block} (h : Compatible b₁ b₂) : Compatible b₂ b₁ := by
  obtain ⟨k₁, t, c₁, r₁⟩ := b₁
  obtain ⟨k₂, c₂, r₂, rfl⟩ := eq_mk_of_compatible h
  dsimp only at h ⊢
  rw [compatible_mk_iff] at h ⊢
  exact ⟨h.1.symm, Cell.forall₂_symm h.2.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩

private theorem join_comm {b₁ b₂ : Block} (h : Compatible b₁ b₂) : join b₁ b₂ = join b₂ b₁ := by
  obtain ⟨k₁, t, c₁, r₁⟩ := b₁
  obtain ⟨k₂, c₂, r₂, rfl⟩ := eq_mk_of_compatible h
  dsimp only at h ⊢
  rw [compatible_mk_iff] at h
  rw [join_mk, join_mk, h.1, Cell.joinList_comm h.2.1, DeallocRight.join_comm h.2.2.1]

private theorem compatible_assoc' (a b c : Block) :
    Compatible a b ∧ Compatible (join a b) c ↔ Compatible b c ∧ Compatible a (join b c) := by
  obtain ⟨ka, t, ca, ra⟩ := a
  constructor
  · rintro ⟨hab, habc⟩
    obtain ⟨kb, cb, rb, rfl⟩ := eq_mk_of_compatible hab
    dsimp only at hab habc ⊢
    rw [join_mk] at habc
    obtain ⟨kc, cc, rc, rfl⟩ := eq_mk_of_compatible habc
    dsimp only at habc ⊢
    rw [join_mk]
    simp only [compatible_mk_iff] at hab habc ⊢
    have ⟨hbc, ha⟩ := (Cell.forall₂_joinList_assoc _ _ _).mp ⟨hab.2.1, habc.2.1⟩
    rw [Cell.notOwned_joinList hab.2.1] at habc
    rw [Cell.notOwned_joinList hbc]
    have hr := (DeallocRight.compatible_assoc ra rb rc _ _ _).mp ⟨hab.2.2, habc.2.2⟩
    exact ⟨⟨hab.1.symm.trans habc.1, hbc, hr.1⟩, hab.1, ha, hr.2⟩
  · rintro ⟨hbc, habc⟩
    obtain ⟨kb, tb, cb, rb⟩ := b
    obtain ⟨kc, cc, rc, rfl⟩ := eq_mk_of_compatible hbc
    dsimp only at hbc habc ⊢
    rw [join_mk] at habc
    have hTy : tb = t := habc.2.1
    subst hTy
    rw [join_mk]
    simp only [compatible_mk_iff] at hbc habc ⊢
    have ⟨hab, ha⟩ := (Cell.forall₂_joinList_assoc _ _ _).mpr ⟨hbc.2.1, habc.2.1⟩
    rw [Cell.notOwned_joinList hbc.2.1] at habc
    rw [Cell.notOwned_joinList hab]
    have hr := (DeallocRight.compatible_assoc ra rb rc _ _ _).mpr ⟨hbc.2.2, habc.2.2⟩
    exact ⟨⟨habc.1, hab, hr.1⟩, habc.1.trans hbc.1, ha, hr.2⟩

private theorem join_assoc {a b c : Block} (hab : Compatible a b)
    (habc : Compatible (join a b) c) : join (join a b) c = join a (join b c) := by
  obtain ⟨ka, t, ca, ra⟩ := a
  obtain ⟨kb, cb, rb, rfl⟩ := eq_mk_of_compatible hab
  dsimp only at hab habc ⊢
  rw [join_mk] at habc
  obtain ⟨kc, cc, rc, rfl⟩ := eq_mk_of_compatible habc
  dsimp only at habc ⊢
  simp only [compatible_mk_iff] at hab habc
  simp only [join_mk, Cell.joinList_assoc hab.2.1 habc.2.1, DeallocRight.join_assoc]

end Block

private theorem optCompatible_symm {o₁ o₂ : Option Block} (h : OptCompatible o₁ o₂) :
    OptCompatible o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp_all [OptCompatible, Block.compatible_symm]

private theorem merge_join_comm {o₁ o₂ : Option Block} (h : OptCompatible o₁ o₂) :
    Option.merge Block.join o₁ o₂ = Option.merge Block.join o₂ o₁ := by
  match o₁, o₂, h with
  | some _, some _, h => exact congrArg some (Block.join_comm h)
  | some _, none, _ => rfl
  | none, some _, _ => rfl
  | none, none, _ => rfl

private theorem optCompatible_assoc (a b c : Option Block) :
    OptCompatible a b ∧ OptCompatible (Option.merge Block.join a b) c ↔
      OptCompatible b c ∧ OptCompatible a (Option.merge Block.join b c) := by
  cases a <;> cases b <;> cases c <;> simp [OptCompatible, Option.merge, Block.compatible_assoc']

private theorem merge_join_assoc {a b c : Option Block} (hab : OptCompatible a b)
    (habc : OptCompatible (Option.merge Block.join a b) c) :
    Option.merge Block.join (Option.merge Block.join a b) c =
      Option.merge Block.join a (Option.merge Block.join b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [OptCompatible, Option.merge, Block.join_assoc]

/-! ### Heaps -/

namespace Heap

private theorem ext {h₁ h₂ : Heap} (hEq : ∀ a, h₁.lookup a = h₂.lookup a) : h₁ = h₂ := by
  obtain ⟨m₁⟩ := h₁
  obtain ⟨m₂⟩ := h₂
  congr 1
  exact Finmap.ext_lookup hEq

private theorem lookup_foldr (h₁ h₂ : Heap) (a : AllocId) (m : Finmap fun _ : AllocId => Block)
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
    (h₁ ∪ h₂).lookup a = Option.merge Block.join (h₁.lookup a) (h₂.lookup a) := by
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

private theorem lookup_insert (h : Heap) (a : AllocId) (s : Block) :
    (h.insert a s).lookup a = some s :=
  Finmap.lookup_insert _

private theorem lookup_insert_ne (h : Heap) {a b : AllocId} (s : Block) (hNe : b ≠ a) :
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
private noncomputable def cellsAt (h : Heap) (a : AllocId) (t : Type v) : List (Cell t) :=
  match h.lookup a with
  | some b => b.cellsAs t
  | _ => []

/-- The right of `h` on the block `a`. -/
private def rightAt (h : Heap) (a : AllocId) : DeallocRight :=
  match h.lookup a with
  | some b => b.right
  | _ => .none

/-- A block of `h₁` stays in `h₁ ∪ h₂`, with the same header: the cells and the right of `h₂` are
joined into it. -/
private theorem lookup_union_some {h₁ h₂ : Heap} {a : AllocId} {b : Block}
    (hLookup : h₁.lookup a = some b) :
    (h₁ ∪ h₂).lookup a = some ⟨b.kind, b.ty, Cell.joinList b.cells (h₂.cellsAt a b.ty),
      b.right.join (h₂.rightAt a)⟩ := by
  rw [lookup_union, hLookup]
  unfold cellsAt rightAt
  rcases hs : h₂.lookup a with _ | _
  · cases hr : b.right <;> simp [Option.merge, Cell.joinList_nil_right, DeallocRight.join, ← hr]
  · rfl

private theorem cell?_union_left {h₁ h₂ : Heap} {l : RawPtr T M} {c : Σ α : Type v, α}
    (hCell : h₁.cell? l = some c) : (h₁ ∪ h₂).cell? l = some c := by
  unfold cell? at hCell ⊢
  split at hCell
  · rename_i b hLookup
    rw [lookup_union_some hLookup]
    dsimp only
    split at hCell
    · rename_i x hx
      rw [Cell.getElem?_joinList_owned hx]
      exact hCell
    · simp at hCell
  · simp at hCell

theorem mem_singleton {α : Type v} {q : RawPtr α M} {value : α} {kind : AllocKind} {len : Nat}
    {a : AllocId} : a ∈ singleton q value kind len ↔ a = q.allocId :=
  Finmap.mem_singleton _ _ _

/-- The cell does not depend on the pointer's mutability. -/
theorem singleton_eq_of_addr {α : Type v} {q : RawPtr α M} {r : RawPtr α M'}
    (hId : q.allocId = r.allocId) (hOffset : q.offset = r.offset) (value : α) (kind : AllocKind)
    (len : Nat) : singleton q value kind len = singleton r value kind len := by
  unfold singleton
  rw [hId, hOffset]

private theorem lookup_singleton {α : Type v} (q : RawPtr α M) (value : α) (kind : AllocKind)
    (len : Nat) : (singleton q value kind len).lookup q.allocId =
      some ⟨kind, α, (List.replicate len .notOwned).set q.offset (.owned value), .none⟩ :=
  Finmap.lookup_singleton_eq

private theorem lookup_singleton_ne {α : Type v} {q : RawPtr α M} {value : α} {kind : AllocKind}
    {len : Nat} {a : AllocId} (hNe : a ≠ q.allocId) :
    (singleton q value kind len).lookup a = none :=
  lookup_eq_none.mpr fun hMem => hNe (mem_singleton.mp hMem)

@[simp]
theorem not_isValid_empty {α : Type v} (q : RawPtr α M) :
    ¬ IsValid (∅ : Heap) q := by
  simp [IsValid, cell?]

theorem notMem_freshAllocId {h : Heap} {a : AllocId}
    (hBase : a = freshAllocId h) : a ∉ h := by
  intro hMem
  have hLe : a ≤ h.allocs.keys.sup id := Finset.le_sup (f := id) (Finmap.mem_keys.mpr hMem)
  rw [hBase, freshAllocId] at hLe
  exact Nat.not_succ_le_self _ hLe

private theorem lookup_allocation {α : Type v} (a : AllocId) (values : List α) (kind : AllocKind) :
    (allocation a values kind).lookup a = some ⟨kind, α, values.map .owned, .freeable⟩ :=
  Finmap.lookup_singleton_eq

private theorem lookup_allocation_ne {α : Type v} {a b : AllocId} {values : List α}
    {kind : AllocKind} (hNe : b ≠ a) : (allocation a values kind).lookup b = none :=
  lookup_eq_none.mpr fun hMem => hNe ((Finmap.mem_singleton _ _ _).mp hMem)

/-- A fresh allocation sits next to the heap it was allocated in. -/
theorem allocBlock_eq {α : Type v} (h : Heap) (values : List α) (kind : AllocKind) :
    h.allocBlock values kind =
      (⟨freshAllocId h, 0⟩, allocation (freshAllocId h) values kind ∪ h) := by
  refine Prod.ext rfl (ext fun a => ?_)
  rw [lookup_union]
  by_cases ha : a = freshAllocId h
  · subst ha
    have hNone := lookup_eq_none.mpr (notMem_freshAllocId (h := h) rfl)
    simp only [allocBlock, lookup_insert, hNone, lookup_allocation]
    rfl
  · simp only [allocBlock, lookup_insert_ne _ _ ha, lookup_allocation_ne ha, Option.merge_none_left]

theorem compatible_freshAllocId {α : Type v} (h : Heap) (values : List α) (kind : AllocKind) :
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

private theorem lookup_of_cell? {h : Heap} {l : RawPtr T M} {c : Σ α : Type v, α}
    (hCell : h.cell? l = some c) :
    ∃ b : Block, h.lookup l.allocId = some b ∧
      ∃ x, b.cells[l.offset]? = some (.owned x) ∧ c = ⟨b.ty, x⟩ := by
  unfold cell? at hCell
  split at hCell
  · rename_i b hLookup
    split at hCell
    · rename_i x hx
      exact ⟨b, hLookup, x, hx, (Option.some.inj hCell).symm⟩
    · simp at hCell
  · simp at hCell

private theorem cell?_of_isValid {α : Type v} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : ∃ x : α, h.cell? q = some ⟨α, x⟩ := by
  unfold IsValid at hValid
  split at hValid
  · contradiction
  · rename_i β x hCell
    subst hValid
    exact ⟨x, hCell⟩

private theorem lookup_of_isValid {α : Type v} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) :
    ∃ b : Block, h.lookup q.allocId = some b ∧ b.ty = α ∧
      ∃ x, b.cells[q.offset]? = some (.owned x) := by
  obtain ⟨_, hCell⟩ := cell?_of_isValid hValid
  obtain ⟨b, hLookup, x, hx, hEq⟩ := lookup_of_cell? hCell
  exact ⟨b, hLookup, (congrArg Sigma.fst hEq).symm, x, hx⟩

theorem mem_of_isLive {h : Heap} {l : RawPtr T M} (hLive : IsLive h l) : l.allocId ∈ h := by
  obtain ⟨c, hCell⟩ := Option.isSome_iff_exists.mp hLive
  obtain ⟨b, hLookup, -⟩ := lookup_of_cell? hCell
  exact mem_iff_lookup.mpr (by simp [hLookup])

theorem isLive_of_isValid {α : Type v} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : IsLive h q := by
  obtain ⟨x, hCell⟩ := cell?_of_isValid hValid
  simp [IsLive, hCell]

theorem mem_of_isValid {α : Type v} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : q.allocId ∈ h :=
  mem_of_isLive (isLive_of_isValid hValid)

theorem not_compatible_of_isValid {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid₁ : IsValid h₁ q) (hValid₂ : IsValid h₂ q) :
    ¬ PartialCommMonoid.Compatible h₁ h₂ := by
  intro hCompatible
  obtain ⟨b₁, hLookup₁, -, x₁, hx₁⟩ := lookup_of_isValid hValid₁
  obtain ⟨b₂, hLookup₂, -, x₂, hx₂⟩ := lookup_of_isValid hValid₂
  have hBlock := hCompatible q.allocId
  simp only [hLookup₁, hLookup₂, OptCompatible] at hBlock
  obtain ⟨k₁, t, c₁, f₁⟩ := b₁
  obtain ⟨k₂, c₂, f₂', rfl⟩ := Block.eq_mk_of_compatible hBlock
  dsimp only at hBlock hx₂
  rw [Block.compatible_mk_iff] at hBlock
  have := (Cell.forall₂_iff_getElem?.mp hBlock.2.1).2 _ _ _ hx₁ hx₂
  simp [Cell.Compatible] at this

theorem isValid_union_left {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) : IsValid (h₁ ∪ h₂) q := by
  obtain ⟨x, hCell⟩ := cell?_of_isValid hValid
  simp [IsValid, cell?_union_left hCell]

theorem isLive_union_left {h₁ h₂ : Heap} {l : RawPtr T M}
    (hLive : IsLive h₁ l) : IsLive (h₁ ∪ h₂) l := by
  obtain ⟨c, hCell⟩ := Option.isSome_iff_exists.mp hLive
  simp [IsLive, cell?_union_left hCell]

/-- Framing: `read` on a bigger heap reads the same value and leaves the frame alone. -/
theorem read_union_left {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M}
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
      have hCells : (⟨β, value⟩ : Σ α : Type v, α) = ⟨β₁, value₁⟩ :=
        Option.some.inj (hCell.symm.trans (cell?_union_left hCell₁))
      cases hCells
      rfl

/-- `setOwned` on a heap whose block at `q` is `b`. -/
private theorem setOwned_of_lookup {α : Type v} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some b → b.ty = α} {b : Block}
    (hLookup : h.lookup q.allocId = some b) :
    h.setOwned q value hTy =
      h.insert q.allocId
        ⟨b.kind, b.ty, b.cells.set q.offset (.owned (cast (hTy b hLookup).symm value)),
          b.right⟩ := by
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
private theorem setOwned_union_left {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M} {value : α}
    {b : Block} (hLookup : h₁.lookup q.allocId = some b) (hTy : b.ty = α)
    (hTy₁ : ∀ b, h₁.lookup q.allocId = some b → b.ty = α)
    (hTyUnion : ∀ b, (h₁ ∪ h₂).lookup q.allocId = some b → b.ty = α) :
    (h₁ ∪ h₂).setOwned q value hTyUnion = h₁.setOwned q value hTy₁ ∪ h₂ := by
  rw [setOwned_of_lookup (lookup_union_some hLookup), setOwned_of_lookup hLookup]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    obtain ⟨k, t, c, f⟩ := b
    dsimp only at hTy ⊢
    subst hTy
    simp only [cast_eq]
    unfold cellsAt rightAt
    rcases hs : h₂.lookup q.allocId with _ | _
    · simp [Option.merge, Cell.joinList_nil_right]
    · simp [Option.merge, Block.join, Cell.joinList_set_owned]
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

theorem write_union_left {α : Type v} {h₁ h₂ : Heap}
    (q : RawPtr α M) (value : α) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).write q value (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.write q value hValid) := by
  obtain ⟨b, hLookup, hTy, -⟩ := lookup_of_isValid hValid
  exact congrArg (Prod.mk ()) (setOwned_union_left hLookup hTy _ _)

/-- After `setOwned` at `q`, the block of `q` owns the cell of `q` and keeps its header. -/
private theorem lookup_setOwned {α : Type v} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some b → b.ty = α} {b : Block}
    (hLookup : h.lookup q.allocId = some b) :
    ∃ x, (h.setOwned q value hTy).lookup q.allocId =
      some ⟨b.kind, b.ty, b.cells.set q.offset (.owned x), b.right⟩ :=
  ⟨_, by rw [setOwned_of_lookup hLookup, lookup_insert]⟩

private theorem lookup_setOwned_ne {α : Type v} {h : Heap} {q : RawPtr α M} {value : α}
    {hTy : ∀ b, h.lookup q.allocId = some b → b.ty = α} {a : AllocId}
    (ha : a ≠ q.allocId) : (h.setOwned q value hTy).lookup a = h.lookup a := by
  unfold setOwned
  split
  · exact lookup_insert_ne _ _ ha
  · rfl

/-- Owning a cell that `h₁` owns or borrows keeps compatibility: a compatible frame does not own or
borrow it. -/
private theorem compatible_setOwned_left {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M}
    {value : α} {hTy : ∀ b, h₁.lookup q.allocId = some b → b.ty = α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hExcl : ∀ b, h₁.lookup q.allocId = some b → b.cells[q.offset]? ≠ some .notOwned) :
    PartialCommMonoid.Compatible (h₁.setOwned q value hTy) h₂ := by
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    have hBlock := hCompatible q.allocId
    rcases hs₁ : h₁.lookup q.allocId with _ | b₁
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
      rcases hs₂ : h₂.lookup q.allocId with _ | b₂
      · trivial
      · rw [hs₂] at hBlock
        simp only [OptCompatible] at hBlock ⊢
        obtain ⟨k₁, t, c₁, r₁⟩ := b₁
        dsimp only at hExcl₁
        obtain ⟨k₂, c₂, r₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
        dsimp only at hBlock hs₂ ⊢
        rw [Block.compatible_mk_iff] at hBlock ⊢
        refine ⟨hBlock.1, Cell.forall₂_iff_getElem?.mpr ⟨by simp [hBlock.2.1.length_eq], ?_⟩,
          hBlock.2.2.1, hBlock.2.2.2.1,
          fun hFreed => Cell.forall_notOwned_set (hBlock.2.2.2.2 hFreed) hExcl₁⟩
        intro i y z hy hz
        rw [List.getElem?_set] at hy
        split at hy
        · rename_i hi
          subst hi
          have hi₁ : q.offset < c₁.length := by
            have := hBlock.2.1.length_eq; have := (List.getElem?_eq_some_iff.mp hz).1; omega
          rw [List.getElem?_eq_getElem hi₁] at hExcl₁
          have hz' := Cell.eq_notOwned_of_compatible
            ((Cell.forall₂_iff_getElem?.mp hBlock.2.1).2 _ _ _ (List.getElem?_eq_getElem hi₁) hz)
            (fun h => hExcl₁ (congrArg some h))
          subst hz'
          cases y <;> trivial
        · exact (Cell.forall₂_iff_getElem?.mp hBlock.2.1).2 i y z hy hz
  · show OptCompatible ((h₁.setOwned q value hTy).lookup a) _
    rw [lookup_setOwned_ne ha]
    exact hCompatible a

theorem compatible_write_left {α : Type v} {q : RawPtr α M} {value : α}
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
      q.offset = 0 ∧ ∃ b, h.lookup q.allocId = some b ∧ b.kind = kind ∧
        b.cells.length = n ∧ (∀ i < n, IsLive h (q.shift i)) ∧ b.right = .freeable := by
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
  obtain ⟨-, -, -, -, -, hLive, -⟩ := canDealloc_iff'.mp hDealloc
  exact hLive i hi

/-- The block `b` that `q` deallocates owns all its `n` cells and the right to deallocate it. -/
private theorem block_of_canDealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    {b : Block} (hDealloc : CanDealloc h q n kind) (hLookup : h.lookup q.allocId = some b) :
    b.cells.length = n ∧ (∀ (i : Nat) (x : Cell b.ty), b.cells[i]? = some x → x ≠ .notOwned) ∧
      b.right = .freeable := by
  obtain ⟨hOffset, b', hLookup', -, hLen, hLive, hFree⟩ := canDealloc_iff'.mp hDealloc
  rw [hLookup] at hLookup'
  cases hLookup'
  refine ⟨hLen, ?_, hFree⟩
  rintro i x hx rfl
  have := hLive i (hLen ▸ (List.getElem?_eq_some_iff.mp hx).1)
  simp [IsLive, cell?, hLookup, hOffset, hx] at this

private theorem freeBlock_snd_of_lookup {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    {b : Block} (hDealloc : CanDealloc h q n kind) (hLookup : h.lookup q.allocId = some b) :
    (h.freeBlock q n kind hDealloc).2 =
      h.insert q.allocId ⟨b.kind, b.ty, List.replicate n .notOwned, .freed⟩ := by
  simp only [freeBlock, hLookup]

/-- A fragment compatible with the block that `q` deallocates owns none of its cells and holds no
right on it. -/
private theorem lookup_of_compatible_canDealloc {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat}
    {kind : AllocKind} {b : Block} (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hDealloc : CanDealloc h₁ q n kind) (hLookup : h₁.lookup q.allocId = some b) :
    h₂.lookup q.allocId = none ∨
      h₂.lookup q.allocId = some ⟨b.kind, b.ty, List.replicate n .notOwned, .none⟩ := by
  obtain ⟨hLen, hOwned, hFree⟩ := block_of_canDealloc hDealloc hLookup
  have hBlock := hCompatible q.allocId
  rw [hLookup] at hBlock
  rcases hs : h₂.lookup q.allocId with _ | b₂
  · exact .inl rfl
  · rw [hs] at hBlock
    obtain ⟨k₂, c₂, r₂, rfl⟩ := Block.eq_mk_of_compatible hBlock
    obtain ⟨k, t, c, r⟩ := b
    dsimp only at hBlock hLen hOwned hFree ⊢
    subst hFree
    rw [OptCompatible, Block.compatible_mk_iff] at hBlock
    obtain ⟨hKind, hCells, hRight, -⟩ := hBlock
    have hc := Cell.eq_replicate_of_forall₂ hCells hOwned
    rw [← hCells.length_eq, hLen] at hc
    have hr : r₂ = .none := by simpa using hRight
    rw [hc, hr, hKind]
    exact .inr rfl

theorem canDealloc_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h₁ q n kind) : CanDealloc (h₁ ∪ h₂) q n kind := by
  obtain ⟨hOffset, b, hLookup, hKind, hLen, hLive, hFree⟩ := canDealloc_iff'.mp hDealloc
  exact canDealloc_iff'.mpr ⟨hOffset, _, lookup_union_some hLookup, hKind,
    by rw [Cell.length_joinList, hLen], fun i hi => isLive_union_left (hLive i hi),
    by simp [hFree, DeallocRight.join]⟩

theorem compatible_freeBlock_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat}
    {kind : AllocKind}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : CanDealloc h₁ q n kind) :
    PartialCommMonoid.Compatible (h₁.freeBlock q n kind hDealloc).2 h₂ := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  intro a
  show OptCompatible ((h₁.freeBlock q n kind hDealloc).2.lookup a) _
  rw [freeBlock_snd_of_lookup hDealloc hLookup]
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert]
    rcases lookup_of_compatible_canDealloc hCompatible hDealloc hLookup with hs | hs <;> rw [hs]
    · trivial
    · show Block.Compatible _ _
      rw [Block.compatible_mk_iff]
      exact ⟨rfl, Cell.forall₂_replicate_notOwned n, .inr rfl,
        fun _ _ hx => List.eq_of_mem_replicate hx, fun h => nomatch h⟩
  · rw [lookup_insert_ne _ _ ha]
    exact hCompatible a

theorem freeBlock_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : CanDealloc h₁ q n kind) :
    (h₁ ∪ h₂).freeBlock q n kind (canDealloc_union_left hDealloc) =
      Prod.map id (· ∪ h₂) (h₁.freeBlock q n kind hDealloc) := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  refine Prod.ext rfl (ext fun a => ?_)
  show ((h₁ ∪ h₂).freeBlock q n kind _).2.lookup a =
    ((h₁.freeBlock q n kind hDealloc).2 ∪ h₂).lookup a
  rw [freeBlock_snd_of_lookup _ (lookup_union_some hLookup),
    freeBlock_snd_of_lookup hDealloc hLookup]
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    rcases lookup_of_compatible_canDealloc hCompatible hDealloc hLookup with hs | hs <;> rw [hs]
    · rfl
    · simp [Option.merge, Block.join_mk, Cell.joinList_replicate_notOwned]
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

/-- Freed blocks stay in the heap, so their allocation id is never handed out again. -/
theorem mem_freeBlock {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) : q.allocId ∈ (h.freeBlock q n kind hDealloc).2 := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  rw [freeBlock_snd_of_lookup hDealloc hLookup]
  exact mem_iff_lookup.mpr (by simp [lookup_insert])

/-- No cell of a freed block can be read or written. -/
theorem not_isLive_freeBlock {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    {l : RawPtr T M'}
    (hDealloc : CanDealloc h q n kind) (hId : l.allocId = q.allocId) :
    ¬ IsLive (h.freeBlock q n kind hDealloc).2 l := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  rw [freeBlock_snd_of_lookup hDealloc hLookup]
  simp [IsLive, cell?, hId, lookup_insert, List.getElem?_replicate]

/-- A freed block cannot be freed again. -/
theorem not_canDealloc_freeBlock {h : Heap} {q : RawPtr α M} {r : RawPtr β M'} {n n' : Nat}
    {kind kind' : AllocKind} (hDealloc : CanDealloc h q n kind)
    (hId : r.allocId = q.allocId) :
    ¬ CanDealloc (h.freeBlock q n kind hDealloc).2 r n' kind' := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  rw [canDealloc_iff', freeBlock_snd_of_lookup hDealloc hLookup]
  rintro ⟨-, b', hLookup', -, -, -, hFree⟩
  rw [hId, lookup_insert] at hLookup'
  cases hLookup'
  cases hFree

/-- A cell of a freed block cannot be borrowed back to life. -/
theorem not_isBorrowed_freeBlock {h : Heap} {q : RawPtr α M} {r : RawPtr β M'} {n : Nat}
    {kind : AllocKind} (hDealloc : CanDealloc h q n kind)
    (hId : r.allocId = q.allocId) :
    ¬ IsBorrowed (h.freeBlock q n kind hDealloc).2 r := by
  obtain ⟨-, b, hLookup, -⟩ := canDealloc_iff'.mp hDealloc
  rw [freeBlock_snd_of_lookup hDealloc hLookup]
  simp [IsBorrowed, hId, lookup_insert, List.getElem?_replicate]

/-! ### Allocation -/

private theorem lookup_allocBlock {α : Type v} (h : Heap) (values : List α) (kind : AllocKind) :
    (h.allocBlock values kind).2.lookup (freshAllocId h) =
      some ⟨kind, α, values.map .owned, .freeable⟩ :=
  lookup_insert _ _ _

/-- Allocation leaves the blocks already in the heap untouched. -/
theorem isLive_allocBlock_of_mem {β : Type v} {h : Heap} {values : List β}
    {kind : AllocKind} {l : RawPtr T M} (hMem : l.allocId ∈ h) :
    IsLive (h.allocBlock values kind).2 l ↔ IsLive h l := by
  have hNe : l.allocId ≠ freshAllocId h := fun hEq => notMem_freshAllocId hEq hMem
  simp only [IsLive, cell?, allocBlock, lookup_insert_ne _ _ hNe]

/-- Even an empty allocation reserves its id. -/
theorem mem_allocBlock {α : Type v} {kind : AllocKind} (h : Heap) (values : List α) :
    freshAllocId h ∈ (h.allocBlock values kind).2 :=
  mem_iff_lookup.mpr (by simp [lookup_allocBlock])

/-- The values of a fresh allocation are live, whatever the type of the pointer. -/
theorem isLive_allocBlock {α : Type v} {h : Heap} {values : List α} {kind : AllocKind}
    {i : Nat}
    (hIndex : i < values.length) :
    IsLive (h.allocBlock values kind).2 (⟨freshAllocId h, i⟩ : RawPtr T M) := by
  simp [IsLive, cell?, lookup_allocBlock, hIndex]

/-- A fresh allocation has no cell past its values. -/
theorem not_isLive_allocBlock_of_le {α : Type v} {h : Heap} {values : List α}
    {kind : AllocKind}
    {i : Nat} (hIndex : values.length ≤ i) :
    ¬ IsLive (h.allocBlock values kind).2 (⟨freshAllocId h, i⟩ : RawPtr T M) := by
  simp [IsLive, cell?, lookup_allocBlock, List.getElem?_eq_none hIndex]

/-- A fresh allocation can be freed whole, and only for its kind. -/
theorem canDealloc_allocBlock_iff {α : Type v} {β : Type u} (h : Heap) (values : List α)
    (n : Nat)
    (kind kind' : AllocKind) :
    CanDealloc (h.allocBlock values kind).2 (⟨freshAllocId h, 0⟩ : MutRawPtr β) n kind' ↔
      kind = kind' ∧ values.length = n := by
  rw [canDealloc_iff']
  constructor
  · rintro ⟨-, b, hLookup, hKind, hLen, -⟩
    rw [lookup_allocBlock] at hLookup
    cases hLookup
    exact ⟨hKind, by simpa using hLen⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, _, by rw [lookup_allocBlock], rfl, by simp,
      fun i hi => by simpa [RawPtr.shift] using isLive_allocBlock hi, rfl⟩

/-! ### Singletons -/

/-- Singletons of different blocks are always compatible. -/
theorem compatible_singleton_of_allocId_ne {α β : Type v} {q : RawPtr α M} {r : RawPtr β M'}
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
theorem compatible_singleton {α : Type v} {q : RawPtr α M} {r : RawPtr α M'} {value₁ value₂ : α}
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
    simp only [OptCompatible]
    rw [Block.compatible_mk_iff]
    refine ⟨rfl, Cell.forall₂_iff_getElem?.mpr ⟨by simp, fun i x y hx hy => ?_⟩, .inl rfl,
      nofun, nofun⟩
    simp only [List.getElem?_set, List.length_replicate, List.getElem?_replicate] at hx hy
    split at hx <;> split at hy <;> simp_all
    all_goals (try obtain ⟨-, rfl⟩ := hx); all_goals (try obtain ⟨-, rfl⟩ := hy)
    all_goals trivial
  · show OptCompatible _ _
    rw [lookup_singleton_ne ha]
    trivial

theorem isValid_singleton {α : Type v} (q : RawPtr α M) (value : α) (kind : AllocKind) {len : Nat}
    (hOffset : q.offset < len) : IsValid (singleton q value kind len) q := by
  simp [IsValid, cell?, lookup_singleton, hOffset]

theorem read_singleton {α : Type v} (q : RawPtr α M) (value : α) (kind : AllocKind) (len : Nat)
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

theorem write_singleton {α : Type v} (q : RawPtr α M) (oldValue newValue : α) (kind : AllocKind)
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

theorem Subheap.isValid {α : Type v} {A h : Heap} {q : RawPtr α M} (hSub : Heap.Subheap A h)
    (hValid : IsValid A q) : IsValid h q := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isValid_union_left hValid

theorem Subheap.isLive {A h : Heap} {l : RawPtr T M} (hSub : Heap.Subheap A h)
    (hLive : IsLive A l) : IsLive h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isLive_union_left hLive

theorem read_of_subheap {α : Type v} {q : RawPtr α M} {value : α} {kind : AllocKind} {len : Nat}
    {h : Heap} (hSub : Heap.Subheap (singleton q value kind len) h)
    (hOffset : q.offset < len) (hValid : IsValid h q) : (h.read q hValid).1 = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hValidSingleton := isValid_singleton q value kind hOffset
  rw [show hValid = isValid_union_left hValidSingleton from
      Subsingleton.elim _ _,
    read_union_left hValidSingleton, read_singleton]
  rfl

/-- The block of a fresh allocation is the union of one singleton per value. -/
theorem Subheap.singleton_allocation {α : Type v} (a : AllocId) (values : List α)
    (kind : AllocKind) {i : Nat} (hIndex : i < values.length) :
    Heap.Subheap (singleton (⟨a, i⟩ : MutRawPtr α) values[i] kind values.length)
      (allocation a values kind) := by
  let rest : Heap := ⟨Finmap.singleton a
    ⟨kind, α, (values.map Cell.owned).set i .notOwned, .freeable⟩⟩
  have hRest : ∀ b, rest.lookup b = if b = a then
      some ⟨kind, α, (values.map Cell.owned).set i .notOwned, .freeable⟩ else none := by
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
      exact (Block.compatible_mk_iff _ _ _ _ _ _ _).mpr
        ⟨rfl, hCells, .inl rfl, nofun, nofun⟩
    · show OptCompatible ((singleton _ _ _ _).lookup _) _
      rw [lookup_singleton_ne hb]
      trivial
  · rw [lookup_union]
    by_cases hb : b = a
    · subst hb
      rw [lookup_singleton, hRest, ite_eq_left rfl]
      rw [lookup_allocation]
      dsimp only
      simp only [Option.merge, Block.join_mk, Cell.joinList_of_forall₂ hCells]
      congr 2
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_zipWith, List.getElem?_set, List.length_replicate,
        List.getElem?_replicate, List.length_map, List.getElem?_map]
      by_cases hj : j < values.length <;> by_cases hij : i = j <;>
        simp_all [Cell.join]
    · rw [lookup_singleton_ne hb, hRest, ite_eq_right hb]
      exact lookup_allocation_ne hb

/-- `read` leaves the heap alone. -/
theorem read_snd {α : Type v} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    (h.read q hValid).2 = h := by
  unfold Heap.read
  split
  · rename_i hLookup
    simp [IsValid, hLookup] at hValid
  · rfl

/-- `borrow` returns the value that `read` returns. -/
theorem borrow_fst {α : Type v} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    (h.borrow q hValid).1 = (h.read q hValid).1 := by
  unfold Heap.borrow; rfl

/-! ### Borrows -/

/-- `borrow` on a heap whose block at `q` is `b`. -/
private theorem borrow_snd_of_lookup {α : Type v} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) {b : Block} (hLookup : h.lookup q.allocId = some b) :
    (h.borrow q hValid).2 =
      h.insert q.allocId ⟨b.kind, b.ty, b.cells.set q.offset .borrowed, b.right⟩ := by
  simp only [borrow, hLookup]

theorem borrow_union_left {α : Type v} {h₁ h₂ : Heap} (q : RawPtr α M)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).borrow q (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.borrow q hValid) := by
  obtain ⟨b, hLookup, hTy, x, hx⟩ := lookup_of_isValid hValid
  refine Prod.ext (congrArg Prod.fst (read_union_left (h₂ := h₂) hValid) :) ?_
  dsimp only [Prod.map]
  rw [borrow_snd_of_lookup _ (lookup_union_some hLookup), borrow_snd_of_lookup _ hLookup]
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_insert, lookup_union, lookup_insert]
    have hBlock := hCompatible q.allocId
    rw [hLookup] at hBlock
    unfold cellsAt rightAt
    rcases hs : h₂.lookup q.allocId with _ | b₂
    · simp [Option.merge, Cell.joinList_nil_right]
    · rw [hs] at hBlock
      simp only [OptCompatible] at hBlock
      obtain ⟨k, t, c, f⟩ := b
      obtain ⟨k₂, c₂, f₂', rfl⟩ := Block.eq_mk_of_compatible hBlock
      dsimp only at hBlock hx ⊢
      rw [Block.compatible_mk_iff] at hBlock
      simp only [Option.merge, Block.join_mk, Block.cellsAs_mk]
      rw [Cell.joinList_set_borrowed]
  · rw [lookup_insert_ne _ _ ha, lookup_union, lookup_union, lookup_insert_ne _ _ ha]

theorem compatible_borrow_left {α : Type v} {q : RawPtr α M} {h₁ h₂ : Heap}
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
    rcases hs : h₂.lookup q.allocId with _ | b₂
    · trivial
    · rw [hs] at hBlock
      simp only [OptCompatible] at hBlock ⊢
      obtain ⟨k, t, c, f⟩ := b
      obtain ⟨k₂, c₂, f₂', rfl⟩ := Block.eq_mk_of_compatible hBlock
      dsimp only at hBlock hx ⊢
      rw [Block.compatible_mk_iff] at hBlock ⊢
      refine ⟨hBlock.1, Cell.forall₂_iff_getElem?.mpr ⟨by simp [hBlock.2.1.length_eq], ?_⟩,
        hBlock.2.2.1, hBlock.2.2.2.1,
        fun hFreed => Cell.forall_notOwned_set (hBlock.2.2.2.2 hFreed) (by simp [hx])⟩
      intro i y z hy hz
      rw [List.getElem?_set] at hy
      split at hy
      · rename_i hi
        subst hi
        simp at hy; obtain ⟨-, rfl⟩ := hy
        rw [Cell.eq_notOwned_of_compatible ((Cell.forall₂_iff_getElem?.mp hBlock.2.1).2 _ _ _ hx hz)
          (by simp)]
        trivial
      · exact (Cell.forall₂_iff_getElem?.mp hBlock.2.1).2 i y z hy hz
  · show OptCompatible ((h₁.insert _ _).lookup a) _
    rw [lookup_insert_ne _ _ ha]
    exact hCompatible a

/-- A borrowed cell holds no value: no access goes through it until `endBorrow`. -/
theorem not_isLive_borrow {α : Type v} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    ¬ IsLive (h.borrow q hValid).2 q := by
  obtain ⟨b, hLookup, -⟩ := lookup_of_isValid hValid
  rw [borrow_snd_of_lookup hValid hLookup]
  simp only [IsLive, cell?, lookup_insert, List.getElem?_set]
  split <;> simp_all

/-- A borrowed cell can be given back. -/
theorem isBorrowed_borrow {α : Type v} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    IsBorrowed (h.borrow q hValid).2 q := by
  obtain ⟨b, hLookup, hTy, x, hx⟩ := lookup_of_isValid hValid
  rw [borrow_snd_of_lookup hValid hLookup]
  have hi : q.offset < b.cells.length := (List.getElem?_eq_some_iff.mp hx).1
  simp [IsBorrowed, lookup_insert, hTy, hi]

private theorem lookup_borrowedBlock {α : Type v} (q : RawPtr α M) (kind : AllocKind) (len : Nat) :
    (borrowedBlock q kind len).lookup q.allocId =
      some ⟨kind, α, (List.replicate len .notOwned).set q.offset .borrowed, .none⟩ :=
  Finmap.lookup_singleton_eq

private theorem lookup_header {α : Type v} (q : RawPtr α M) (kind : AllocKind) (len : Nat) :
    (header q kind len).lookup q.allocId =
      some ⟨kind, α, List.replicate len .notOwned, .freeable⟩ :=
  Finmap.lookup_singleton_eq

theorem borrow_singleton {α : Type v} (q : RawPtr α M) (value : α) (kind : AllocKind) (len : Nat)
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

theorem isBorrowed_borrowedBlock {α : Type v} (q : RawPtr α M) (kind : AllocKind) {len : Nat}
    (hOffset : q.offset < len) : IsBorrowed (borrowedBlock q kind len) q := by
  unfold IsBorrowed
  rw [lookup_borrowedBlock]
  simp [hOffset]

/-- The borrow of a cell wins over any other fragment of it. -/
theorem isBorrowed_union_left {α : Type v} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hBorrowed : IsBorrowed h₁ q) : IsBorrowed (h₁ ∪ h₂) q := by
  unfold IsBorrowed at hBorrowed ⊢
  split at hBorrowed
  · rename_i b hLookup
    rw [lookup_union_some hLookup]
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
theorem endBorrow_union_left {α : Type v} {h₁ h₂ : Heap} (q : RawPtr α M) (value : α)
    (hBorrowed : IsBorrowed h₁ q) :
    (h₁ ∪ h₂).endBorrow q value (isBorrowed_union_left hBorrowed) =
      Prod.map id (· ∪ h₂) (h₁.endBorrow q value hBorrowed) := by
  unfold IsBorrowed at hBorrowed
  split at hBorrowed
  · rename_i b hLookup
    exact congrArg (Prod.mk ()) (setOwned_union_left hLookup hBorrowed.1 _ _)
  · exact hBorrowed.elim

theorem compatible_endBorrow_left {α : Type v} {q : RawPtr α M} {value : α} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hBorrowed : IsBorrowed h₁ q) :
    PartialCommMonoid.Compatible (h₁.endBorrow q value hBorrowed).2 h₂ :=
  compatible_setOwned_left (hTy := ty_of_isBorrowed hBorrowed) hCompatible fun b hLookup => by
    unfold IsBorrowed at hBorrowed
    rw [hLookup] at hBorrowed
    simp [hBorrowed.2]

theorem endBorrow_borrowedBlock {α : Type v} (q : RawPtr α M) (value : α) (kind : AllocKind)
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

/-! ### Separation logic support -/

@[simp] theorem notMem_empty (a : AllocId) : a ∉ (∅ : Heap) :=
  Finmap.notMem_empty

theorem mem_header {α : Type v} {q : RawPtr α M} {kind : AllocKind} {len : Nat}
    {a : AllocId} : a ∈ header q kind len ↔ a = q.allocId :=
  Finmap.mem_singleton _ _ _

/-- The header of a block does not depend on the offset of the pointer. -/
theorem header_eq_of_allocId {α : Type v} {q : RawPtr α M} {r : RawPtr α M'}
    (hId : q.allocId = r.allocId) (kind : AllocKind) (len : Nat) :
    header q kind len = header r kind len := by
  unfold header
  rw [hId]

@[simp] theorem header_shift {α : Type v} (q : RawPtr α M) (i : Nat) (kind : AllocKind)
    (len : Nat) : header (q.shift i) kind len = header q kind len :=
  header_eq_of_allocId (RawPtr.allocId_shift q i) kind len

/-- A fragment with the header of the block of `q` that owns all its cells can
deallocate it. -/
theorem canDealloc_of_subheap {α : Type v} {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hOffset : q.offset = 0) (hSub : Heap.Subheap (header q kind n) h)
    (hLive : ∀ i < n, IsLive h (q.shift i)) : CanDealloc h q n kind := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact canDealloc_iff'.mpr ⟨hOffset, _, lookup_union_some (lookup_header q kind n), rfl,
    by simp only [Cell.length_joinList, List.length_replicate], hLive,
    by simp [DeallocRight.join]⟩

/-- The cells of `range`: `values` from `offset` on, in a block of `len` cells. -/
private def rangeCells {α : Type v} (offset : Nat) (values : List α) (len : Nat) : List (Cell α) :=
  (List.range len).map fun i =>
    if offset ≤ i then (values[i - offset]?.map .owned).getD .notOwned else .notOwned

private theorem getElem?_rangeCells {α : Type v} (offset : Nat) (values : List α) (len i : Nat) :
    (rangeCells offset values len)[i]? =
      if i < len then
        some (if offset ≤ i then (values[i - offset]?.map .owned).getD .notOwned else .notOwned)
      else none := by
  simp only [rangeCells, List.getElem?_map]
  by_cases hi : i < len
  · rw [ite_eq_left hi, List.getElem?_range hi]
    rfl
  · rw [ite_eq_right hi, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The block of `q`, of kind `kind` and `len` cells, owning `values` from `q` on (those that fit in
the block), and the right to deallocate it. -/
def range {α : Type v} (q : RawPtr α M) (values : List α) (kind : AllocKind) (len : Nat) : Heap :=
  ⟨Finmap.singleton q.allocId ⟨kind, α, rangeCells q.offset values len, .freeable⟩⟩

private theorem lookup_range {α : Type v} (q : RawPtr α M) (values : List α) (kind : AllocKind)
    (len : Nat) :
    (range q values kind len).lookup q.allocId =
      some ⟨kind, α, rangeCells q.offset values len, .freeable⟩ :=
  Finmap.lookup_singleton_eq

private theorem lookup_range_ne {α : Type v} {q : RawPtr α M} {values : List α} {kind : AllocKind}
    {len : Nat} {a : AllocId} (hNe : a ≠ q.allocId) : (range q values kind len).lookup a = none :=
  lookup_eq_none.mpr fun hMem => hNe ((Finmap.mem_singleton _ _ _).mp hMem)

/-- Owning no value leaves the header of the block. -/
theorem range_nil {α : Type v} (q : RawPtr α M) (kind : AllocKind) (len : Nat) :
    range q ([] : List α) kind len = header q kind len := by
  apply ext
  intro a
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_range, lookup_header]
    congr 2
    apply List.ext_getElem?
    intro i
    rw [getElem?_rangeCells, List.getElem?_replicate]
    simp
  · rw [lookup_range_ne ha]
    exact (lookup_eq_none.mpr fun hMem => ha ((Finmap.mem_singleton _ _ _).mp hMem)).symm

/-- A fresh allocation owns all its values. -/
theorem allocation_eq_range {α : Type v} (a : AllocId) (values : List α) (kind : AllocKind) :
    allocation a values kind = range (⟨a, 0⟩ : MutRawPtr α) values kind values.length := by
  apply ext
  intro b
  by_cases hb : b = a
  · subst hb
    rw [lookup_allocation, lookup_range (⟨b, 0⟩ : MutRawPtr α)]
    congr 2
    apply List.ext_getElem?
    intro i
    rw [getElem?_rangeCells, List.getElem?_map]
    by_cases hi : i < values.length
    · simp [hi]
    · simp [hi]
  · rw [lookup_allocation_ne hb, lookup_range_ne hb]

private theorem lookup_range_shift {α : Type v} (q : RawPtr α M) (values : List α)
    (kind : AllocKind) (len : Nat) :
    (range (q.shift 1) values kind len).lookup q.allocId =
      some ⟨kind, α, rangeCells (q.offset + 1) values len, .freeable⟩ :=
  lookup_range (q.shift 1) values kind len

private theorem forall₂_singleton_range {α : Type v} (q : RawPtr α M) (value : α) (values : List α)
    (len : Nat) :
    List.Forall₂ Cell.Compatible ((List.replicate len .notOwned).set q.offset (.owned value))
      (rangeCells (q.offset + 1) values len) := by
  refine Cell.forall₂_iff_getElem?.mpr ⟨by simp [rangeCells], fun i x y hx hy => ?_⟩
  rw [getElem?_rangeCells] at hy
  simp only [List.getElem?_set, List.length_replicate, List.getElem?_replicate] at hx
  by_cases hi : q.offset = i
  · subst hi
    have hy' : y = .notOwned := by
      split at hy
      · simp only [Option.some.injEq] at hy
        rw [ite_eq_right (by omega)] at hy
        exact hy.symm
      · cases hy
    subst hy'
    cases x <;> trivial
  · have hx' : x = .notOwned := by
      rw [ite_eq_right hi] at hx
      split at hx
      · exact (Option.some.inj hx).symm
      · cases hx
    subst hx'
    trivial

theorem compatible_singleton_range {α : Type v} (q : RawPtr α M) (value : α) (values : List α)
    (kind : AllocKind) (len : Nat) :
    PartialCommMonoid.Compatible (singleton q value kind len) (range (q.shift 1) values kind len) := by
  intro a
  show OptCompatible _ _
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_singleton, lookup_range_shift]
    exact (Block.compatible_mk_iff _ _ _ _ _ _ _).mpr
      ⟨rfl, forall₂_singleton_range q value values len, .inl rfl, nofun, nofun⟩
  · rw [lookup_singleton_ne ha]
    trivial

/-- A range is its first cell and the range after it. -/
theorem singleton_union_range {α : Type v} (q : RawPtr α M) (value : α) (values : List α)
    (kind : AllocKind) (len : Nat) :
    singleton q value kind len ∪ range (q.shift 1) values kind len =
      range q (value :: values) kind len := by
  apply ext
  intro a
  rw [lookup_union]
  by_cases ha : a = q.allocId
  · subst ha
    rw [lookup_singleton, lookup_range_shift, lookup_range]
    simp only [Option.merge, Block.join_mk,
      Cell.joinList_of_forall₂ (forall₂_singleton_range q value values len)]
    congr 2
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_zipWith, getElem?_rangeCells, getElem?_rangeCells, List.getElem?_set,
      List.length_replicate, List.getElem?_replicate]
    by_cases hi : i < len
    · by_cases hOffset : q.offset = i
      · subst hOffset
        simp [hi, Cell.join]
      · by_cases hLe : q.offset ≤ i
        · have hSub : i - q.offset = (i - (q.offset + 1)) + 1 := by omega
          simp [hi, hOffset, hLe, Cell.join, hSub, show q.offset + 1 ≤ i by omega]
        · simp [hi, hOffset, hLe, Cell.join, show ¬ q.offset + 1 ≤ i by omega]
    · simp [hi]
  · rw [lookup_singleton_ne ha, lookup_range_ne (q := q.shift 1) ha, lookup_range_ne (q := q) ha]
    rfl

private theorem cells_eq_of_joinList_eq {α : Type v} {c₁ c₂ c : List (Cell α)}
    (h₁ : List.Forall₂ Cell.Compatible c₁ c) (h₂ : List.Forall₂ Cell.Compatible c₂ c)
    (hEq : Cell.joinList c₁ c = Cell.joinList c₂ c) : c₁ = c₂ := by
  rw [Cell.joinList_of_forall₂ h₁, Cell.joinList_of_forall₂ h₂] at hEq
  induction h₁ generalizing c₂ with
  | nil => cases h₂; rfl
  | @cons x y l₁ l hxy _ ih =>
    cases h₂ with
    | @cons x' _ l₂ _ hxy' h₂' =>
      simp only [List.zipWith_cons_cons, List.cons.injEq] at hEq
      rw [ih h₂' hEq.2]
      congr 1
      have hHead := hEq.1
      cases x <;> cases x' <;> cases y <;> simp_all [Cell.join, Cell.Compatible]

/-- Two blocks that combine with `f` into the same block are equal, unless one of them is absent. -/
private theorem block_eq_of_merge_eq {s₁ s₂ f : Option Block}
    (h₁ : OptCompatible s₁ f) (h₂ : OptCompatible s₂ f)
    (hEq : Option.merge Block.join s₁ f = Option.merge Block.join s₂ f) :
    s₁ = none ∨ s₂ = none ∨ s₁ = s₂ := by
  rcases s₁ with _ | b₁
  · exact .inl rfl
  rcases s₂ with _ | b₂
  · exact .inr (.inl rfl)
  refine .inr (.inr ?_)
  rcases f with _ | bf
  · simpa [Option.merge] using hEq
  simp only [Option.merge, Option.some.injEq] at hEq
  simp only [OptCompatible] at h₁ h₂
  obtain ⟨k₁, t, c₁, r₁⟩ := b₁
  obtain ⟨kf, cf, rf, rfl⟩ := Block.eq_mk_of_compatible h₁
  obtain ⟨k₂, c₂, r₂, rfl⟩ := Block.eq_mk_of_compatible (Block.compatible_symm h₂)
  dsimp only at h₁ h₂ hEq ⊢
  rw [Block.compatible_mk_iff] at h₁ h₂
  simp only [Block.join_mk, Block.mk.injEq, heq_eq_eq, true_and] at hEq
  have hr : r₁ = r₂ := by
    have := hEq.2.2; have := h₁.2.2.1; have := h₂.2.2.1
    cases r₁ <;> cases r₂ <;> cases rf <;> simp_all [DeallocRight.join]
  rw [hEq.1, cells_eq_of_joinList_eq h₁.2.1 h₂.2.1 hEq.2.1, hr]

private theorem merge_join_self (s : Option Block) : Option.merge Block.join s s = s := by
  rcases s with _ | ⟨k, t, c, r⟩
  · rfl
  · have hCells : Cell.joinList c c = c := by
      rw [Cell.joinList, ite_eq_left rfl]
      induction c with
      | nil => rfl
      | cons x c ih => rw [List.zipWith_cons_cons, ih]; cases x <;> rfl
    cases r <;> simp [Option.merge, Block.join_mk, hCells, DeallocRight.join]

/-- The blocks of `h₂` that are not in `h₁`. -/
private noncomputable def without (h₂ h₁ : Heap) : Heap :=
  ⟨h₁.allocs.keys.toList.foldr (fun a m => Finmap.erase a m) h₂.allocs⟩

private theorem lookup_foldr_erase (m : Finmap fun _ : AllocId => Block) (a : AllocId) :
    ∀ l : List AllocId,
      (l.foldr (fun b m => Finmap.erase b m) m).lookup a = if a ∈ l then none else m.lookup a
  | [] => by simp
  | b :: l => by
    rw [List.foldr_cons]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Finmap.lookup_erase_ne hab, lookup_foldr_erase m a l]
      simp [hab]

private theorem lookup_without_of_mem {h₁ h₂ : Heap} {a : AllocId} (ha : a ∈ h₁) :
    (without h₂ h₁).lookup a = none := by
  show Finmap.lookup a (h₁.allocs.keys.toList.foldr (fun b m => Finmap.erase b m) h₂.allocs) = _
  rw [lookup_foldr_erase, ite_eq_left (Finset.mem_toList.mpr (Finmap.mem_keys.mpr ha))]

private theorem lookup_without_of_not_mem {h₁ h₂ : Heap} {a : AllocId} (ha : a ∉ h₁) :
    (without h₂ h₁).lookup a = h₂.lookup a := by
  show Finmap.lookup a (h₁.allocs.keys.toList.foldr (fun b m => Finmap.erase b m) h₂.allocs) = _
  rw [lookup_foldr_erase,
    ite_eq_right fun hMem => ha (Finmap.mem_keys.mp (Finset.mem_toList.mp hMem))]
  rfl

private theorem subheap_union_of_slots {g₁ g₂ : Heap}
    (hSlot : ∀ a, g₁.lookup a = none ∨ g₂.lookup a = none ∨ g₁.lookup a = g₂.lookup a) :
    Heap.Subheap g₁ (g₁ ∪ g₂) := by
  refine ⟨without g₂ g₁, fun a => ?_, ext fun a => ?_⟩
  · show OptCompatible _ _
    by_cases ha : a ∈ g₁
    · rw [lookup_without_of_mem ha]
      cases g₁.lookup a <;> trivial
    · rw [lookup_eq_none.mpr ha]
      trivial
  · rw [lookup_union, lookup_union]
    by_cases ha : a ∈ g₁
    · rw [lookup_without_of_mem ha, Option.merge_none_right]
      rcases hSlot a with h | h | h
      · exact absurd ha (lookup_eq_none.mp h)
      · rw [h, Option.merge_none_right]
      · rw [← h, merge_join_self]
    · rw [lookup_without_of_not_mem ha]

/-- `∪` does not cancel: two fragments that combine with `frame` into the same heap may differ by
blocks of which they own no cell. Both are below a fragment that combines with `frame` into the
same heap. -/
theorem exists_subheap_of_union_eq {h₁ h₂ frame : Heap}
    (hCompatible₁ : PartialCommMonoid.Compatible h₁ frame)
    (hCompatible₂ : PartialCommMonoid.Compatible h₂ frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) :
    ∃ h, PartialCommMonoid.Compatible h frame ∧ h ∪ frame = h₁ ∪ frame ∧
      Heap.Subheap h₁ h ∧ Heap.Subheap h₂ h := by
  have hLookup a : Option.merge Block.join (h₁.lookup a) (frame.lookup a) =
      Option.merge Block.join (h₂.lookup a) (frame.lookup a) := by
    rw [← lookup_union, ← lookup_union, hEq]
  have hSlot a : h₁.lookup a = none ∨ h₂.lookup a = none ∨ h₁.lookup a = h₂.lookup a :=
    block_eq_of_merge_eq (hCompatible₁ a) (hCompatible₂ a) (hLookup a)
  have hSlot' a : h₂.lookup a = none ∨ h₁.lookup a = none ∨ h₂.lookup a = h₁.lookup a := by
    rcases hSlot a with h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h.symm)
  have hComm : h₁ ∪ h₂ = h₂ ∪ h₁ := ext fun a => by
    rw [lookup_union, lookup_union]
    rcases hSlot a with h | h | h
    · rw [h, Option.merge_none_left, Option.merge_none_right]
    · rw [h, Option.merge_none_left, Option.merge_none_right]
    · rw [h]
  refine ⟨h₁ ∪ h₂, fun a => ?_, ext fun a => ?_, subheap_union_of_slots hSlot,
    hComm ▸ subheap_union_of_slots hSlot'⟩
  · show OptCompatible ((h₁ ∪ h₂).lookup a) _
    rw [lookup_union]
    rcases hSlot a with h | h | h
    · rw [h, Option.merge_none_left]
      exact hCompatible₂ a
    · rw [h, Option.merge_none_right]
      exact hCompatible₁ a
    · rw [h, merge_join_self]
      exact hCompatible₂ a
  · rw [lookup_union, lookup_union, lookup_union]
    rcases hSlot a with h | h | h
    · rw [h, Option.merge_none_left, ← hLookup, h]
    · rw [h, Option.merge_none_right]
    · rw [h, merge_join_self]

end Heap

end Aeneas.Std
