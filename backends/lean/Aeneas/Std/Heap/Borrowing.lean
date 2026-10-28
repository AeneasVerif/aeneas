module

public import Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Borrow restoration is a privileged operation of matching translated backward
computations, not a Rust-callable raw-pointer operation. These triples account for its
heap resources; they do not prove that arbitrary Lean callers possess a lifetime token. -/

@[expose] public section

namespace Aeneas.Std

universe u

@[simp] theorem Cell.full_inj {xs ys : List ty} :
    Cell.full xs = Cell.full ys ↔ xs = ys :=
  List.map_inj_right fun _ _ h => (Cell.val.inj h).2

@[simp] theorem Cell.borrowed_inj {xs ys : List ty} :
    Cell.borrowed xs = Cell.borrowed ys ↔ xs = ys :=
  List.map_inj_right fun _ _ h => (Cell.val.inj h).2

theorem Cell.shared_values_eq {xs ys : List ty} {f g : Nat}
    (h : Cell.shared f xs = Cell.shared g ys) : xs = ys := by
  induction xs generalizing ys
  · have hy : ys = [] := by simpa [Cell.shared] using h.symm
    exact hy.symm
  · rename_i x xs ih
    cases ys
    · simp [Cell.shared] at h
    · rename_i y ys
      have hh := List.cons.inj h
      rw [(Cell.val.inj hh.1).2, ih hh.2]

theorem Cell.shared_succ_eq {xs ys : List ty} {f g : Nat}
    (h : Cell.shared f xs = Cell.shared g ys) :
    Cell.shared (f + 1) xs = Cell.shared (g + 1) ys := by
  have hv := Cell.shared_values_eq h
  subst ys
  cases xs
  · rfl
  · have hf := Option.some.inj (Cell.val.inj (List.cons.inj h).1).1
    subst g
    rfl

theorem Cell.shared_pred_eq {xs : List ty} {f g : Nat}
    (h : Cell.shared (f + 1) xs = Cell.shared (g + 1) xs) :
    Cell.shared f xs = Cell.shared g xs := by
  cases xs
  · rfl
  · have hf := Nat.add_right_cancel (Option.some.inj (Cell.val.inj (List.cons.inj h).1).1)
    subst g
    rfl

namespace SepLogic

variable {m : Layout.{u}}

theorem borrowRange.spec (p : RawPtr ty) (values : List ty) :
    Triple m (block p (Cell.full values)) (Heap.borrowRange m p values.length)
      (fun result h => result = values ∧ block p (Cell.borrowed values) h) := by
  apply triple_replaceRange (old := Cell.full values) (new := Cell.borrowed values)
  · intro s hm
    have hl : (Cell.full values).length = (Cell.borrowed values).length := by
      simp [Cell.full, Cell.borrowed]
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨values, s', rfl, hu⟩
  · rintro s result s' hm ⟨hlen, hu⟩
    have hl : (Cell.full values).length = (Cell.full result).length := by
      simp [Cell.full, hlen]
    have he := Cell.full_inj.mp (replaceRange.old_eq hm hl hu)
    subst result
    exact ⟨rfl, hu⟩

theorem endBorrowRange.spec (p : RawPtr ty) (original values : List ty)
    (hlen : original.length = values.length) :
    Triple m (block p (Cell.borrowed original)) (Heap.endBorrowRange m p values)
      (fun _ => block p (Cell.full values)) := by
  apply Triple.conseq (P' := block p (Cell.borrowed original))
    (Q' := fun (_ : Unit) h => True ∧ block p (Cell.full values) h)
    (fun _ h => h) (fun _ _ h => h.2)
  apply triple_replaceRange (old := Cell.borrowed original) (new := Cell.full values)
  · intro s hm
    have hl : (Cell.borrowed original).length = (Cell.full values).length := by
      simp [Cell.borrowed, Cell.full, hlen]
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨(), s', original, hu⟩
  · rintro s _ s' hm ⟨actual, hu⟩
    have hl : (Cell.borrowed original).length = (Cell.borrowed actual).length :=
      (by simpa [Cell.borrowed, Cell.full, hlen] using (replaceRange.length hu).symm)
    have he := Cell.borrowed_inj.mp (replaceRange.old_eq hm hl hu)
    subst actual
    exact ⟨trivial, hu⟩

theorem shareRange.spec (p : RawPtr ty) (values : List ty) (fraction : Nat) :
    Triple m (block p (Cell.shared fraction values)) (Heap.shareRange m p values.length)
      (fun result h => result = values ∧ block p (Cell.shared (fraction + 1) values) h) := by
  apply triple_replaceRange (old := Cell.shared fraction values)
    (new := Cell.shared (fraction + 1) values)
  · intro s hm
    have hl : (Cell.shared fraction values).length =
        (Cell.shared (fraction + 1) values).length := by simp [Cell.shared]
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨values, s', rfl, fraction, hu⟩
  · rintro s result s' hm ⟨hlen, f, hu⟩
    have hl : (Cell.shared fraction values).length = (Cell.shared f result).length := by
      simp [Cell.shared, hlen]
    have he := replaceRange.old_eq hm hl hu
    have hv := Cell.shared_values_eq he
    have hn := Cell.shared_succ_eq he
    subst result
    rw [← he, ← hn] at hu
    exact ⟨rfl, hu⟩

theorem endShareRange.spec (p : RawPtr ty) (values : List ty) (fraction : Nat) :
    Triple m (block p (Cell.shared (fraction + 1) values)) (Heap.endShareRange m p values)
      (fun _ => block p (Cell.shared fraction values)) := by
  apply Triple.conseq (P' := block p (Cell.shared (fraction + 1) values))
    (Q' := fun (_ : Unit) h => True ∧ block p (Cell.shared fraction values) h)
    (fun _ h => h) (fun _ _ h => h.2)
  apply triple_replaceRange (old := Cell.shared (fraction + 1) values)
    (new := Cell.shared fraction values)
  · intro s hm
    have hl : (Cell.shared (fraction + 1) values).length =
        (Cell.shared fraction values).length := by simp [Cell.shared]
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨(), s', fraction, hu⟩
  · rintro s _ s' hm ⟨f, hu⟩
    have hl : (Cell.shared (fraction + 1) values).length =
        (Cell.shared (f + 1) values).length := by simp [Cell.shared]
    have he := replaceRange.old_eq hm hl hu
    have hn := Cell.shared_pred_eq he
    rw [← he, ← hn] at hu
    exact ⟨trivial, hu⟩

theorem add.spec (p : RawPtr ty) (cs : List (Cell ty)) (count : Nat)
    (hne : cs ≠ []) (hbound : count ≤ cs.length) :
    Triple m (block p cs) (Heap.add m p count)
      (fun result h => result = p.shift count ∧ block p cs h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, _⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨before, after, hoff, hs⟩ := segment_of_matches hne hown
  have hb : p.offset + count ≤ (before ++ cs ++ after).length := by
    simp only [List.length_append]
    grind
  refine ⟨⟨p.shift count, s, ⟨_, hs, hb⟩, rfl, rfl⟩, ?_⟩
  rintro _ _ ⟨_, rfl, rfl⟩
  exact ⟨_, hd, hm, hi, rfl, rfl⟩

/-- Cleanup authority records the extent even when there are no cell resources. -/
theorem addWholeBlock.spec (p : RawPtr ty) (cs : List (Cell ty)) (own : Bool) (count : Nat)
    (hbound : count ≤ cs.length) :
    Triple m (sep (alloc p cs.length own) (block p cs)) (Heap.add m p count)
      (fun result h => result = p.shift count ∧ sep (alloc p cs.length own) (block p cs) h) := by
  intro h F s hp hd hm hi
  have hpre := hp
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p cs at hb
  subst h a b
  obtain ⟨hab, _⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨ha', hc⟩ := (Fragment.matches_union _ _ _ _).mp hab
  obtain ⟨_, hs⟩ := whole_of_matches hoff ha' hc
  have hbound' : p.offset + count ≤ cs.length := by simpa [hoff] using hbound
  refine ⟨⟨p.shift count, s, ⟨cs, hs, hbound'⟩, rfl, rfl⟩, ?_⟩
  rintro _ _ ⟨_, rfl, rfl⟩
  exact ⟨_, hd, hm, hi, rfl, hpre⟩

end SepLogic
end Aeneas.Std
