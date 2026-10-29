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
  List.map_inj_right fun _ _ h => (Cell.shared.inj h).2

theorem Cell.shared_values_eq {xs ys : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared f)) = (ys.map (Cell.shared g))) : xs = ys := by
  induction xs generalizing ys
  · have hy : ys = [] := by simpa using h.symm
    exact hy.symm
  · rename_i x xs ih
    cases ys
    · simp at h
    · rename_i y ys
      have hh := List.cons.inj h
      rw [(Cell.shared.inj hh.1).2, ih hh.2]

theorem Cell.shared_succ_eq {xs ys : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared f)) = (ys.map (Cell.shared g))) :
    (xs.map (Cell.shared (f + 1))) = (ys.map (Cell.shared (g + 1))) := by
  have hv := Cell.shared_values_eq h
  subst ys
  cases xs
  · rfl
  · have hf := (Cell.shared.inj (List.cons.inj h).1).1
    subst g
    rfl

theorem Cell.shared_pred_eq {xs : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared (f + 1))) = (xs.map (Cell.shared (g + 1)))) :
    (xs.map (Cell.shared f)) = (xs.map (Cell.shared g)) := by
  cases xs
  · rfl
  · have hf := Nat.add_right_cancel (Cell.shared.inj (List.cons.inj h).1).1
    subst g
    rfl

namespace SepLogic

variable {m : Layout.{u}}

theorem borrowRange.spec (p : RawPtr ty) (values : List ty)
    (hsize : values = [] ∨ 0 < m.byteLength ty) :
    Triple m (block p (Cell.full values)) (Heap.borrowRange m p values.length)
      (fun result h => result = values ∧
        block p (List.replicate values.length .borrowed) h) := by
  apply triple_replaceRange (old := Cell.full values)
    (new := List.replicate values.length .borrowed)
  · intro s hm
    have hl : (Cell.full values).length =
        (List.replicate values.length (.borrowed : Cell ty)).length := by simp [Cell.full]
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨values, s', rfl, hsize, hu⟩
  · rintro s result s' hm ⟨hlen, _, hu⟩
    have hl : (Cell.full values).length = (Cell.full result).length := by
      simp [Cell.full, hlen]
    have he := Cell.full_inj.mp (replaceRange.old_eq hm hl hu)
    subst result
    exact ⟨rfl, hu⟩

theorem endBorrowRange.spec (p : RawPtr ty) (values : List ty) :
    Triple m (block p (List.replicate values.length .borrowed)) (Heap.endBorrowRange m p values)
      (fun _ => block p (Cell.full values)) :=
  replaceRange.spec p _ _ (by simp [Cell.full])

theorem shareRange.spec (p : RawPtr ty) (values : List ty) (depth : Nat) :
    Triple m (block p (values.map (Cell.shared depth))) (Heap.shareRange m p values.length)
      (fun result h => result = values ∧ block p (values.map (Cell.shared (depth + 1))) h) := by
  apply triple_replaceRange (old := (values.map (Cell.shared depth)))
    (new := (values.map (Cell.shared (depth + 1))))
  · intro s hm
    have hl : (values.map (Cell.shared depth)).length =
        (values.map (Cell.shared (depth + 1))).length := by simp
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨values, s', rfl, depth, hu⟩
  · rintro s result s' hm ⟨hlen, f, hu⟩
    have hl : (values.map (Cell.shared depth)).length = (result.map (Cell.shared f)).length := by
      simp [hlen]
    have he := replaceRange.old_eq hm hl hu
    have hv := Cell.shared_values_eq he
    have hn := Cell.shared_succ_eq he
    subst result
    rw [← he, ← hn] at hu
    exact ⟨rfl, hu⟩

theorem endShareRange.spec (p : RawPtr ty) (values : List ty) (depth : Nat) :
    Triple m (block p (values.map (Cell.shared (depth + 1)))) (Heap.endShareRange m p values)
      (fun _ => block p (values.map (Cell.shared depth))) := by
  apply Triple.conseq (P' := block p (values.map (Cell.shared (depth + 1))))
    (Q' := fun (_ : Unit) h => True ∧ block p (values.map (Cell.shared depth)) h)
    (fun _ h => h) (fun _ _ h => h.2)
  apply triple_replaceRange (old := (values.map (Cell.shared (depth + 1))))
    (new := (values.map (Cell.shared depth)))
  · intro s hm
    have hl : (values.map (Cell.shared (depth + 1))).length =
        (values.map (Cell.shared depth)).length := by simp
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨(), s', depth, hu⟩
  · rintro s _ s' hm ⟨f, hu⟩
    have hl : (values.map (Cell.shared (depth + 1))).length =
        (values.map (Cell.shared (f + 1))).length := by simp
    have he := replaceRange.old_eq hm hl hu
    have hn := Cell.shared_pred_eq he
    rw [← he, ← hn] at hu
    exact ⟨trivial, hu⟩

theorem offset.spec (p : RawPtr ty) (cs : List (Cell ty)) (start target : Nat)
    (hne : cs ≠ []) (hstart : start ≤ cs.length) (htarget : target ≤ cs.length) :
    Triple m (block p cs)
      (Heap.offset m (⟨p.base, p.index + start⟩ : RawPtr ty) ((target : Int) - start))
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧ block p cs h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, _⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨r, hs, hv⟩ := views_of_matches hne hown
  have hrange := hv.bound hne
  have hb : p.index + start ≤ m.extent ty r ∧ p.index + target ≤ m.extent ty r := by grind
  have hextent : s.extent m ty p.base = some (m.extent ty r) := by
    simp [Heap.extent, hs]
  refine ⟨⟨⟨p.base, p.index + target⟩, s, ⟨_, hextent, hb⟩, rfl, ?_, rfl⟩, ?_⟩
  · grind
  · rintro result _ ⟨_, hbase, hindex, rfl⟩
    have hindex' : result.index = p.index + target := by grind
    have he : result = ⟨p.base, p.index + target⟩ := by
      cases result
      simp only [RawPtr.mk.injEq]
      exact ⟨hbase, hindex'⟩
    exact ⟨_, hd, hm, hi, he, rfl⟩

/-- Cleanup authority records the extent even when there are no cell resources. -/
theorem offsetWholeBlock.spec (p : RawPtr ty) (cs : List (Cell ty)) (own : Bool)
    (start target : Nat) (hstart : start ≤ cs.length) (htarget : target ≤ cs.length) :
    Triple m (sep (alloc p cs.length own) (block p cs))
      (Heap.offset m (⟨p.base, p.index + start⟩ : RawPtr ty) ((target : Int) - start))
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧
        sep (alloc p cs.length own) (block p cs) h) := by
  intro h F s hp hd hm hi
  have hpre := hp
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p cs at hb
  subst h a b
  obtain ⟨hab, _⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨ha', hc⟩ := (Fragment.matches_union _ _ _ _).mp hab
  obtain ⟨_, hs⟩ := whole_of_matches hoff ha' hc
  obtain ⟨r, hs, hn, _⟩ := hs
  have hextent : s.extent m ty p.base = some cs.length := by simp [Heap.extent, hs, hn]
  have hb : p.index + start ≤ cs.length ∧ p.index + target ≤ cs.length := by
    simpa [hoff] using And.intro hstart htarget
  refine ⟨⟨⟨p.base, p.index + target⟩, s, ⟨cs.length, hextent, hb⟩, rfl, ?_, rfl⟩, ?_⟩
  · grind
  · rintro result _ ⟨_, hbase, hindex, rfl⟩
    have hindex' : result.index = p.index + target := by grind
    have he : result = ⟨p.base, p.index + target⟩ := by
      cases result
      simp only [RawPtr.mk.injEq]
      exact ⟨hbase, hindex'⟩
    exact ⟨_, hd, hm, hi, he, hpre⟩

end SepLogic
end Aeneas.Std
