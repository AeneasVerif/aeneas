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
  List.map_inj_right fun _ _ h => Option.some.inj (Cell.shared.inj h).2

theorem Cell.shared_values_eq {xs ys : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared f ∘ some)) = (ys.map (Cell.shared g ∘ some))) : xs = ys := by
  induction xs generalizing ys
  · have hy : ys = [] := by simpa using h.symm
    exact hy.symm
  · rename_i x xs ih
    cases ys
    · simp at h
    · rename_i y ys
      have hh := List.cons.inj h
      rw [Option.some.inj (Cell.shared.inj hh.1).2, ih hh.2]

theorem Cell.shared_succ_eq {xs ys : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared f ∘ some)) = (ys.map (Cell.shared g ∘ some))) :
    (xs.map (Cell.shared (f + 1) ∘ some)) = (ys.map (Cell.shared (g + 1) ∘ some)) := by
  have hv := Cell.shared_values_eq h
  subst ys
  cases xs
  · rfl
  · have hf := (Cell.shared.inj (List.cons.inj h).1).1
    subst g
    rfl

theorem Cell.shared_pred_eq {xs : List ty} {f g : Nat}
    (h : (xs.map (Cell.shared (f + 1) ∘ some)) = (xs.map (Cell.shared (g + 1) ∘ some))) :
    (xs.map (Cell.shared f ∘ some)) = (xs.map (Cell.shared g ∘ some)) := by
  cases xs
  · rfl
  · have hf := Nat.add_right_cancel (Cell.shared.inj (List.cons.inj h).1).1
    subst g
    rfl

namespace SepLogic

theorem borrowRange.spec (p : RawPtr ty) (values : List ty)
    (hsize : values = [] ∨ 0 < Heap.size ty) :
    Triple (block p (Cell.full values)) (Heap.borrowRange p values.length)
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
    Triple (block p (List.replicate values.length .borrowed)) (Heap.endBorrowRange p values)
      (fun _ => block p (Cell.full values)) :=
  replaceRange.spec p _ _ (by simp [Cell.full])

theorem shareRange.spec (p : RawPtr ty) (values : List ty) (depth : Nat) :
    Triple (block p (values.map (Cell.shared depth ∘ some))) (Heap.shareRange p values.length)
      (fun result h => result = values ∧ block p (values.map (Cell.shared (depth + 1) ∘ some)) h) := by
  apply triple_replaceRange (old := (values.map (Cell.shared depth ∘ some)))
    (new := (values.map (Cell.shared (depth + 1) ∘ some)))
  · intro s hm
    have hl : (values.map (Cell.shared depth ∘ some)).length =
        (values.map (Cell.shared (depth + 1) ∘ some)).length := by simp
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨values, s', rfl, depth, hu⟩
  · rintro s result s' hm ⟨hlen, f, hu⟩
    have hl : (values.map (Cell.shared depth ∘ some)).length = (result.map (Cell.shared f ∘ some)).length := by
      simp [hlen]
    have he := replaceRange.old_eq hm hl hu
    have hv := Cell.shared_values_eq he
    have hn := Cell.shared_succ_eq he
    subst result
    rw [← he, ← hn] at hu
    exact ⟨rfl, hu⟩

theorem endShareRange.spec (p : RawPtr ty) (values : List ty) (depth : Nat) :
    Triple (block p (values.map (Cell.shared (depth + 1) ∘ some))) (Heap.endShareRange p values)
      (fun _ => block p (values.map (Cell.shared depth ∘ some))) := by
  apply Triple.conseq (P' := block p (values.map (Cell.shared (depth + 1) ∘ some)))
    (Q' := fun (_ : Unit) h => True ∧ block p (values.map (Cell.shared depth ∘ some)) h)
    (fun _ h => h) (fun _ _ h => h.2)
  apply triple_replaceRange (old := (values.map (Cell.shared (depth + 1) ∘ some)))
    (new := (values.map (Cell.shared depth ∘ some)))
  · intro s hm
    have hl : (values.map (Cell.shared (depth + 1) ∘ some)).length =
        (values.map (Cell.shared depth ∘ some)).length := by simp
    obtain ⟨s', hu⟩ := replaceRange.exists hl hm
    exact ⟨(), s', depth, hu⟩
  · rintro s _ s' hm ⟨f, hu⟩
    have hl : (values.map (Cell.shared (depth + 1) ∘ some)).length =
        (values.map (Cell.shared (f + 1) ∘ some)).length := by simp
    have he := replaceRange.old_eq hm hl hu
    have hn := Cell.shared_pred_eq he
    rw [← he, ← hn] at hu
    exact ⟨trivial, hu⟩

theorem offset.spec (p : RawPtr ty) (cs : List (Cell ty)) (start target : Nat)
    (hne : cs ≠ []) (hstart : start ≤ cs.length) (htarget : target ≤ cs.length) :
    Triple (block p cs)
      (Heap.offset (⟨p.base, p.index + start⟩ : RawPtr ty) ((target : Int) - start))
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧ block p cs h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, _⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨r, hs, ha, hv⟩ := views_of_matches hne hown
  have hrange := hv.bound hne
  have hb : p.index + start ≤ Std.Block.extent ty r ∧ p.index + target ≤ Std.Block.extent ty r := by grind
  have hextent : s.extent ty p.base = some (Std.Block.extent ty r) := by
    simp [Heap.extent, hs, ha]
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
    Triple (sep (alloc p cs.length own) (block p cs))
      (Heap.offset (⟨p.base, p.index + start⟩ : RawPtr ty) ((target : Int) - start))
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧
        sep (alloc p cs.length own) (block p cs) h) := by
  intro h F s hp hd hm hi
  have hpre := hp
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p cs at hb
  subst h a b
  obtain ⟨hab, _⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨ha', hc⟩ := (Fragment.matches_union _ _ _).mp hab
  obtain ⟨_, hs⟩ := whole_of_matches hoff ha' hc
  obtain ⟨r, hs, halign, hn, _⟩ := hs
  have hextent : s.extent ty p.base = some cs.length := by
    simp [Heap.extent, hs, halign, hn]
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
