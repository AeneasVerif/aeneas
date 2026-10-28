module

public import Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u v

namespace RawPtr

@[simp] theorem base_shift (p : RawPtr ty) (n : Nat) : (p.shift n).base = p.base := rfl
@[simp] theorem offset_shift (p : RawPtr ty) (n : Nat) :
    (p.shift n).offset = p.offset + n := rfl
@[simp] theorem shift_zero (p : RawPtr ty) : p.shift 0 = p := rfl

theorem shift_shift (p : RawPtr ty) (i j : Nat) :
    (p.shift i).shift j = p.shift (i + j) := by
  simp [shift, Nat.add_assoc]

end RawPtr

namespace Heap

variable {Repr : Type v} {m : Layout.{u}}

theorem inv_empty : (empty : Heap Repr).Inv := fun _ _ => ⟨rfl, rfl⟩

@[simp] theorem load_store (s : Heap m.Repr) (ty : Type u) (base : BasePtr)
    (cs : List (Cell ty)) :
    (s.store m.represent ty base cs).load m.interpret ty base = some cs := by
  simpa [load, store, update] using m.roundTrip ty cs

theorem load_store_other (s : Heap m.Repr) (ty otherTy : Type u)
    (base other : BasePtr) (cs : List (Cell ty)) (hne : other ≠ base) :
    (s.store m.represent ty base cs).load m.interpret otherTy other =
      s.load m.interpret otherTy other := by
  simp [load, store, update, hne]

@[simp] theorem load_createRepr (s : Heap Repr) (interpret) (ty : Type u)
    (r : Repr) (own : Bool) :
    (s.createRepr r own).load interpret ty s.next = interpret ty r := by
  simp [load, createRepr, update]

theorem load_createRepr_other (s : Heap Repr) (interpret) (ty : Type u)
    (r : Repr) (own : Bool) (base : BasePtr) (hne : base ≠ s.next) :
    (s.createRepr r own).load interpret ty base = s.load interpret ty base := by
  simp [load, createRepr, update, hne]

@[simp] theorem load_remove (s : Heap Repr) (interpret) (ty : Type u) (base : BasePtr) :
    (s.remove base).load interpret ty base = none := by
  simp [load, remove, update]

theorem load_remove_other (s : Heap Repr) (interpret) (ty : Type u)
    (base other : BasePtr) (hne : other ≠ base) :
    (s.remove base).load interpret ty other = s.load interpret ty other := by
  simp [load, remove, update, hne]

theorem Inv.base_lt {s : Heap Repr} (h : s.Inv)
    {interpret : (ty : Type u) → Repr → Option (List (Cell ty))}
    {ty : Type u} {base : BasePtr} {cs : List (Cell ty)}
    (hc : s.load interpret ty base = some cs) : base < s.next := by
  apply Nat.lt_of_not_ge
  intro hn
  have hf := (h base hn).1
  simp [load, hf] at hc

theorem Inv.store {s : Heap Repr} (h : s.Inv) (represent)
    (ty : Type u) (base : BasePtr) (cs : List (Cell ty)) (hb : base < s.next) :
    (s.store represent ty base cs).Inv := by
  intro other ho
  change s.next ≤ other at ho
  have hne : other ≠ base := by grind
  simpa [Heap.store, update, hne] using h other ho

theorem Inv.createRepr {s : Heap Repr} (h : s.Inv) (r : Repr) (own : Bool) :
    (s.createRepr r own).Inv := by
  intro base hb
  change s.next + 1 ≤ base at hb
  have hne : base ≠ s.next := by grind
  have hle : s.next ≤ base := by grind
  simpa [Heap.createRepr, update, hne] using h base hle

theorem Inv.remove {s : Heap Repr} (h : s.Inv) (base : BasePtr) :
    (s.remove base).Inv := by
  intro other ho
  change s.next ≤ other at ho
  by_cases he : other = base
  · simp [Heap.remove, update, he]
  · simpa [Heap.remove, update, he] using h other ho

theorem replaceRange.load {s s' : Heap m.Repr} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : replaceRange m s p old new s') (hne : old ≠ []) :
    ∃ before after, before.length = p.offset ∧
      s.load m.interpret ty p.base = some (before ++ old ++ after) ∧
      s'.load m.interpret ty p.base = some (before ++ new ++ after) := by
  obtain ⟨_, before, after, hoff, hs, rfl⟩ := (ite_eq_right hne).mp h
  exact ⟨before, after, hoff, hs, load_store _ _ _ _⟩

theorem replaceRange.inv {s s' : Heap m.Repr} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : replaceRange m s p old new s') (hi : s.Inv) :
    s'.Inv := by
  by_cases he : old = []
  · have hs : s' = s := ((ite_eq_left he).mp h).2
    simpa [hs] using hi
  · obtain ⟨_, before, after, _, hs, rfl⟩ := (ite_eq_right he).mp h
    exact hi.store _ _ _ _ (hi.base_lt hs)

theorem alloc.exists (m : Layout.{u}) (ty : Type u) (count : Nat)
    (s : Heap m.Repr) (hi : s.Inv) :
    ∃ p s', alloc m count s (p : RawPtr ty) s' := by
  exact ⟨⟨s.next, 0⟩, s.createRepr (m.fresh ty count) true, hi, rfl,
    m.fresh ty count, m.fresh_uninitialized ty count, m.fresh_interpret ty count, rfl⟩

end Heap
end Aeneas.Std
