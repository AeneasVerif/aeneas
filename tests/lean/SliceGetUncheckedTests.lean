module
public import Aeneas
public section

open Aeneas.Std Result Error core.ops.range WP

namespace SliceGetUncheckedTests

def data : Slice Nat := Slice.from [10, 20] (by scalar_tac)

def getAt (i : Usize) : Result Nat :=
  core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice Nat) data i

def isUndef {T : Type} (r : Result T) : Bool :=
  match r.match with
  | .vis (.fail .undef) _ => true
  | _ => false

-- Success at both valid endpoints; UB at and beyond the exclusive upper bound.
#guard (getAt 0#usize).reducesTo 10
#guard (getAt 1#usize).reducesTo 20
#guard isUndef (getAt 2#usize)
#guard isUndef (getAt 3#usize)
#guard isUndef (core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice Nat)
  (Slice.new Nat) 0#usize)

-- Kernel proofs additionally check that the executable model is transparent.
example : getAt 0#usize = ok 10 := by
  simp [getAt, core.slice.Slice.get_unchecked, core.slice.index.Usize.get,
    Slice.getElem?_Usize_eq, data, bind_tc_ok]
example : getAt 2#usize = fail .undef := by
  simp [getAt, core.slice.Slice.get_unchecked, core.slice.index.Usize.get,
    Slice.getElem?_Usize_eq, data, bind_tc_ok]

def range (start stop : Usize) : Result (List Nat) := do
  let s ← core.slice.Slice.get_unchecked
    (core.slice.index.SliceIndexRangeUsizeSlice Nat) data ⟨start, stop⟩
  ok s.val

#guard (range 0#usize 2#usize).reducesTo [10, 20]
#guard (range 1#usize 2#usize).reducesTo [20]
#guard (range 2#usize 2#usize).reducesTo []
#guard isUndef (range 0#usize 3#usize)
#guard isUndef (range 2#usize 1#usize)

theorem inBounds {T : Type} [Inhabited T] (s : Slice T) (i : Usize)
    (h : i.val < s.length) :
    Aeneas.Std.WP.spec
      (core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice T) s i)
      (fun x => x = s[i]) :=
  core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec h

/-- info: 'SliceGetUncheckedTests.inBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inBounds

end SliceGetUncheckedTests
