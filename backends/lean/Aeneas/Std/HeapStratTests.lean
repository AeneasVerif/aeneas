module
import Aeneas.Std.HeapStrat
import Aeneas.Std.Alloc.Boxed
import Aeneas.Std.Slice
import Aeneas.Do.Elab

/-! Stratified heap tests: a raw pointer of level `n + 1` can hold a function of level `n`, code
of a lower level runs at a higher one (Lean inserts the lift), the pointer operations work at every
level, and a function can never be stored at its own level. -/

namespace Aeneas.Std.HeapStratTests

/-- Level 0: `*q += 1`. -/
def incr (q : MutRawPtr Nat) : Result Unit := do
  let n ← q.read
  q.write (n + 1)

/-- Level 1: a `Box<dyn Fn(usize) -> usize>` behind a raw pointer, called on `*q`.
```rust
let p = Box::into_raw(f);
let r = unsafe { (*p)(*q) };
incr(q);
unsafe { *q = r; drop(Box::from_raw(p)) };
r
```
-/
def callStored (f : Nat → Result Nat) (q : MutRawPtr Nat) : Result%1 Nat := do
  let p ← alloc.boxed.Box.into_raw f
  let g ← p.read
  let n ← q.read
  let r ← g n
  incr q
  q.write r
  let _ ← alloc.boxed.Box.from_raw p
  pure r

/-- Level 1: a slice of closures seen through a raw pointer, `s.as_ptr().add(i).read()(x)`. -/
def callNth (s : Slice (Nat → Result Nat)) (i : Usize) (x : Nat) : Result%1 Nat := do
  let (p, back) ← s.as_ptr
  let p ← p.add i
  let g ← p.read
  let r ← g x
  back
  pure r

/-- Level 1, recursive: applies the stored closure `n` times. -/
def iterate (p : MutRawPtr (Nat → Result Nat)) (n x : Nat) : Result%1 Nat :=
  match n with
  | 0 => pure x
  | n + 1 => do
    let g ← p.read
    let y ← g x
    iterate p n y
partial_fixpoint

/-- Generic in the heap: the same code runs at every level that stores `Nat`. -/
def bump [Stores H Nat] (q : MutRawPtr Nat) : ResultAt H Unit := do
  let n ← q.read
  q.write (n + 1)

example (q : MutRawPtr Nat) : Result Unit := bump q
example (q : MutRawPtr Nat) : Result%2 Unit := bump q

/-- Generic in the levels: stores a closure of a level `L` below and calls it. The constraints
say that `H` has a layer for the code of `L` and runs it, so the same definition works at every
pair of levels, and only the callers pick the levels. -/
def callStoredAt [Stores H (Nat → ResultAt L Nat)] [Stores L Nat]
    [MonadLiftT (ResultAt L) (ResultAt H)] (f : Nat → ResultAt L Nat) (q : MutRawPtr Nat) :
    ResultAt H Nat := do
  let p ← alloc.boxed.Box.into_raw f
  let g ← p.read
  let n ← (q.read : ResultAt L Nat)
  let r ← g n
  let _ ← alloc.boxed.Box.from_raw p
  pure r

example (f : Nat → Result Nat) (q : MutRawPtr Nat) : Result%1 Nat := callStoredAt f q
example (f : Nat → Result%1 Nat) (q : MutRawPtr Nat) : Result%2 Nat := callStoredAt f q
example (f : Nat → Result Nat) (q : MutRawPtr Nat) : Result%2 Nat := callStoredAt f q

/-! Landin's knot: a function of level 1 would reach the cell that stores it. It does not fit in
the layer of level 1 (`Nat → Result%1 Nat : Type 2`). -/
/--
info: failed to synthesize instance of type class
  Stores (HeapS Heap0) (ℕ → ResultAt (HeapS Heap0) ℕ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check_failure (alloc.alloc.Global.allocate .mk [fun x => pure x] :
  Result%1 (MutRawPtr (Nat → Result%1 Nat)))

/-! `State : Type 1` (a type, no function) lives in the layer of level 1. -/

structure Entry where
  Payload : Type
  value : Payload

structure State where
  entries : List Entry

/-- Answers `Unit`, and uses both layers: `*q += (*p).entries.len()`. -/
def addCount (p : MutRawPtr State) (q : MutRawPtr Nat) : Result%1 Unit := do
  let s ← p.read
  let n ← q.read
  q.write (n + s.entries.length)

def push (p : MutRawPtr State) (e : Entry) : Result%1 Unit := do
  let s ← p.read
  p.write ⟨e :: s.entries⟩

end Aeneas.Std.HeapStratTests
