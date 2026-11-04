/- Extracted by Aeneas, then adapted to explicit representations and corrected in
   `alias_write` to retain the read after the write. The compiler is not patched.
   Re-extraction overwrites these adaptations; see EXTRACTION.md. -/
-- [raw_box]
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace raw_box

/-- [raw_box::round_trip]:
    Source: 'tests/src/raw_box.rs', lines 3:0-11:1
    Visibility: public -/
def round_trip
  (repr : Aeneas.Std.Repr Std.U32)
  (initial : Std.U32) (replacement : Std.U32) : Result Std.U32 := do
  let p ← alloc.boxed.Box.into_raw repr initial
  MutRawPtr.write repr p replacement
  let value ← RawPtr.read repr p
  let _ ← alloc.boxed.Box.from_raw repr p
  ok value

/-- [raw_box::stored_pointer]:
    Source: 'tests/src/raw_box.rs', lines 13:0-22:1
    Visibility: public -/
def stored_pointer
  (repr : Aeneas.Std.Repr Std.U32) (pointerRepr : Aeneas.Std.Repr (MutRawPtr Std.U32))
  (initial : Std.U32) (replacement : Std.U32) : Result Std.U32 := do
  let target ← alloc.boxed.Box.into_raw repr initial
  let slot ← alloc.boxed.Box.into_raw pointerRepr target
  let loaded ← RawPtr.read pointerRepr slot
  MutRawPtr.write repr loaded replacement
  let _ ← alloc.boxed.Box.from_raw pointerRepr slot
  alloc.boxed.Box.from_raw repr target

/-- [raw_box::alias_write]:
    Source: 'tests/src/raw_box.rs', lines 25:0-35:1
    Visibility: public -/
def alias_write
  (repr : Aeneas.Std.Repr Std.U32)
  (initial : Std.U32) (replacement : Std.U32) :
  Result (Std.U32 × Std.U32)
  := do
  let p ← alloc.boxed.Box.into_raw repr initial
  let before ← RawPtr.read repr p
  MutRawPtr.write repr p replacement
  let after ← RawPtr.read repr p
  let _ ← alloc.boxed.Box.from_raw repr p
  ok (before, after)

/-- [raw_box::replace_pair]:
    Source: 'tests/src/raw_box.rs', lines 38:0-45:1
    Visibility: public -/
def replace_pair
  (repr : Aeneas.Std.Repr (Std.U32 × Std.U32))
  (first : Std.U32) (second : Std.U32) (replacement : Std.U32) :
  Result (Std.U32 × Std.U32)
  := do
  let p ← alloc.boxed.Box.into_raw repr (first, second)
  let (i, _) ← RawPtr.read repr p
  MutRawPtr.write repr p (i, replacement)
  alloc.boxed.Box.from_raw repr p

/-- [raw_box::one_past_end]:
    Source: 'tests/src/raw_box.rs', lines 48:0-57:1
    Visibility: public -/
def one_past_end (repr : Aeneas.Std.Repr Std.U32) (value : Std.U32) : Result Std.U32 := do
  let p ← alloc.boxed.Box.into_raw repr value
  let start ← RawPtr.add repr p 0#usize
  let _ ← RawPtr.add repr p 1#usize
  let result ← RawPtr.read repr start
  let _ ← alloc.boxed.Box.from_raw repr p
  ok result

/-- [raw_box::zero_sized_box]:
    Source: 'tests/src/raw_box.rs', lines 60:0-66:1
    Visibility: public -/
def zero_sized_box (repr : Aeneas.Std.Repr Unit) : Result Unit := do
  let p ← alloc.boxed.Box.into_raw repr ()
  RawPtr.read repr p
  alloc.boxed.Box.from_raw repr p

end raw_box
