/- Extracted by Aeneas, then manually corrected in `alias_write` to retain the
   read after the write. The compiler is not patched. Re-extraction overwrites
   this correction; see EXTRACTION.md. -/
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
  (initial : Std.U32) (replacement : Std.U32) : Result Std.U32 := do
  let p ← alloc.boxed.Box.into_raw initial
  MutRawPtr.write p replacement
  let value ← RawPtr.read p
  let _ ← alloc.boxed.Box.from_raw p
  ok value

/-- [raw_box::stored_pointer]:
    Source: 'tests/src/raw_box.rs', lines 13:0-22:1
    Visibility: public -/
def stored_pointer
  (initial : Std.U32) (replacement : Std.U32) : Result Std.U32 := do
  let target ← alloc.boxed.Box.into_raw initial
  let slot ← alloc.boxed.Box.into_raw target
  let loaded ← RawPtr.read slot
  MutRawPtr.write loaded replacement
  let _ ← alloc.boxed.Box.from_raw slot
  alloc.boxed.Box.from_raw target

/-- [raw_box::alias_write]:
    Source: 'tests/src/raw_box.rs', lines 25:0-35:1
    Visibility: public -/
def alias_write
  (initial : Std.U32) (replacement : Std.U32) :
  Result (Std.U32 × Std.U32)
  := do
  let p ← alloc.boxed.Box.into_raw initial
  let before ← RawPtr.read p
  MutRawPtr.write p replacement
  let after ← RawPtr.read p
  let _ ← alloc.boxed.Box.from_raw p
  ok (before, after)

/-- [raw_box::replace_pair]:
    Source: 'tests/src/raw_box.rs', lines 38:0-45:1
    Visibility: public -/
def replace_pair
  (first : Std.U32) (second : Std.U32) (replacement : Std.U32) :
  Result (Std.U32 × Std.U32)
  := do
  let p ← alloc.boxed.Box.into_raw (first, second)
  let (i, _) ← RawPtr.read p
  MutRawPtr.write p (i, replacement)
  alloc.boxed.Box.from_raw p

/-- [raw_box::one_past_end]:
    Source: 'tests/src/raw_box.rs', lines 48:0-57:1
    Visibility: public -/
def one_past_end (value : Std.U32) : Result Std.U32 := do
  let p ← alloc.boxed.Box.into_raw value
  let start ← RawPtr.add p 0#usize
  let _ ← RawPtr.add p 1#usize
  let result ← RawPtr.read start
  let _ ← alloc.boxed.Box.from_raw p
  ok result

/-- [raw_box::zero_sized_box]:
    Source: 'tests/src/raw_box.rs', lines 60:0-66:1
    Visibility: public -/
def zero_sized_box : Result Unit := do
  let p ← alloc.boxed.Box.into_raw ()
  RawPtr.read p
  alloc.boxed.Box.from_raw p

end raw_box
