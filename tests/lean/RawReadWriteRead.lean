/- Extracted by Aeneas, then manually corrected to retain reads after writes.
   The compiler is not patched. Re-extraction overwrites these corrections;
   see EXTRACTION.md. -/
-- [raw_read_write_read]
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

namespace raw_read_write_read

/-- [raw_read_write_read::read_write_read]:
    Source: 'tests/src/raw_read_write_read.rs', lines 5:0-9:1
    Visibility: public -/
def read_write_read (p : MutRawPtr Std.U32) : Result (Std.U32 × Std.U32) := do
  let before ← RawPtr.read p
  MutRawPtr.write p 1#u32
  let after ← RawPtr.read p
  ok (before, after)

/-- [raw_read_write_read::discarded_read]:
    Source: 'tests/src/raw_read_write_read.rs', lines 13:0-17:1
    Visibility: public -/
def discarded_read (p : MutRawPtr Std.U32) : Result Std.U32 := do
  let _ ← RawPtr.read p
  MutRawPtr.write p 1#u32
  RawPtr.read p

end raw_read_write_read
