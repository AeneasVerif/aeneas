-- The user-filled copy of [Axioms2_Template.lean]: [SplitFiles.Layered]
-- imports this file, and re-extraction does not touch it.
import Aeneas
import SplitFiles.Layered.Part1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace split_files

/-- [split_files::layered::mystery]:
    Source: 'src/layered.rs', lines 11:0-13:1
    Visibility: public -/
def layered.mystery (x : Std.I32) : Result Std.I32 :=
  x + 1#i32

end split_files
