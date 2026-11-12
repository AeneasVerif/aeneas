-- The model of the opaque function of `cross_crate_lib` (filled copy of `FunsExternal_Template.lean`)
module
public import Aeneas
public import CrossCrateLib.Types
@[expose] public section
open Aeneas Aeneas.Std Result
open cross_crate_lib

/-- [cross_crate_lib::checksum] -/
def checksum (x : Std.U32) : Result Std.U32 := x % 251#u32
