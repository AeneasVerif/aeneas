-- [external]: templates for the external functions.
import Base
import External.Types
open Primitives
open external

/- [core::cell::{core::cell::Cell<T>#10}::get]: -/
def core.cell.Cell.get
  {T : Type} (markerCopyInst : core.marker.Copy T) (c : core.cell.Cell T) (s : State) :
  Result (State × T) :=
  sorry

/- [core::cell::{core::cell::Cell<T>#11}::get_mut]: -/
def core.cell.Cell.get_mut {T : Type} (c : core.cell.Cell T) (s : State) :
  Result (State × (T × (T → State → State × (core.cell.Cell T)))) :=
  sorry
