-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [external]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.
import Base
import External.Types
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
open external

/- [core::cell::{core::cell::Cell<T>#10}::get]:
   Source: '/rustc/library/core/src/cell.rs', lines 509:4-509:26
   Name pattern: core::cell::{core::cell::Cell<@T>}::get -/
axiom core.cell.Cell.get
  (T : Type) (markerCopyInst : core.marker.Copy T) :
  core.cell.Cell T → State → Result (State × T)

/- [core::cell::{core::cell::Cell<T>#11}::get_mut]:
   Source: '/rustc/library/core/src/cell.rs', lines 587:4-587:39
   Name pattern: core::cell::{core::cell::Cell<@T>}::get_mut -/
axiom core.cell.Cell.get_mut
  (T : Type) :
  core.cell.Cell T → State → Result (State × (T × (T → State → Result
    (State × (core.cell.Cell T)))))

