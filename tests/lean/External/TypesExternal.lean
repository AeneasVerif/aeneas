-- [external]: external types.
import Aeneas
open Lean Aeneas.Std

/- [core::num::nonzero::NonZeroU32]
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/num/nonzero.rs', lines 50:12-50:33 -/
structure core.cell.Cell (T : Type) where
  id : Nat

def CellValue := (T:Type) × T

/- The state type used in the state-error monad

   TODO: we tried the following definition, but it makes State a Type 1, leading
   to type errors later:

     structure State :=
       cells : AssocList Nat CellValue
  -/
axiom State : Type
