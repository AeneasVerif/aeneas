-- [external]: templates for the external functions.
import Base
import External.Types
open Primitives
open external

-- TODO: fill those bodies

/- [core::mem::swap] -/
def core.mem.swap
  (T : Type) : T → T → State → Result (State × (T × T)) :=
  fun x y s => .ok (s, (y, x))

/- [core::num::nonzero::NonZeroU32::{14}::new] -/
def core.num.nonzero.NonZeroU32.new :
  U32 → State → Result (State × (Option core_num_nonzero_non_zero_u32_t)) :=
  fun _ _ => .fail .panic

/- [core::option::Option::{0}::unwrap] -/
def core.option.Option.unwrap
  (T : Type) : Option T → State → Result (State × T) :=
  fun _ _ => .fail .panic
