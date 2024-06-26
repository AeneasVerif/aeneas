-- [external]: opaque function definitions
import Base
import External.Types
open Primitives

namespace external

structure OpaqueDefs where
  
  /- [core::mem::swap] -/
  core.mem.swap_fwd (T : Type) : T → T → State → Result (State × Unit)
  
  /- [core::mem::swap] -/
  core.mem.swap_back0
    (T : Type) : T → T → State → State → Result (State × T)
  
  /- [core::mem::swap] -/
  core.mem.swap_back1
    (T : Type) : T → T → State → State → Result (State × T)
  
  /- [core::num::nonzero::NonZeroU32::{14}::new] -/
  core.num.nonzero.NonZeroU32.new_fwd
    :
    U32 → State → Result (State × (Option
      core_num_nonzero_non_zero_u32_t))
  
  /- [core::option::Option::{0}::unwrap] -/
  core.option.Option.unwrap_fwd
    (T : Type) : Option T → State → Result (State × T)
  
end external
