-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [external]: opaque function definitions
import Base.Primitives
import External.Types

structure OpaqueDefs where
  
  /- [core::mem::swap] -/
  core_mem_swap_fwd (T : Type) : T -> T -> state -> result (state × Unit)
  
  /- [core::mem::swap] -/
  core_mem_swap_back0
    (T : Type) : T -> T -> state -> state -> result (state × T)
  
  /- [core::mem::swap] -/
  core_mem_swap_back1
    (T : Type) : T -> T -> state -> state -> result (state × T)
  
  /- [core::num::nonzero::NonZeroU32::{14}::new] -/
  core_num_nonzero_non_zero_u32_new_fwd
    :
    UInt32 -> state -> result (state × (Option
      core_num_nonzero_non_zero_u32_t))
  
  /- [core::option::Option::{0}::unwrap] -/
  core_option_option_unwrap_fwd
    (T : Type) : Option T -> state -> result (state × T)
  
