/- `alloc::alloc`: the global allocator. It is the only allocator: registering another one with
`#[global_allocator]` is not modelled. -/
module
public import Aeneas.Std.Core.Core
public section

namespace Aeneas.Std

/-- The type of the global allocator - note it shouldn't appear in the generated code because
    we systematically filter it when providing information about the definitions supported by the standard
    libary. -/
@[rust_type "alloc::alloc::Global"]
inductive alloc.alloc.Global where | mk

@[expose, rust_fun "alloc::alloc::{core::clone::Clone<alloc::alloc::Global>}::clone"]
def alloc.alloc.CloneGlobal.clone (_ : alloc.alloc.Global) : Result alloc.alloc.Global := .ok .mk

@[expose, reducible, rust_trait_impl "core::clone::Clone<alloc::alloc::Global>"]
def core.clone.CloneGlobal : core.clone.Clone alloc.alloc.Global := {
  clone := alloc.alloc.CloneGlobal.clone
}

end Aeneas.Std
