import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Fmt
import Aeneas.Std.Core.Cmp
import Aeneas.Std.Core.Hash

namespace Aeneas.Std

@[rust_trait "core::marker::DiscriminantKind"
  (parentClauses := ["cloneInst", "copyInst", "debugInst", "partialEqInst", "eqInst", "hashInst"])
  (types := ["Discriminant"])]
structure DiscriminantKind (Self : Type) where
  Discriminant : Type -- TODO: this should be a parameter
  cloneInst : core.clone.Clone Discriminant
  copyInst : core.marker.Copy Discriminant
  debugInst : core.fmt.Debug Discriminant
  partialEqInst : core.cmp.PartialEq Discriminant Discriminant
  eqInst : core.cmp.Eq Discriminant
  hashInst : core.hash.Hash Discriminant

/-- **IMPORTANT:** the type of this function is not correct, the reason being that we can not
actually model it (it relies on the existence of some builtin implementation of `DiscriminantKind`,
which are available to rustc but which we can't provide). Any code which relies on this definition
will not type-check. The reason why we provide it is that it happens that the LLBC crate contains
this definition, while it is actually not used in the extracted model: we just want Aeneas to consider
it as builtin so that it doesn't generate any axiom for it (this is a way of ignoring it). -/
@[rust_fun "core::intrinsics::discriminant_value"]
def core.intrinsics.discriminant_value
  {T : Type} (DiscrInst : DiscriminantKind T) (_ : T) :
  Result (DiscrInst.Discriminant) := .fail .undef -- TODO: we need

end Aeneas.Std
