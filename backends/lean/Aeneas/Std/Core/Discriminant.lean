import Aeneas.Std.Core.Core
import Aeneas.Std.Core.Fmt
import Aeneas.Std.Core.Cmp
import Aeneas.Std.Core.Hash

namespace Aeneas.Std

@[rust_trait "core::marker::DiscriminantKind"]
structure DisciminantKind (Self Discriminant : Type) where
  cloneInst : core.clone.Clone Discriminant
  copyInst : core.marker.Copy Discriminant
  debugInst : core.fmt.Debug Discriminant
  partialEqInst : core.cmp.PartialEq Discriminant Discriminant
  eqInst : core.cmp.Eq Discriminant
  hashInst : core.hash.Hash Discriminant

end Aeneas.Std
