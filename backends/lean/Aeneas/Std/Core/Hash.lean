module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Slice
public section

namespace Aeneas.Std

@[rust_trait "core::hash::Hasher"]
structure core.hash.Hasher (Self : Type _) where
  finish : Self → Result U64
  write : Self → Slice U8 → Result Self

@[rust_trait "core::hash::Hash"]
structure core.hash.Hash (Self : Type _) where
  hash : forall {H : Type}, core.hash.Hasher H → Self → H → Result H

end Aeneas.Std
