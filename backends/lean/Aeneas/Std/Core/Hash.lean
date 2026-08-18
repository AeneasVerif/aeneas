import Aeneas.Std.Core.Core
import Aeneas.Std.Slice

namespace Aeneas.Std

@[rust_trait "core::hash::Hasher"]
structure core.hash.Hasher (Self : Type) where
  finish : Self → RustM U64
  write : Self → Slice U8 → RustM Self

@[rust_trait "core::hash::Hash"]
structure core.hash.Hash (Self : Type) where
  hash : forall {H : Type}, core.hash.Hasher H → Self → H → RustM H

end Aeneas.Std
