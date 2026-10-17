module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Slice
public section

namespace Aeneas.Std

/-- The little-endian bytes of a `u64` (`to_ne_bytes`: the target is little-endian, as the
encoding of the values in memory). -/
@[expose] def core.hash.Hasher.u64Bytes (i : U64) : Slice U8 :=
  Slice.from (i.bv.toLEBytes.map UScalar.mk) (by simp; scalar_tac)

@[rust_trait "core::hash::Hasher"]
structure core.hash.Hasher (Self : Type _) where
  finish : Self → Result U64
  write : Self → Slice U8 → Result Self
  write_u64 : Self → U64 → Result Self := fun self i => write self (core.hash.Hasher.u64Bytes i)

/-- `Hasher::write_u64`: writes the bytes of the integer. -/
@[expose, trait_default, rust_fun "core::hash::Hasher::write_u64"]
def core.hash.Hasher.write_u64.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
    (self : Self) (i : U64) : Result Self :=
  HasherInst.write self (core.hash.Hasher.u64Bytes i)

@[rust_trait "core::hash::Hash"]
structure core.hash.Hash (Self : Type _) where
  hash : forall {H : Type}, core.hash.Hasher H → Self → H → Result H

end Aeneas.Std
