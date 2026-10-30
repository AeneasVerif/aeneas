module

public import RawTransmuteExternals.Types
public import RawTransmute
import all Aeneas.Std.Core.Ptr

/- Models for the opaque Rust wrappers, not replacements for generated callers.
The access wrappers use the fixture's explicit little-endian word and identity-byte
descriptors. Pointer transmutes themselves are independent of either descriptor.
Rust's default Sized bounds restrict these wrappers to thin pointers. -/

@[expose] public section

open Aeneas.Std

namespace raw_transmute_externals.ext

def transmute_mut {T : Type} (U : Type) (p : MutRawPtr T) : Result (MutRawPtr U) :=
  .ok (RawPtr.cast U p)

def transmute_const {T : Type} (U : Type) (p : ConstRawPtr T) : Result (ConstRawPtr U) :=
  .ok (RawPtr.cast U p)

def read_word (p : MutRawPtr U32) : Result U32 :=
  RawPtr.read raw_box.u32Repr p

def write_word (p : MutRawPtr U32) (value : U32) : Result Unit :=
  MutRawPtr.write raw_box.u32Repr p value

def read_byte (p : MutRawPtr U8) : Result U8 :=
  RawPtr.read raw_transmute.byteRepr p

def write_byte (p : MutRawPtr U8) (value : U8) : Result Unit :=
  MutRawPtr.write raw_transmute.byteRepr p value

end raw_transmute_externals.ext
