module

public import RawValueCasts.Types
public import RawValueCasts.Repr

@[expose] public section

open Aeneas.Std

namespace raw_value_casts.ext

def bool_to_byte (value : Bool) : Result U8 :=
  reinterpret boolRepr raw_transmute.byteRepr rfl value

def byte_to_bool (value : U8) : Result Bool :=
  reinterpret raw_transmute.byteRepr boolRepr rfl value

def unsigned_to_signed (value : U32) : Result I32 :=
  reinterpret raw_box.u32Repr signedRepr rfl value

def signed_to_unsigned (value : I32) : Result U32 :=
  reinterpret signedRepr raw_box.u32Repr rfl value

end raw_value_casts.ext
