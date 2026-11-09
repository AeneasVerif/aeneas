module
public import Aeneas.Std.StringDef
public meta import Aeneas.Extract.Extract
@[expose] public section

namespace Aeneas.Std

/-- Undefined behavior if the bytes are not valid UTF-8. -/
@[rust_fun "core::str::converts::from_utf8_unchecked"]
def core.str.converts.from_utf8_unchecked (s : SharedBorrow (Slice U8)) : Result (SharedBorrow Str) :=
  if ByteArray.validateUTF8 ⟨(s.val.val.map fun b => UInt8.ofBitVec b.bv).toArray⟩ then
    .ok (SharedBorrow.mk s.val)
  else .fail .undef

end Aeneas.Std
