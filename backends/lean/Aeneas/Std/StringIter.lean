import Aeneas.Std.String
import Aeneas.Std.Core.Iter
import Aeneas.Std.SliceIter

namespace Aeneas.Std

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::next"]
def core.str.iter.IteratorChars.next (it : core.str.iter.Chars) : RustM ((Option Char) × core.str.iter.Chars) := do
  let (r, iter) ← core.slice.iter.IteratorSliceIter.next it.iter
  .ok (r.map Char.ofNat, ⟨iter⟩)

@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
noncomputable opaque core.str.iter.IteratorChars.collect
  {B : Type} (itertraitscollectFromIteratorBCharInst :
  core.iter.traits.collect.FromIterator B Char) :
  core.str.iter.Chars → RustM B

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>"]
def core.iter.traits.iterator.IteratorChars :
  core.iter.traits.iterator.Iterator core.str.iter.Chars Char := {
  next := core.str.iter.IteratorChars.next
}

@[rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : RustM core.str.iter.Chars :=
  .ok { iter := { slice := s, i := 0 } }

end Aeneas.Std
