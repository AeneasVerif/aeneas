import Aeneas.Std.String

namespace Aeneas.Std

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

/- [core::str::iter::{core::iter::traits::iterator::Iterator<char> for core::str::iter::Chars<'a>}::collect]:
   Source: '/rustc/library/core/src/str/iter.rs', lines 35:0-35:31
   Name pattern: [core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect] -/
@[rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
def core.str.iter.IteratorChars.collect
  {B : Type} (itertraitscollectFromIteratorBCharInst :
  core.iter.traits.collect.FromIterator B Char) :
  core.str.iter.Chars → Result B := sorry

@[rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : Result core.str.iter.Chars := sorry

end Aeneas.Std
