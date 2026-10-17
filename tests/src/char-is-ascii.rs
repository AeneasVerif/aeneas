//@ [!lean] skip
//! `char::is_ascii`, as used by unicode-ident.

pub fn ascii(c: char) -> bool {
    c.is_ascii()
}
