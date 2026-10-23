//@ [!lean] skip
//! String and char literals that Lean's lexer needs escaped (issue #1467):
//! a `"` or a `'` in a literal, backslashes, control characters, non-ASCII.
//! Only the chars are checked at extraction time: `Chars::next` is opaque in
//! the Lean standard library, so the strings cannot be inspected by `#guard`.
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(unused)]

fn quote_in_string() -> &'static str {
    "x\" axiom evil : False --"
}

fn escapes_in_string() -> &'static str {
    "tab\tnl\nq\"bs\\é€😀\u{7f}\r"
}

fn quote() -> char {
    '\''
}

fn backslash() -> char {
    '\\'
}

fn newline() -> char {
    '\n'
}

fn double_quote() -> char {
    '"'
}

fn non_ascii() -> char {
    'é'
}

fn astral() -> char {
    '😀'
}

fn is_quote(c: char) -> bool {
    c == '\''
}

#[verify::test]
fn test_chars() {
    assert!(quote() == '\'');
    assert!(backslash() == '\\');
    assert!(newline() == '\n');
    assert!(double_quote() == '"');
    assert!(non_ascii() == 'é');
    assert!(astral() == '😀');
    assert!(is_quote('\''));
    assert!(!is_quote('"'));
}
