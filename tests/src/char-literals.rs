//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Character literals that need escaping, or that are not ASCII, in the generated Lean.

pub fn quote() -> char {
    '\''
}

pub fn backslash() -> char {
    '\\'
}

pub fn newline() -> char {
    '\n'
}

pub fn nul() -> char {
    '\0'
}

pub fn del() -> char {
    '\x7f'
}

pub fn e_acute() -> char {
    'é'
}

pub fn line_separator() -> char {
    '\u{2028}'
}

pub fn smiley() -> char {
    '😀'
}

pub fn is_quote(c: char) -> bool {
    c == '\'' || c == '\\' || c == '\n'
}

#[verify::test]
pub fn test_char_literals() {
    // Each literal denotes its own code point: they are pairwise distinct and
    // `is_quote` recognises exactly the escaped ones.
    assert!(is_quote(quote()));
    assert!(is_quote(backslash()));
    assert!(is_quote(newline()));
    assert!(!is_quote(nul()));
    assert!(!is_quote(del()));
    assert!(!is_quote(e_acute()));
    assert!(!is_quote(line_separator()));
    assert!(!is_quote(smiley()));
    assert!(quote() != backslash());
    assert!(nul() != del());
    assert!(e_acute() != line_separator());
    assert!(line_separator() != smiley());
    assert!(is_quote('\\'));
    assert!(!is_quote('a'));
}
