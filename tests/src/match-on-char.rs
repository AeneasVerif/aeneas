//@ known-failure
//@ no-check-output
fn match_on_char_symbolic(c: char) -> usize {
    match c {
        'a' => 0,
        _ => 1,
    }
}

fn match_on_char_concrete() -> usize {
    match 'a' {
        'a' => 0,
        _ => 1,
    }
}

fn match_on_char_multiple_arms(c: char) -> usize {
    match c {
        'a' => 0,
        'b' => 1,
        'c' => 2,
        _ => 3,
    }
}

fn match_on_char_or_pattern(c: char) -> usize {
    match c {
        'a' | 'b' => 0,
        _ => 1,
    }
}
