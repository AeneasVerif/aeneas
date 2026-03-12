//@ charon-args=--skip-borrowck
//@ [!lean] skip
#![allow(dead_code)]

// =============================================================================
// Tests from https://rust-lang.zulipchat.com/#narrow/channel/546987-project-goals.2F2026-workshop/topic/Roadmap.3A.20The.20borrow.20checker.20within/with/578439424
// =============================================================================

// Note that the symbolic execution simplifies `if true` away, which is why we
// introduce a variant below that branches on booleans that the function receives
// as input.
#[allow(dropping_references)]
fn unnecessary_error() {
    let mut x: (&u32,) = (&0,);
    let mut y: (&u32,) = (&1,);
    let mut z = 2;

    if true {
        y.0 = x.0; // creates `'x: 'y` subset relation
    }

    if true {
        x.0 = &z; // creates `{L0} in 'x` constraint

        // at this point, we have `'x: 'y` and `{L0} in 'x`, so we also have `{L0} in 'y`
        drop(x.0);
    }

    z += 1; // polonius flags an (unnecessary) error

    drop(y.0);
}

#[allow(dropping_references)]
fn unnecessary_error_2(b0: bool, b1: bool) {
    let mut x: (&u32,) = (&0,);
    let mut y: (&u32,) = (&1,);
    let mut z = 2;

    if b0 {
        y.0 = x.0;
    }

    if b1 {
        x.0 = &z;
        drop(x.0);
    }

    z += 1;

    drop(y.0);
}

// =============================================================================
// Tests from https://github.com/rust-lang/rust/blob/main/tests/ui/nll/polonius/iterating-updating-cursor-issue-57165.rs
// =============================================================================

struct X {
    next: Option<Box<X>>,
}

fn no_control_flow() {
    let mut b = Some(Box::new(X { next: None }));
    let mut p = &mut b;
    while let Some(now) = p {
        p = &mut now.next;
    }
}

fn conditional() {
    let mut b = Some(Box::new(X { next: None }));
    let mut p = &mut b;
    while let Some(now) = p {
        if true {
            p = &mut now.next;
        }
    }
}

fn conditional_with_indirection() {
    let mut b = Some(Box::new(X { next: None }));
    let mut p = &mut b;
    while let Some(now) = p {
        if true {
            p = &mut p.as_mut().unwrap().next;
        }
    }
}

fn conditional_with_indirection_2(b0: bool) {
    let mut b = Some(Box::new(X { next: None }));
    let mut p = &mut b;
    while let Some(now) = p {
        if b0 {
            p = &mut p.as_mut().unwrap().next;
        }
    }
}
