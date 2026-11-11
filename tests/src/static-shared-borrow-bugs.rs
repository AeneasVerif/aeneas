//@ [!lean] skip
//! Regression tests for 6 bugs in Lean lambda extraction and `'static` /
//! shared-borrow region abstraction joins, projections, and loop fixed points.

fn nop() {}

pub struct Ptr(pub usize);

fn borrow_unit(x: &mut (i32, ())) -> &mut () {
    &mut x.1
}

fn id_static(x: &'static u32) -> &'static u32 {
    x
}

fn to_ptr(_x: &'static u32) -> Ptr {
    Ptr(0)
}

fn first3(x: &'static u32, _y: &'static u32, _z: &'static u32) -> &'static u32 {
    x
}

fn take_static(_x: &'static u32) {}

fn take_two_static(_x: &'static u32, _y: &'static u32) {}

fn reborrow_mut_with_shr(m: &'static mut i32, _s: &'static u32) -> &'static mut i32 {
    m
}

pub enum OptRef<'a> {
    None,
    Some(&'a u32),
}

fn consume_opt<'a>(_o: OptRef<'a>) {}

/// Bug 0: Lean universe-unification failure on unannotated ignored/unused
/// lambda binders (`fun _ => ...`) inside a join's backward continuation.
pub fn bug0_lambda_universe(b: bool) -> i32 {
    let mut x = (1, ());
    let r = if b { borrow_unit(&mut x) } else { &mut x.1 };
    nop();
    *r = ();
    x.0
}

/// Bug 1: `Not_found` in `collapse_ctx_following_sequence` when updating
/// `shared_borrows_seq` for an unmerged `'static` abstraction.
pub fn bug1_unmerged_static_abs(b: bool, x: &'static u32, y: &'static u32) -> Ptr {
    let p = if b { to_ptr(x) } else { to_ptr(y) };
    nop();
    p
}

/// Bug 2: `project_context` deleting a `PLeft`-only `'static` abstraction whose
/// `avalues` become empty on `PRight` even though `add_borrows_seq` targets it
/// (and retaining its left-side `Join` continuation if kept naively).
pub fn bug2_projected_empty_abs(b: bool, x: &'static u32) -> Ptr {
    let p = if b {
        let y = id_static(x);
        to_ptr(y)
    } else {
        Ptr(0)
    };
    nop();
    p
}

/// Bug 3: `eliminate_shared_borrow_markers` double-counting `i + !offset` and
/// drifting indices across `PLeft`/`PRight` elements when recording `shared_borrows_seq`.
pub fn bug3_borrow_insertion_offset(
    b: bool,
    x: &'static u32,
    y: &'static u32,
    z: &'static u32,
) -> Option<&'static u32> {
    let o = if b { Some(first3(x, y, z)) } else { None };
    nop();
    o
}

/// Bug 4: Loop fixed-point divergence when loan-free abstractions sharing a
/// concrete shared borrow accumulate across iterations without merging in `reduce_ctx`.
pub fn bug4_loop_loan_free_shared_borrow(mut n: i32, x: &'static u32) -> u32 {
    take_static(x);
    loop {
        if n <= 0 {
            break;
        }
        take_static(x);
        n -= 1;
    }
    *x
}

/// Follow-up 1 to Bug 4: `iterate_shared_borrows` must not merge abstractions
/// that also hold mutable borrows / ended mutable loans, and `reorder_fresh_abs`
/// must ignore ephemeral `SharedBorrowId`s so `(m1, m2)` is not swapped across breaks.
pub fn bug4_mut_and_shared_static(
    mut n: i32,
    cond: bool,
    m1: &'static mut i32,
    m2: &'static mut i32,
    s: &'static u32,
) -> u32 {
    loop {
        if n <= 0 {
            let r1 = reborrow_mut_with_shr(m1, s);
            *r1 = 1;
            let r2 = reborrow_mut_with_shr(m2, s);
            *r2 = 2;
            break;
        }
        if cond {
            *m2 = 2;
            break;
        }
        n -= 1;
    }
    *s
}

/// Follow-up 2 to Bug 4: `eval_switch_with_join` must also run `reduce_ctx` on
/// `joined_ctx` so `src_ctx` and `tgt_ctx` reduce `'static` shared-borrow
/// abstractions symmetrically during `match_ctx_with_target`.
pub fn bug4_if_two_static_shared_borrows(b: bool, x: &'static u32, y: &'static u32) -> u32 {
    if b {
        take_static(x);
        take_two_static(x, y);
    }
    nop();
    *x
}

/// Bug 5: Broken `AProjBorrows` / `Proj` handling in `eliminate_shared_borrow_markers`
/// (`RegionSet.empty` instead of `abs.regions.owned` and `ty_get_ref` on an ADT)
/// and `add_shared_borrows` (normalizing with `abs.regions.owned` instead of `regions'`).
pub fn bug5_symbolic_proj_shared_borrow(b: bool, x: &'static u32, o: OptRef<'static>) -> u32 {
    if b {
        consume_opt(o);
    } else {
        let _moved = o;
    }
    nop();
    *x
}
