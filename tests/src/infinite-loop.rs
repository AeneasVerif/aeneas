//@ [coq,fstar,lean] skip
//@ [coq,fstar] aeneas-args=-use-fuel
//@ [coq,fstar] subdir=misc
// FIXME: make it work
fn bar() {}

fn foo() {
    loop {
        bar()
    }
}
