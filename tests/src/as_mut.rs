//@ [!lean] skip
fn use_box_as_mut<T>(mut x: &mut Box<T>) -> &mut T {
    x.as_mut()
}

fn use_as_mut<S, T: core::convert::AsMut<S>>(mut x: &mut T) -> &mut S {
    x.as_mut()
}
