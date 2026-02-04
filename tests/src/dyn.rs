//@ [!lean] skip

trait Trait { fn get(&self) -> u32; }

impl Trait for u32 {
    fn get(&self) -> u32 {
        *self
    }
}

impl Trait for bool {
    fn get(&self) -> u32 {
        *self as u32
    }
}

fn bool_to_trait(b : bool) -> impl Trait {
    b
}

fn mk_trait(b : bool) -> Box<dyn Trait> {
    if b {
        Box::new(b)
    }
    else {
        Box::new(0)
    }
}


trait Into<T> {
    fn into(self) -> T;
}

// Checking that nothing wrong happens when mixing type variable indices
fn mk_into<U, V, T : Into<V> + 'static, W : Into<V> + 'static>(b : bool, x : T, y : W) -> Box<dyn Into<V>> {
    if b {
        Box::new(x)
    }
    else {
        Box::new(y)
    }
}
