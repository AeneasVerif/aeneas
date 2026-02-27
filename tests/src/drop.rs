//@ [!lean] skip

fn fill<T>(s: &mut [T], value: T)
where
    T: Clone,
{
    for i in 0..s.len() {
        s[i] = value.clone();
    }
}
