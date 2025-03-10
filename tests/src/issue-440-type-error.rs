//@ [!lean] skip

enum PeanoNum {
    Zero,
    Succ(Box<PeanoNum>),
}

fn f(x: &mut PeanoNum, value: isize) {
    match x {
        PeanoNum::Zero => {
            std::mem::replace(x, PeanoNum::Succ(Box::new(PeanoNum::Zero)));
        }
        PeanoNum::Succ { .. } => {}
    }
}
