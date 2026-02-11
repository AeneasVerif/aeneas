//@ [!lean] skip

trait From<T> {
    fn from(x: T) -> Self;
}

trait To {
    fn to<T: From<Self>>(&self) -> T
    where
        Self: std::marker::Sized;
}

impl From<u32> for u32 {
    fn from(x: u32) -> u32 {
        x
    }
}

impl To for u32 {
    fn to<T: From<Self>>(&self) -> T {
        <T as From<Self>>::from(*self)
    }
}
