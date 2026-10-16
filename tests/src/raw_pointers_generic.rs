//@ [!lean] skip

fn generic_ptr<T>(data: &[T]) -> *const T {
    data.as_ptr()
}

fn generic_mut_ptr<T>(data: &mut [T]) -> *mut T {
    data.as_mut_ptr()
}

fn bool_ptr(data: &[bool]) -> *const bool {
    data.as_ptr()
}

fn bool_mut_ptr(data: &mut [bool]) -> *mut bool {
    data.as_mut_ptr()
}

/// The implementation of `FnOnce` for the closure reads through a raw pointer:
/// it receives the `Pointee` instance of `T`.
fn read_opt<T: Copy>(p: Option<*const T>) -> Option<T> {
    p.map(|p| unsafe { *p })
}

/// The method implementations read through raw pointers to the type parameters
/// of the method: they receive their `Pointee` instances.
trait ReadAt {
    fn read_at<T: Copy>(&self, p: *const T) -> T;
}

struct Reader;

impl ReadAt for Reader {
    fn read_at<T: Copy>(&self, p: *const T) -> T {
        unsafe { *p }
    }
}

fn read_with<R: ReadAt, T: Copy>(r: &R, p: *const T) -> T {
    r.read_at(p)
}
