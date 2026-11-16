/- `core::any` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

/-- Model of `TypeId` (<https://doc.rust-lang.org/std/any/struct.TypeId.html>): opaque. -/
@[rust_type "core::any::TypeId"]
structure core.any.TypeId where
  id : Nat

/-- `core::any::Any` (<https://doc.rust-lang.org/std/any/trait.Any.html>). `Dyn Any` is the type of
`Box<dyn Any + Send>`, the payload of a panic in `JoinHandle::join`. -/
@[rust_trait "core::any::Any"]
structure core.any.Any (Self : Type _) where
  type_id : Self → Result core.any.TypeId

/-- Model of `<dyn Any as Debug>::fmt`, which prints `Any { .. }`. As for the other `Debug`
models, nothing is printed. -/
@[expose, rust_fun "core::any::{core::fmt::Debug<@>}::fmt"]
def core.any.DebugDynAny.fmt :
    Dyn.{0, 0} (fun (_dyn : Type) => core.any.Any _dyn) → core.fmt.Formatter →
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

end Aeneas.Std
