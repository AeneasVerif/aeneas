module
public meta import Aeneas.Extract.Extract
public import Aeneas.Std.Primitives
public section

namespace Aeneas.Std

/-- Model of `core::pin::Pin` (<https://doc.rust-lang.org/std/pin/struct.Pin.html>).

    `Pin<Ptr>` is a transparent wrapper around a pointer: pinning restricts which
    operations are *allowed* on the pointee (it must not be moved out), it does not change
    their result. We therefore model it by a one-field structure, exactly like its Rust
    definition. As Aeneas translates `&mut T` to `T`, `Pin<&mut T>` is translated to `Pin T`.

    The constructors and accessors of `Pin` are not modelled by functions: Aeneas rewrites
    their calls to the corresponding aggregates and field accesses (see the pre-pass
    `simplify_pin_calls`), because their generic definition cannot be given a model which
    type-checks when `Ptr` is instantiated with a mutable reference (see
    <https://github.com/AeneasVerif/aeneas/issues/1215>). -/
@[rust_type "core::pin::Pin"]
structure core.pin.Pin (Ptr : Type _) where
  pointer : Ptr

-- TODO
@[rust_type "core::pin::helper::PinHelper"]
axiom core.pin.helper.PinHelper (Ptr : Type _) : Type

/-- The helper trait of `impl DerefMut for Pin<Ptr>` (which is unused: the calls to `deref_mut`
    are rewritten, see above). Modelling it prevents Aeneas from generating it in every crate
    which uses `Pin`. -/
@[rust_trait "core::pin::helper::PinDerefMutHelper"]
structure core.pin.helper.PinDerefMutHelper (Self : Type _) (Self_Target : Type _) where
  deref_mut : Self → Result (Self_Target × (Self_Target → Self))

end Aeneas.Std
