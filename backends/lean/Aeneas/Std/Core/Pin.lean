import Aeneas.Extract

namespace Aeneas.Std

-- TODO: make general
@[rust_type "core::pin::Pin"]
structure core.pin.Pin (Ptr : Type) where
  pointer : Ptr

-- TODO
@[rust_type "core::pin::helper::PinHelper"]
axiom core.pin.helper.PinHelper (Ptr : Type) : Type

end Aeneas.Std
