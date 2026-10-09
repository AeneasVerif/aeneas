module
public meta import Aeneas.Extract.Extract
public section

namespace Aeneas.Std

-- TODO
@[rust_type "core::pin::Pin"]
axiom core.pin.Pin (Ptr : Type _) : Type

-- TODO
@[rust_type "core::pin::helper::PinHelper"]
axiom core.pin.helper.PinHelper (Ptr : Type _) : Type

end Aeneas.Std
