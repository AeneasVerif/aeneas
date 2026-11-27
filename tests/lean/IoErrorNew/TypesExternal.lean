module
public import Aeneas
@[expose] public section

namespace Aeneas.Std

/-- This test observes whether construction succeeds, so the error payload is abstracted. -/
@[rust_type "core::io::error::Error"]
def core.io.error.Error : Type := Unit

end Aeneas.Std
