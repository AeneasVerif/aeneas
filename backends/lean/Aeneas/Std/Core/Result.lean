import Aeneas.Extract

namespace Aeneas.Std

@[rust_type "core::result::Result"]
inductive core.result.Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

end Aeneas.Std
