import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Std.Core.Default
import Aeneas.Std.Scalar.Notations

namespace Aeneas.Std

open Result ScalarElab

/- [core::default::{core::default::Default for u32}::default]:
   Source: '/rustc/library/core/src/default.rs', lines 156:12-156:30
   Name pattern: [core::default::{core::default::Default<u32>}::default] -/
uscalar @[simp, scalar_tac_simps] def core.default.Default'S.default : «%S» := ⟨ 0, by scalar_tac ⟩
iscalar @[simp, scalar_tac_simps] def core.default.Default'S.default : «%S» := ⟨ 0, by scalar_tac ⟩

/- Trait implementation: [core::default::{core::default::Default for u32}#7]
   Source: '/rustc/library/core/src/default.rs', lines 153:8-153:27
   Name pattern: [core::default::Default<u32>] -/
scalar @[reducible] def core.default.Default'S : core.default.Default «%S» := {
  default := ok core.default.Default'S.default }

end Aeneas.Std
