import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.Std.StringDef

/-! # Compilation Target and Target Features

    Models of the compilation target and of the target features which are
    available on the machine executing the code. -/

namespace Aeneas.Std

/-- Returns the compilation target as a string.

    Used by multi-target dispatch: nothing meaningful can be deduced from
    its output. -/
axiom get_target : RustM Str

@[step]
axiom get_target.spec : get_target ⦃ fun _ => True ⦄

/-- `target_feature_enabled feat` is `true` if the target feature `feat` (for
    instance `"avx2"`) is available on the machine executing the code.

    Introduced by the `-feature-gates` option: the functions annotated with
    `#[target_feature(enable = "feat")]` assert `target_feature_enabled "feat"` at
    the beginning of their body. -/
axiom target_feature_enabled : Str → Bool

end Aeneas.Std
