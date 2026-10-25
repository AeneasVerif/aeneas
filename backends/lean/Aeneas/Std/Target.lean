module
public import Aeneas.Std.Scalar

/-! # Compilation Target and Target Features

    Models of the compilation target and of the target features which are
    available on the machine executing the code. -/

public section

namespace Aeneas.Std
open Result

/-- Returns the compilation target (e.g., `"x86_64-unknown-linux-gnu"`) as a
    Lean `String`.

    Used by multi-target dispatch: nothing meaningful can be deduced from
    its output. -/
noncomputable opaque target : String

noncomputable def get_target : Result String := ok target

@[step]
theorem get_target.spec : get_target ⦃ fun _ => True ⦄ := by simp [get_target]

/-- `target_feature_enabled feat` is `true` if the target feature `feat` (for
    instance `"avx2"`) is available on the machine executing the code.

    Introduced by the `-feature-gates` option: the functions annotated with
    `#[target_feature(enable = "feat")]` assert `target_feature_enabled "feat"` at
    the beginning of their body. -/
noncomputable opaque target_feature_enabled : String → Bool

end Aeneas.Std
