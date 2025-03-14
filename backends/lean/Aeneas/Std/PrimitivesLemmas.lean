import Aeneas.Std.Primitives
import Aeneas.Progress.Init
import Aeneas.Bvify.Init

namespace Aeneas.Std

open Result

@[progress]
theorem massert_spec (b : Bool) (h : b) :
  massert b = ok () := by
  simp [massert, *]

@[progress]
theorem massert_decide_spec (b : Prop) [Decidable b] (h : b) :
  massert (decide b) = ok () := by
  simp [massert, *]

@[simp, progress_pre_simps, bvify_simps]
theorem massert_ok (b : Bool) : massert b = ok () ↔ b := by simp [massert]

@[simp, global_simps] theorem massert_true : massert true = ok () := by simp [massert]
@[simp, global_simps] theorem massert_false : massert false = fail .assertionFailure := by simp [massert]

end Aeneas.Std
