import Aeneas.Std.Primitives
import Aeneas.Progress.Core

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

end Aeneas.Std
