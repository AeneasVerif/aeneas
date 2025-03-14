/- Arrays/Slices -/
import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

/-!
# Notations for `List`
-/
instance {α : Type u} : GetElem (List α) Usize α (fun l i => i.val < l.length) where
  getElem l i h := getElem l i.val h

instance {α : Type u} : GetElem? (List α) Usize α (fun l i => i < l.length) where
  getElem? l i := getElem? l i.val

end Aeneas.Std
