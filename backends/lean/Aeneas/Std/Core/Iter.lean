import Aeneas.Std.Core.Cmp
import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

@[rust_trait "core::iter::range::Step"
  (parentClauses := ["cloneCloneInst", "cmpPartialOrdInst"])]
structure core.iter.range.Step (Self : Type) where
  cloneCloneInst : core.clone.Clone Self
  cmpPartialOrdInst : core.cmp.PartialOrd Self Self
  steps_between : Self → Self → Result (Usize × (Option Usize))
  forward_checked : Self → Usize → Result (Option Self)
  backward_checked : Self → Usize → Result (Option Self)
