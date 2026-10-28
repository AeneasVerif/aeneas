module

public import Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u

/- The translation's memory effect needs a fixed representation type. Assume one model at
each required universe, including the round-trip, cross-view read/write, and fresh-storage
laws in `Layout`.
A future bytes-and-alignment implementation must discharge these laws; none of its layout
choices are assumptions of the parametric heap operations or their proofs. -/
axiom layout : Layout.{u}

end Aeneas.Std
