module

public import Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u

/- The translation's memory effect needs a fixed instrumented representation type.
Assume one relational byte layout at each required universe. The fields of `Layout`
state byte-permission coherence, local update existence/framing, and typed invalidation.
No concrete instrumentation or universal finite-byte codec is assumed by generic proofs. -/
axiom layout : Layout.{u}

end Aeneas.Std
