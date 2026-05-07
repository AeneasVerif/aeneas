import Aeneas.Tactic.Solver.BvTac.BvTac

/-! # BvTac regression tests -/

open Aeneas Aeneas.Std

namespace BvTac.Tests

example (a b res i i1 res1 : U32)
    (ha : a.bv < 3329#32) (hb : b.bv < 3329#32)
    (hres : res.bv = a.bv - b.bv)
    (hi : i.bv = res.bv >>> 16)
    (hdisj : (decide (i = 0#u32) || decide (i = 65535#u32)) = true)
    (hi1 : i1.bv = 3329#32 &&& i.bv)
    (hres1 : res1.bv = res.bv + i1.bv) :
    res1.bv < 3329#32 := by
  bv_tac 32

end BvTac.Tests
