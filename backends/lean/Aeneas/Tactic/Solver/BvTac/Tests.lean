import Aeneas.Tactic.Solver.BvTac.BvTac

/-! # BvTac regression tests -/

open Aeneas Aeneas.Std

namespace BvTac.Tests

example (a b : U32) (ha : a.val < 3329) (hb : b.val < 3329)
    (res : U32) (hres : res = core.num.U32.wrapping_sub a b)
    (i : U32) (hi2 : i.bv = res.bv >>> 16)
    (hdisj : (decide (i = 0#u32) || decide (i = 65535#u32)) = true)
    (i1 : U32) (hi1_2 : i1.bv = (3329 : BitVec 32) &&& i.bv)
    (res1 : U32) (hres1 : res1 = core.num.U32.wrapping_add res i1) :
    res1 < 3329#u32 := by
  bv_tac 32

end BvTac.Tests
