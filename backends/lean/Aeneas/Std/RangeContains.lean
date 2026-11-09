module
public import Aeneas.Std.Range
public import Aeneas.Std.Core.Cmp
public meta import Aeneas.Extract.Extract
@[expose] public section

namespace Aeneas.Std

open Result

/-- `RangeInclusive::contains`: `start <= item` and `item <= end` (or `item < end` once the range
is exhausted, as its end bound is then excluded). -/
@[rust_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains"]
def core.ops.range.RangeInclusive.contains {Idx U : Type _}
    (_cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (r : SharedBorrow (core.ops.range.RangeInclusive Idx)) (item : SharedBorrow U) :
    Result Bool := do
  if ← cmpPartialOrdInst1.le (SharedBorrow.mk r.val.start) item then
    if r.val.exhausted then cmpPartialOrdInst2.lt item (SharedBorrow.mk r.val.«end»)
    else cmpPartialOrdInst2.le item (SharedBorrow.mk r.val.«end»)
  else ok false

end Aeneas.Std
