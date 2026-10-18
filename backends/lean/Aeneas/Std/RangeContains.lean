module
public import Aeneas.Std.Range
public import Aeneas.Std.Core.Cmp
public meta import Aeneas.Extract.Extract
@[expose] public section

namespace Aeneas.Std

open Result

/-- `RangeInclusive::contains`: `start <= item` and `item <= end` (or
`item < end` once the range is exhausted, as its end bound is then
excluded). -/
@[rust_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains"]
def core.ops.range.RangeInclusive.contains {Idx U : Type}
    (_cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (item : U) : Result Bool := do
  if ← cmpPartialOrdInst1.le r.start item then
    if r.exhausted then cmpPartialOrdInst2.lt item r.«end»
    else cmpPartialOrdInst2.le item r.«end»
  else ok false

end Aeneas.Std
