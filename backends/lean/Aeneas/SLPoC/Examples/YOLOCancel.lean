import Aeneas.SLPoC.SLTactics

/-!
# Downscaled YOLO synthetic cancellation benchmarks

The upstream `verse-lab/yolo` artifact at commit
`c127d4205a1594d9398dd4a115a444eca0a56d2f` benchmarks shuffled entailments with 100 through 800 opaque atoms.
Those sizes currently exhaust impractical amounts of memory in `sl_frame`, so
this file uses 10 through 40 atoms.  Each case filters the exact `cancel100.lean`
left- and right-hand permutations to `H1` through `Hn`, preserving their
relative order.

Run safely from `backends/lean` with a three-GiB Lean heap and one worker:

```
lake env lean -M3072 -j1 Aeneas/SLPoC/Examples/YOLOCancel.lean
```

`-M` is in MiB.  `trace.profiler` reports declaration and `sl_frame` time.
-/

namespace Aeneas.SLPoC.YOLOCancel

open scoped SepLogic

set_option maxRecDepth 100000
set_option maxHeartbeats 600000

set_option trace.profiler true in
theorem q10 (H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 : SLProp) :
  H2 ∗ H1 ∗ H5 ∗ H6 ∗ H8 ∗ H4 ∗ H10 ∗ H7 ∗ H9 ∗ H3
  ⊢
  H7 ∗ H1 ∗ H4 ∗ H9 ∗ H2 ∗ H10 ∗ H3 ∗ H8 ∗ H6 ∗ H5 := by
  sl_frame

set_option trace.profiler true in
theorem q20 (H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 : SLProp) :
  H2 ∗ H1 ∗ H5 ∗ H12 ∗ H20 ∗ H6 ∗ H14 ∗ H8 ∗ H11 ∗ H4 ∗
  H17 ∗ H19 ∗ H13 ∗ H10 ∗ H18 ∗ H7 ∗ H16 ∗ H9 ∗ H3 ∗ H15
  ⊢
  H7 ∗ H15 ∗ H17 ∗ H1 ∗ H12 ∗ H16 ∗ H18 ∗ H4 ∗ H19 ∗ H9 ∗
  H14 ∗ H2 ∗ H10 ∗ H3 ∗ H13 ∗ H20 ∗ H8 ∗ H11 ∗ H6 ∗ H5 := by
  sl_frame

set_option trace.profiler true in
theorem q30 (H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 : SLProp) :
  H22 ∗ H2 ∗ H1 ∗ H5 ∗ H12 ∗ H25 ∗ H20 ∗ H6 ∗ H14 ∗ H8 ∗
  H11 ∗ H27 ∗ H4 ∗ H26 ∗ H17 ∗ H19 ∗ H13 ∗ H10 ∗ H18 ∗ H28 ∗
  H23 ∗ H7 ∗ H30 ∗ H16 ∗ H9 ∗ H3 ∗ H15 ∗ H29 ∗ H21 ∗ H24
  ⊢
  H7 ∗ H15 ∗ H22 ∗ H21 ∗ H25 ∗ H17 ∗ H1 ∗ H24 ∗ H12 ∗ H16 ∗
  H30 ∗ H18 ∗ H26 ∗ H4 ∗ H19 ∗ H9 ∗ H14 ∗ H2 ∗ H27 ∗ H28 ∗
  H10 ∗ H3 ∗ H23 ∗ H13 ∗ H20 ∗ H29 ∗ H8 ∗ H11 ∗ H6 ∗ H5 := by
  sl_frame

set_option trace.profiler true in
theorem q40 (H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 : SLProp) :
  H22 ∗ H37 ∗ H2 ∗ H1 ∗ H34 ∗ H5 ∗ H12 ∗ H40 ∗ H39 ∗ H25 ∗
  H20 ∗ H38 ∗ H6 ∗ H14 ∗ H8 ∗ H11 ∗ H27 ∗ H4 ∗ H26 ∗ H17 ∗
  H19 ∗ H13 ∗ H10 ∗ H18 ∗ H28 ∗ H32 ∗ H23 ∗ H7 ∗ H30 ∗ H16 ∗
  H36 ∗ H9 ∗ H3 ∗ H33 ∗ H15 ∗ H29 ∗ H35 ∗ H21 ∗ H24 ∗ H31
  ⊢
  H35 ∗ H7 ∗ H15 ∗ H22 ∗ H37 ∗ H21 ∗ H25 ∗ H31 ∗ H32 ∗ H36 ∗
  H17 ∗ H1 ∗ H40 ∗ H34 ∗ H39 ∗ H24 ∗ H12 ∗ H16 ∗ H30 ∗ H18 ∗
  H26 ∗ H4 ∗ H19 ∗ H9 ∗ H14 ∗ H2 ∗ H27 ∗ H28 ∗ H10 ∗ H3 ∗
  H23 ∗ H13 ∗ H20 ∗ H33 ∗ H38 ∗ H29 ∗ H8 ∗ H11 ∗ H6 ∗ H5 := by
  sl_frame

end Aeneas.SLPoC.YOLOCancel
