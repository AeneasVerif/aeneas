# Ideal separation-logic proof score

Regenerate with `lake env lean --run Aeneas/SLPoC/ProofScore.lean` from `backends/lean`.  A *spot* is one straight-line block of a proof: the block before the first branch, then one per branch body, recursively.  A spot is ideal when it steers the separation logic nowhere by hand — only `sl_step`, `sl_pull`, and pure reasoning.  See the module docstring of `Aeneas/SLPoC/ProofScore.lean` for the details.

## Rules

- free: `sl_step`, `sl_pull`, pure reasoning, and `unfold` of a program;
- manual: `sl_frame`, `sl_frame?`, `sl_xsimpl`, `sl_xpull`, `sl_xchange`, `sl_xapp`, `sl_xval`, `sl_conseq`, `sl_pull_step`, `sl_pull_keep`, `sl_pull_keep_step`, `sl_side?`, `step`, `step*`;
- manual: any other step mentioning a separation-logic connective (`∗`, `∗+`, `↦`, `⊢`, `⊢+`, `⊣⊢`, `-∗`, `-∗+`, `iprop(`, `⌜`, `⌝`, `emp`, `GC`, `∀ˢ`, `⦃`, `⦄`), a simp set of the automation (`sl_simps`, `step_simps`, `step_post_simps`), or a declaration whose statement is about `SLProp`.

## Summary

| File | Triples | Ideal proofs | Spots | Ideal spots | Score |
|---|---:|---:|---:|---:|---:|
| `Aeneas/SLPoC/Examples/Basic.lean` | 9 | 9 | 9 | 9 | 100.0% |
| `Aeneas/SLPoC/Examples/EqOrDisj.lean` | 4 | 0 | 4 | 0 | 0.0% |
| `Aeneas/SLPoC/Examples/IrisTutorial.lean` | 20 | 13 | 48 | 27 | 56.3% |
| `Aeneas/SLPoC/Examples/UnitTest.lean` | 25 | 18 | 28 | 20 | 71.4% |
| `Aeneas/SLPoC/Examples/VerusDoublyLinkedList.lean` | 13 | 12 | 23 | 22 | 95.7% |
| `Aeneas/SLPoC/Examples/VerusStd.lean` | 1 | 0 | 1 | 0 | 0.0% |
| **Total** | **72** | **52** | **113** | **78** | **69.0%** |

## `Aeneas/SLPoC/Examples/Basic.lean`

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `add1.spec` | 13 | 1 | 1 | 100.0% |
| `add2.spec` | 22 | 1 | 1 | 100.0% |
| `incr_ptr.spec` | 32 | 1 | 1 | 100.0% |
| `incr_borrow.spec` | 43 | 1 | 1 | 100.0% |
| `«example@50»` | 50 | 1 | 1 | 100.0% |
| `«example@54»` | 54 | 1 | 1 | 100.0% |
| `«example@58»` | 58 | 1 | 1 | 100.0% |
| `«example@64»` | 64 | 1 | 1 | 100.0% |
| `«example@73»` | 73 | 1 | 1 | 100.0% |
| **Total** | | **9** | **9** | **100.0%** |

9 of 9 proofs are ideal throughout.

### Proofs, spot by spot

#### `add1.spec` (line 13) — 1/1 spots ideal

Spot at line 15 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 15 | `unfold add1` | ideal |
| 16 | `sl_step*` | ideal |

#### `add2.spec` (line 22) — 1/1 spots ideal

Spot at line 24 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 24 | `unfold add2` | ideal |
| 25 | `sl_step*` | ideal |

#### `incr_ptr.spec` (line 32) — 1/1 spots ideal

Spot at line 34 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 34 | `unfold incr_ptr` | ideal |
| 35 | `sl_step*` | ideal |

#### `incr_borrow.spec` (line 43) — 1/1 spots ideal

Spot at line 45 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 45 | `unfold incr_borrow` | ideal |
| 46 | `sl_step*` | ideal |

#### `«example@50»` (line 50) — 1/1 spots ideal

Spot at line 52 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 52 | `sl_step*` | ideal |

#### `«example@54»` (line 54) — 1/1 spots ideal

Spot at line 56 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 56 | `sl_step*` | ideal |

#### `«example@58»` (line 58) — 1/1 spots ideal

Spot at line 62 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 62 | `sl_step*` | ideal |

#### `«example@64»` (line 64) — 1/1 spots ideal

Spot at line 68 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 68 | `sl_step*` | ideal |

#### `«example@73»` (line 73) — 1/1 spots ideal

Spot at line 76 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 76 | `unfold conditionalUpdate` | ideal |
| 77 | `sl_step*` | ideal |

## `Aeneas/SLPoC/Examples/EqOrDisj.lean`

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `read.spec'` | 31 | 1 | 0 | 0.0% |
| `update.spec'` | 40 | 1 | 0 | 0.0% |
| `«example@50»` | 50 | 1 | 0 | 0.0% |
| `«example@60»` | 60 | 1 | 0 | 0.0% |
| **Total** | | **4** | **0** | **0.0%** |

0 of 4 proofs are ideal throughout.

### Proofs, spot by spot

#### `read.spec'` (line 31) — 0/1 spots ideal

Spot at line 36 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 36 | `cases relation` | ideal |
| 37 | `simp only [isEqOrDisj, EqOrDisj.read]` | **manual**: mentions the separation-logic declaration `isEqOrDisj` |
| 38 | `sl_step*` | ideal |

#### `update.spec'` (line 40) — 0/1 spots ideal

Spot at line 44 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 44 | `cases relation` | ideal |
| 45 | `simp only [isEqOrDisj, EqOrDisj.write]` | **manual**: mentions the separation-logic declaration `isEqOrDisj` |
| 46 | `sl_step*` | ideal |

#### `«example@50»` (line 50) — 0/1 spots ideal

Spot at line 56 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 56 | `cases relation` | ideal |
| 57 | `simp only [Examples.isEqOrDisj, Examples.EqOrDisj.read]` | **manual**: mentions the separation-logic declaration `Examples.isEqOrDisj` |
| 58 | `sl_step*` | ideal |

#### `«example@60»` (line 60) — 0/1 spots ideal

Spot at line 64 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 64 | `cases relation` | ideal |
| 65 | `simp only [Examples.isEqOrDisj, Examples.EqOrDisj.write]` | **manual**: mentions the separation-logic declaration `Examples.isEqOrDisj` |
| 66 | `sl_step*` | ideal |

## `Aeneas/SLPoC/Examples/IrisTutorial.lean`

⚠ 5 parse errors, listed at the end of this section: the file defines notation of its own and has not been built, so some of its declarations are missing here.

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `arith_spec` | 188 | 1 | 1 | 100.0% |
| `lambda_spec` | 200 | 1 | 1 | 100.0% |
| `prog_spec` | 212 | 1 | 1 | 100.0% |
| `compareAndSetSequential_spec` | 237 | 3 | 3 | 100.0% |
| `cmpXchg_0_to_10_sequential_spec` | 254 | 1 | 1 | 100.0% |
| `cas_sequential_spec` | 276 | 1 | 1 | 100.0% |
| `par_client_sequential_spec` | 290 | 1 | 0 | 0.0% |
| `race_left_then_right_sequential_spec` | 303 | 1 | 1 | 100.0% |
| `race_right_then_left_sequential_spec` | 313 | 1 | 1 | 100.0% |
| `prog_add_2_spec` | 323 | 1 | 1 | 100.0% |
| `prog_add_2_spec'` | 328 | 1 | 1 | 100.0% |
| `prog_add_2_spec''` | 334 | 1 | 0 | 0.0% |
| `swap_spec` | 349 | 1 | 1 | 100.0% |
| `swap_swap_spec` | 355 | 1 | 1 | 100.0% |
| `inc_spec` | 396 | 7 | 3 | 42.9% |
| `append_spec` | 430 | 7 | 3 | 42.9% |
| `reverse_append_spec` | 466 | 7 | 3 | 42.9% |
| `reverse_spec` | 495 | 1 | 1 | 100.0% |
| `fold_right_spec` | 522 | 7 | 3 | 42.9% |
| `sum_list_spec` | 554 | 3 | 0 | 0.0% |
| **Total** | | **48** | **27** | **56.3%** |

13 of 20 proofs are ideal throughout.

### Proofs, spot by spot

#### `arith_spec` (line 188) — 1/1 spots ideal

Spot at line 190 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 190 | `unfold arith` | ideal |
| 191 | `sl_step*` | ideal |

#### `lambda_spec` (line 200) — 1/1 spots ideal

Spot at line 202 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 202 | `unfold lambda` | ideal |
| 203 | `sl_step*` | ideal |

#### `prog_spec` (line 212) — 1/1 spots ideal

Spot at line 214 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 214 | `unfold prog` | ideal |
| 215 | `sl_step*` | ideal |

#### `compareAndSetSequential_spec` (line 237) — 3/3 spots ideal

Spot at line 243 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 243 | `unfold compareAndSetSequential` | ideal |
| 244 | `sl_step` | ideal |
| 245 | `by_cases h : value = expected` | ideal |
| 246 | `· simp only [h, ↓reduceIte, decide_true] …` | ideal |
| 248 | `· simp only [h, ↓reduceIte, decide_false] …` | ideal |

Spot at line 246 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 246 | `simp only [h, ↓reduceIte, decide_true]` | ideal |
| 247 | `sl_step*` | ideal |

Spot at line 248 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 248 | `simp only [h, ↓reduceIte, decide_false]` | ideal |
| 249 | `sl_step*` | ideal |

#### `cmpXchg_0_to_10_sequential_spec` (line 254) — 1/1 spots ideal

Spot at line 259 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 259 | `unfold cmpXchg0To10Sequential` | ideal |
| 260 | `sl_step*` | ideal |

#### `cas_sequential_spec` (line 276) — 1/1 spots ideal

Spot at line 278 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 278 | `unfold casSequential` | ideal |
| 279 | `sl_step*` | ideal |

#### `par_client_sequential_spec` (line 290) — 0/1 spots ideal

Spot at line 294 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 294 | `unfold parClientSequential` | ideal |
| 295 | `sl_step*` | ideal |
| 296 | `apply triple_pure` | **manual**: mentions the separation-logic declaration `triple_pure` |
| 297 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

#### `race_left_then_right_sequential_spec` (line 303) — 1/1 spots ideal

Spot at line 306 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 306 | `unfold raceLeftThenRightSequential` | ideal |
| 307 | `sl_step*` | ideal |

#### `race_right_then_left_sequential_spec` (line 313) — 1/1 spots ideal

Spot at line 316 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 316 | `unfold raceRightThenLeftSequential` | ideal |
| 317 | `sl_step*` | ideal |

#### `prog_add_2_spec` (line 323) — 1/1 spots ideal

Spot at line 325 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 325 | `unfold progAdd2` | ideal |
| 326 | `sl_step*` | ideal |

#### `prog_add_2_spec'` (line 328) — 1/1 spots ideal

Spot at line 330 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 330 | `unfold progAdd2` | ideal |
| 331 | `sl_step with prog_spec` | ideal |
| 332 | `sl_step*` | ideal |

#### `prog_add_2_spec''` (line 334) — 0/1 spots ideal

Spot at line 334 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 335 | `:= …` | **manual**: mentions the separation-logic declaration `prog_add_2_spec'` |

#### `swap_spec` (line 349) — 1/1 spots ideal

Spot at line 352 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 352 | `unfold swap` | ideal |
| 353 | `sl_step*` | ideal |

#### `swap_swap_spec` (line 355) — 1/1 spots ideal

Spot at line 358 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 358 | `unfold swapTwice` | ideal |
| 359 | `sl_step*` | ideal |

#### `inc_spec` (line 396) — 3/7 spots ideal

Spot at line 399 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 399 | `induction xs generalizing l with …` | ideal |

Spot at line 401 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 401 | `cases l` | ideal |
| 402 | `· simp only [isList, inc, List.map_nil] …` | ideal |
| 404 | `· simp only [isList] …` | ideal |

Spot at line 402 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 402 | `simp only [isList, inc, List.map_nil]` | **manual**: mentions the separation-logic declaration `isList` |
| 403 | `sl_step*` | ideal |

Spot at line 404 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 404 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 405 | `sl_pull` | ideal |
| 406 | `contradiction` | ideal |

Spot at line 408 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 408 | `cases l with …` | ideal |

Spot at line 410 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 410 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 411 | `sl_pull` | ideal |
| 412 | `contradiction` | ideal |

Spot at line 414 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 414 | `simp only [isList, inc, List.map_cons]` | **manual**: mentions the separation-logic declaration `isList` |
| 415 | `sl_pull next` | ideal |
| 416 | `sl_step` | ideal |
| 417 | `sl_step` | ideal |
| 418 | `sl_step with ih next` | ideal |

#### `append_spec` (line 430) — 3/7 spots ideal

Spot at line 433 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 433 | `induction xs generalizing l₁ l₂ ys with …` | ideal |

Spot at line 435 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 435 | `cases l₁` | ideal |
| 436 | `· simp only [isList, append, List.nil_append] …` | ideal |
| 439 | `· simp only [isList] …` | ideal |

Spot at line 436 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 436 | `simp only [isList, append, List.nil_append]` | **manual**: mentions the separation-logic declaration `isList` |
| 437 | `apply triple_pure` | **manual**: mentions the separation-logic declaration `triple_pure` |
| 438 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

Spot at line 439 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 439 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 440 | `sl_pull` | ideal |
| 441 | `contradiction` | ideal |

Spot at line 443 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 443 | `cases l₁ with …` | ideal |

Spot at line 445 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 445 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 446 | `sl_pull` | ideal |
| 447 | `contradiction` | ideal |

Spot at line 449 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 449 | `simp only [isList, append, List.cons_append]` | **manual**: mentions the separation-logic declaration `isList` |
| 450 | `sl_pull next` | ideal |
| 451 | `sl_step` | ideal |
| 452 | `sl_step with ih (l₁ := next) (l₂ := l₂) (ys := ys)` | ideal |
| 453 | `sl_step` | ideal |
| 454 | `apply triple_pure` | **manual**: mentions the separation-logic declaration `triple_pure` |
| 455 | `exact isList_cons p x result (xs ++ ys)` | **manual**: mentions the separation-logic declaration `isList_cons` |

#### `reverse_append_spec` (line 466) — 3/7 spots ideal

Spot at line 469 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 469 | `induction xs generalizing l acc ys with …` | ideal |

Spot at line 471 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 471 | `cases l` | ideal |
| 472 | `· simp only [isList, reverseAppend, List.reverse_nil, List.nil_append] …` | ideal |
| 475 | `· simp only [isList] …` | ideal |

Spot at line 472 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 472 | `simp only [isList, reverseAppend, List.reverse_nil, List.nil_append]` | **manual**: mentions the separation-logic declaration `isList` |
| 473 | `apply triple_pure` | **manual**: mentions the separation-logic declaration `triple_pure` |
| 474 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

Spot at line 475 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 475 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 476 | `sl_pull` | ideal |
| 477 | `contradiction` | ideal |

Spot at line 479 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 479 | `cases l with …` | ideal |

Spot at line 481 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 481 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 482 | `sl_pull` | ideal |
| 483 | `contradiction` | ideal |

Spot at line 485 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 485 | `simp only [isList, reverseAppend, List.reverse_cons, List.append_assoc, …` | **manual**: mentions the separation-logic declaration `isList` |
| 487 | `sl_pull next` | ideal |
| 488 | `sl_step` | ideal |
| 489 | `sl_step` | ideal |
| 490 | `sl_step with ih (l := next) (acc := some p) (ys := x :: ys)` | ideal |

#### `reverse_spec` (line 495) — 1/1 spots ideal

Spot at line 498 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 498 | `unfold reverse` | ideal |
| 499 | `sl_step with reverse_append_spec l none xs []` | ideal |

#### `fold_right_spec` (line 522) — 3/7 spots ideal

Spot at line 529 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 529 | `induction xs generalizing l acc with …` | ideal |

Spot at line 531 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 531 | `cases l` | ideal |
| 532 | `· simp only [isList, bigSep, foldRight] …` | ideal |
| 535 | `· simp only [isList] …` | ideal |

Spot at line 532 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 532 | `simp only [isList, bigSep, foldRight]` | **manual**: mentions the separation-logic declaration `isList` |
| 533 | `apply triple_pure` | **manual**: mentions the separation-logic declaration `triple_pure` |
| 534 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

Spot at line 535 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 535 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 536 | `sl_pull` | ideal |
| 537 | `contradiction` | ideal |

Spot at line 539 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 539 | `cases l with …` | ideal |

Spot at line 541 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 541 | `simp only [isList]` | **manual**: mentions the separation-logic declaration `isList` |
| 542 | `sl_pull` | ideal |
| 543 | `contradiction` | ideal |

Spot at line 545 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 545 | `simp only [isList, bigSep, foldRight]` | **manual**: mentions the separation-logic declaration `isList` |
| 546 | `sl_pull next` | ideal |
| 547 | `sl_step` | ideal |
| 548 | `sl_step with ih (l := next) (acc := acc)` | ideal |
| 549 | `sl_step with hf x` | ideal |

#### `sum_list_spec` (line 554) — 0/3 spots ideal

Spot at line 558 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 558 | `have hf : ∀ x acc ys, …` | **manual**: mentions the connective `⦃` |
| 565 | `unfold sumList` | ideal |
| 566 | `apply triple_conseq …` | **manual**: mentions the separation-logic declaration `triple_conseq` |
| 570 | `· simp only [bigSep_emp, hstar_hempty_l_eq] …` | ideal |
| 572 | `· intro result …` | ideal |

Spot at line 570 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 570 | `simp only [bigSep_emp, hstar_hempty_l_eq]` | **manual**: mentions the separation-logic declaration `bigSep_emp` |
| 571 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

Spot at line 572 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 572 | `intro result` | ideal |
| 573 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

### Parse errors

- 23:5: expected token
- 66:36: expected token
- 78:30: expected token
- 90:12: expected token
- 150:35: expected token

## `Aeneas/SLPoC/Examples/UnitTest.lean`

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `«example@47»` | 47 | 1 | 1 | 100.0% |
| `«example@54»` | 54 | 1 | 1 | 100.0% |
| `«example@70»` | 70 | 1 | 1 | 100.0% |
| `«example@77»` | 77 | 1 | 0 | 0.0% |
| `touchAny.spec` | 95 | 1 | 1 | 100.0% |
| `«example@108»` | 108 | 1 | 1 | 100.0% |
| `«example@115»` | 115 | 1 | 1 | 100.0% |
| `«example@123»` | 123 | 1 | 1 | 100.0% |
| `«example@142»` | 142 | 1 | 0 | 0.0% |
| `«example@158»` | 158 | 1 | 1 | 100.0% |
| `«example@178»` | 178 | 1 | 1 | 100.0% |
| `«example@184»` | 184 | 1 | 1 | 100.0% |
| `«example@219»` | 219 | 1 | 0 | 0.0% |
| `«example@226»` | 226 | 1 | 0 | 0.0% |
| `«example@231»` | 231 | 1 | 0 | 0.0% |
| `«example@240»` | 240 | 1 | 1 | 100.0% |
| `«example@247»` | 247 | 1 | 1 | 100.0% |
| `«example@255»` | 255 | 3 | 1 | 33.3% |
| `«example@275»` | 275 | 1 | 0 | 0.0% |
| `«example@286»` | 286 | 1 | 1 | 100.0% |
| `«example@293»` | 293 | 1 | 1 | 100.0% |
| `readTwice.spec` | 308 | 1 | 1 | 100.0% |
| `«example@315»` | 315 | 1 | 1 | 100.0% |
| `«example@320»` | 320 | 1 | 1 | 100.0% |
| `«example@325»` | 325 | 2 | 2 | 100.0% |
| **Total** | | **28** | **20** | **71.4%** |

18 of 25 proofs are ideal throughout.

### Proofs, spot by spot

#### `«example@47»` (line 47) — 1/1 spots ideal

Spot at line 49 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 49 | `unfold Examples.incr_ptr` | ideal |
| 50 | `sl_pull n rfl` | ideal |
| 51 | `sl_step*` | ideal |

#### `«example@54»` (line 54) — 1/1 spots ideal

Spot at line 56 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 56 | `unfold Examples.incr_ptr` | ideal |
| 57 | `sl_pull` | ideal |
| 58 | `subst_vars` | ideal |
| 59 | `sl_step*` | ideal |

#### `«example@70»` (line 70) — 1/1 spots ideal

Spot at line 72 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 72 | `unfold Examples.incr_ptr` | ideal |
| 73 | `sl_step*` | ideal |

#### `«example@77»` (line 77) — 0/1 spots ideal

Spot at line 79 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 79 | `sl_pull_keep` | **manual**: `sl_pull_keep` steers the separation logic by hand |
| 80 | `rename_i hn` | ideal |
| 81 | `exact triple_pure (by simp only [hn]; sl_frame)` | **manual**: mentions the separation-logic declaration `triple_pure` |

#### `touchAny.spec` (line 95) — 1/1 spots ideal

Spot at line 97 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 97 | `unfold touchAny` | ideal |
| 98 | `sl_pull n` | ideal |
| 99 | `sl_step*` | ideal |

#### `«example@108»` (line 108) — 1/1 spots ideal

Spot at line 110 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 110 | `unfold touchThenSet` | ideal |
| 111 | `sl_step*` | ideal |

#### `«example@115»` (line 115) — 1/1 spots ideal

Spot at line 118 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 118 | `unfold touchThenSet` | ideal |
| 119 | `sl_step*` | ideal |

#### `«example@123»` (line 123) — 1/1 spots ideal

Spot at line 125 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 125 | `unfold touchThenSet` | ideal |
| 126 | `sl_step*` | ideal |

#### `«example@142»` (line 142) — 0/1 spots ideal

Spot at line 144 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 144 | `unfold readThenWrite` | ideal |
| 145 | `sl_step` | ideal |
| 146 | `guard_target = …` | **manual**: mentions the separation-logic declaration `triple` |
| 148 | `sl_step*` | ideal |

#### `«example@158»` (line 158) — 1/1 spots ideal

Spot at line 160 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 160 | `unfold readAndFree` | ideal |
| 161 | `sl_step*` | ideal |

#### `«example@178»` (line 178) — 1/1 spots ideal

Spot at line 180 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 180 | `unfold allocAndForget` | ideal |
| 181 | `sl_step*` | ideal |

#### `«example@184»` (line 184) — 1/1 spots ideal

Spot at line 186 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 186 | `sl_step*` | ideal |

#### `«example@219»` (line 219) — 0/1 spots ideal

Spot at line 221 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 221 | `unfold Examples.incr_ptr` | ideal |
| 222 | `sl_xchange (swapEq p q)` | **manual**: `sl_xchange` steers the separation logic by hand |
| 223 | `sl_step*` | ideal |

#### `«example@226»` (line 226) — 0/1 spots ideal

Spot at line 227 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 227 | `sl_xval` | **manual**: `sl_xval` steers the separation logic by hand |
| 228 | `sl_xsimpl` | **manual**: `sl_xsimpl` steers the separation logic by hand |

#### `«example@231»` (line 231) — 0/1 spots ideal

Spot at line 233 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 233 | `sl_xapp (Examples.incr_ptr.spec p x)` | **manual**: `sl_xapp` steers the separation logic by hand |

#### `«example@240»` (line 240) — 1/1 spots ideal

Spot at line 242 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 242 | `sl_step` | ideal |

#### `«example@247»` (line 247) — 1/1 spots ideal

Spot at line 250 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 250 | `sl_step*` | ideal |

#### `«example@255»` (line 255) — 1/3 spots ideal

Spot at line 258 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 258 | `unfold touchThenSet` | ideal |
| 259 | `apply triple_step_bind (touchAny p) _ (touchAny.spec p)` | **manual**: mentions the separation-logic declaration `triple_step_bind` |
| 260 | `case hPre => …` | ideal |
| 263 | `case hNext => …` | ideal |

Spot at line 261 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 261 | `fail_if_success sl_xpull` | **manual**: mentions `sl_xpull` |
| 262 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

Spot at line 264 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 264 | `intro _ _` | ideal |
| 265 | `sl_pull` | ideal |
| 266 | `sl_step*` | ideal |

#### `«example@275»` (line 275) — 0/1 spots ideal

Spot at line 278 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 278 | `refine ⟨?_, ?_⟩` | ideal |
| 279 | `sl_step` | ideal |
| 280 | `sl_frame` | **manual**: `sl_frame` steers the separation logic by hand |

#### `«example@286»` (line 286) — 1/1 spots ideal

Spot at line 288 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 288 | `unfold touchThenSet` | ideal |
| 289 | `sl_step*` | ideal |

#### `«example@293»` (line 293) — 1/1 spots ideal

Spot at line 295 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 295 | `unfold touchAny` | ideal |
| 296 | `sl_pull n` | ideal |
| 297 | `sl_step with read.spec p n` | ideal |
| 298 | `sl_step*` | ideal |

#### `readTwice.spec` (line 308) — 1/1 spots ideal

Spot at line 310 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 310 | `unfold readTwice` | ideal |
| 311 | `sl_step*` | ideal |

#### `«example@315»` (line 315) — 1/1 spots ideal

Spot at line 316 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 316 | `sl_step*` | ideal |

#### `«example@320»` (line 320) — 1/1 spots ideal

Spot at line 322 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 322 | `sl_step*` | ideal |

#### `«example@325»` (line 325) — 2/2 spots ideal

Spot at line 327 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 327 | `sl_step* -grind` | ideal |
| 328 | `case hn => grind` | ideal |

Spot at line 328 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 328 | `grind` | ideal |

## `Aeneas/SLPoC/Examples/VerusDoublyLinkedList.lean`

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `new.spec` | 310 | 1 | 1 | 100.0% |
| `pushEmptyCase.spec` | 317 | 1 | 1 | 100.0% |
| `pushBack.spec` | 325 | 3 | 3 | 100.0% |
| `popBack.spec` | 344 | 1 | 1 | 100.0% |
| `pushFront.spec` | 356 | 5 | 5 | 100.0% |
| `popFront.spec` | 377 | 1 | 1 | 100.0% |
| `nodes_read` | 390 | 1 | 0 | 0.0% |
| `getLoop.spec` | 401 | 3 | 3 | 100.0% |
| `get.spec` | 419 | 1 | 1 | 100.0% |
| `new.spec` | 454 | 1 | 1 | 100.0% |
| `value.spec` | 463 | 1 | 1 | 100.0% |
| `moveNext.spec` | 477 | 3 | 3 | 100.0% |
| `run.spec` | 533 | 1 | 1 | 100.0% |
| **Total** | | **23** | **22** | **95.7%** |

12 of 13 proofs are ideal throughout.

### Proofs, spot by spot

#### `new.spec` (line 310) — 1/1 spots ideal

Spot at line 312 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 312 | `unfold new` | ideal |
| 313 | `sl_step*` | ideal |

#### `pushEmptyCase.spec` (line 317) — 1/1 spots ideal

Spot at line 320 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 320 | `unfold pushEmptyCase` | ideal |
| 321 | `sl_step*` | ideal |

#### `pushBack.spec` (line 325) — 3/3 spots ideal

Spot at line 328 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 328 | `unfold pushBack` | ideal |
| 329 | `split` | ideal |
| 330 | `next => …` | ideal |
| 334 | `next oldTailPtr _ => …` | ideal |

Spot at line 331 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 331 | `sl_pull` | ideal |
| 332 | `obtain rfl : l = [] := (lastPtr_eq_none_iff l).mp (by grind)` | ideal |
| 333 | `sl_step*` | ideal |

Spot at line 335 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 335 | `sl_pull` | ideal |
| 336 | `have hne : l ≠ [] := mt (lastPtr_eq_none_iff l).mpr (by grind)` | ideal |
| 337 | `obtain ⟨l', ⟨rt, vt⟩, rfl⟩ := (eq_nil_or_snoc l).resolve_left hne` | ideal |
| 338 | `obtain rfl : oldTailPtr = rt := by grind [lastPtr_snoc]` | ideal |
| 339 | `sl_step*` | ideal |

#### `popBack.spec` (line 344) — 1/1 spots ideal

Spot at line 347 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 347 | `obtain ⟨l', ⟨_, _⟩, rfl⟩ := (eq_nil_or_snoc l).resolve_left hne` | ideal |
| 348 | `rcases eq_nil_or_snoc l' with rfl \| ⟨_, ⟨_, _⟩, rfl⟩` | ideal |
| 349 | `unfold popBack` | ideal |
| 350 | `sl_pull ⟨_, htail⟩` | ideal |
| 351 | `simp only [lastPtr_snoc] at htail` | ideal |
| 352 | `sl_step*` | ideal |

#### `pushFront.spec` (line 356) — 5/5 spots ideal

Spot at line 359 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 359 | `unfold pushFront` | ideal |
| 360 | `split` | ideal |
| 361 | `next => …` | ideal |
| 365 | `next oldHeadPtr hsome => …` | ideal |

Spot at line 362 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 362 | `sl_pull` | ideal |
| 363 | `obtain rfl : l = [] := (firstPtr_eq_none_iff l).mp (by grind)` | ideal |
| 364 | `sl_step*` | ideal |

Spot at line 366 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 366 | `rcases l with _ \| ⟨⟨rh, _⟩, _⟩` | ideal |
| 367 | `· sl_pull ⟨hhead, _⟩ …` | ideal |
| 371 | `· sl_pull …` | ideal |

Spot at line 367 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 367 | `sl_pull ⟨hhead, _⟩` | ideal |
| 368 | `exfalso` | ideal |
| 369 | `change s.head = none at hhead` | ideal |
| 370 | `simp_all` | ideal |

Spot at line 371 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 371 | `sl_pull` | ideal |
| 372 | `obtain rfl : rh = oldHeadPtr := by grind` | ideal |
| 373 | `sl_step*` | ideal |

#### `popFront.spec` (line 377) — 1/1 spots ideal

Spot at line 381 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 381 | `unfold popFront` | ideal |
| 383 | `rcases l with _ \| ⟨⟨_, _⟩, _⟩` | ideal |
| 383 | `sl_step*` | ideal |

#### `nodes_read` (line 390) — 0/1 spots ideal

Spot at line 390 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 392 | `:= …` | **manual**: mentions the separation-logic declaration `cellsFrom_read` |

#### `getLoop.spec` (line 401) — 3/3 spots ideal

Spot at line 405 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 405 | `induction j, r using getLoop.induct (i := i) with …` | ideal |

Spot at line 407 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 407 | `rw [getLoop, if_pos hlt]` | ideal |
| 408 | `obtain ⟨rj, vj, hj⟩ := exists_cell l j (by omega)` | ideal |
| 409 | `obtain ⟨r', v', hj'⟩ := exists_cell l (j + 1) (by omega)` | ideal |
| 410 | `obtain rfl : r = rj := by grind` | ideal |
| 411 | `sl_step*` | ideal |

Spot at line 413 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 413 | `obtain rfl : j = i := by omega` | ideal |
| 414 | `rw [getLoop, if_neg hge]` | ideal |
| 415 | `sl_step*` | ideal |

#### `get.spec` (line 419) — 1/1 spots ideal

Spot at line 423 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 423 | `unfold get` | ideal |
| 424 | `sl_step as ⟨ r, _ ⟩` | ideal |
| 425 | `obtain ⟨ri, _, _⟩ := exists_cell l i hi` | ideal |
| 426 | `obtain rfl : r = ri := by grind` | ideal |
| 427 | `sl_step*` | ideal |

#### `new.spec` (line 454) — 1/1 spots ideal

Spot at line 457 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 457 | `unfold Iterator.new` | ideal |
| 458 | `simp only [valid]` | ideal |
| 459 | `sl_step*` | ideal |

#### `value.spec` (line 463) — 1/1 spots ideal

Spot at line 466 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 466 | `unfold Iterator.value` | ideal |
| 467 | `obtain ⟨hidx, hcur⟩ := hvalid` | ideal |
| 468 | `obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx` | ideal |
| 469 | `simp only [show it.cur = some r from by grind, get!_some]` | ideal |
| 470 | `sl_step*` | ideal |

#### `moveNext.spec` (line 477) — 3/3 spots ideal

Spot at line 486 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 486 | `unfold Iterator.moveNext` | ideal |
| 487 | `obtain ⟨hidx, hcur⟩ := hvalid` | ideal |
| 488 | `obtain ⟨r, v, hcell⟩ := exists_cell l it.index hidx` | ideal |
| 489 | `simp only [show it.cur = some r from by grind, get!_some]` | ideal |
| 490 | `sl_step` | ideal |
| 491 | `by_cases hlast : it.index + 1 = l.length` | ideal |
| 492 | `· sl_step*` | ideal |
| 493 | `· obtain ⟨r', v', hcell'⟩ := exists_cell l (it.index + 1) (by omega) …` | ideal |

Spot at line 492 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 492 | `sl_step*` | ideal |

Spot at line 493 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 493 | `obtain ⟨r', v', hcell'⟩ := exists_cell l (it.index + 1) (by omega)` | ideal |
| 494 | `simp only [nodeAt, nextOf, if_neg hlast, hcell', Option.map_some, valid]` | ideal |
| 495 | `sl_step*` | ideal |

#### `run.spec` (line 533) — 1/1 spots ideal

Spot at line 536 — ideal:

| Line | Step | Verdict |
|---:|---|---|
| 536 | `unfold run` | ideal |
| 537 | `sl_step*` | ideal |

## `Aeneas/SLPoC/Examples/VerusStd.lean`

| Declaration | Line | Spots | Ideal | Score |
|---|---:|---:|---:|---:|
| `cellsFrom_read` | 234 | 1 | 0 | 0.0% |
| **Total** | | **1** | **0** | **0.0%** |

0 of 1 proofs are ideal throughout.

### Proofs, spot by spot

#### `cellsFrom_read` (line 234) — 0/1 spots ideal

Spot at line 237 — not ideal:

| Line | Step | Verdict |
|---:|---|---|
| 237 | `rw [cellsFrom_split f l i r v h]` | **manual**: mentions the separation-logic declaration `cellsFrom_split` |
| 238 | `sl_step*` | ideal |

