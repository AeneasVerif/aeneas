-- Correctness proofs for docs-example tests in `VecDequeMethods.lean`.

import VecDequeMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace vec_deque_methods

/-- `VecDeque::push_back` then `VecDeque::pop_front` yields the elements in
FIFO order. -/
theorem test_vec_deque_push_pop_correct :
    test_vec_deque_push_pop ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `VecDeque::new().len()` is `0`. -/
theorem test_vec_deque_len_empty_correct :
    test_vec_deque_len_empty ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end vec_deque_methods
