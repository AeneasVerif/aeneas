import Base

/-!

# Computing factorial

Test 1, test 2, test 3.

-/

open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace factorial

/- [factorial::factorial]:
   Source: 'src/factorial.rs', lines 1:0-1:27 -/
divergent def factorial (n : U64) : Result U64 :=
  if n = 0#u64
  then Result.ok 1#u64
  else do
       let i ← n - 1#u64
       let i1 ← factorial i
       n * i1

end factorial
