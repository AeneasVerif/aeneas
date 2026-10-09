/- Checks that generic extracted code and the Std models are universe-polymorphic: they are
   instantiated with `Type`, which lives in `Type 1`. This guards the `Type _` convention for
   when `Result` lives in a higher universe than its argument (function items `A → Result B` are
   then outside `Type`). -/
import FnPtrGeneric

open Aeneas Std Result

noncomputable section

namespace fn_ptr_generic

example : Result Type := id Nat
example (h : Holder Type) : Result Type := get_x h
example (o : Option Type) : Result Type := unwrap_or o Nat
example (w : Wrap Type) : Result Type := (Wrap.Insts.Fn_ptr_genericHasOut Type).get w
example (v : alloc.vec.Vec Type) : Result Type :=
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Type) v 0#usize
example (s : Aeneas.Std.Slice Type) : Result (alloc.vec.Vec Type) :=
  lift (alloc.slice.Slice.into_vec s)
example (inst : core.ops.function.FnOnce (Nat → Result Type) Nat Type) (o : Option Nat)
    (f : Nat → Result Type) : Result (Option Type) :=
  core.option.Option.map inst o f

end fn_ptr_generic

end
