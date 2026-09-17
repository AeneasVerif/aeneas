import Aeneas.Std.Buffer
import SepLogic.MutableData.Ptr
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
Compatibility layer for the original mutable-data buffer prototype.
New code should use `Aeneas.Std.Buffer`.
-/

open Aeneas
open Aeneas.SepLogic

namespace SepLogic

abbrev Buffer := Aeneas.Std.Buffer

namespace Buffer

abbrev ptr {T : Type} (b : Buffer T) : Aeneas.Std.MutRawPtr T :=
  Aeneas.Std.Buffer.ptr b

abbrev ptrAt {T : Type} (b : Buffer T) (i : Nat) : Aeneas.Std.MutRawPtr T :=
  Aeneas.Std.Buffer.ptrAt b i

abbrev sub {T : Type} (b : Buffer T) (i n : Nat) : Buffer T :=
  Aeneas.Std.Buffer.sub b i n

abbrev split {T : Type} (b : Buffer T) (i : Nat) : Buffer T × Buffer T :=
  Aeneas.Std.Buffer.split b i

abbrev join {T : Type} (left right : Buffer T) : Buffer T :=
  Aeneas.Std.Buffer.join left right

export Aeneas.Std.Buffer
  (pointsTo alloc pointsTo_def read write free
   length_of_pointsTo ofList fill pointsTo_pair_entails pair_entails_pointsTo
   copy compare swap pointsTo_entails_range range_entails_pointsTo
   pointsTo_split pointsTo_join pointsTo_sub mut_to_raw end_mut_to_raw)

theorem read.spec_array {T : Type} (b : Buffer T) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ Aeneas.Std.Buffer.read b i
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ b ↦ values⦄ :=
  Aeneas.Std.Buffer.read.spec_buffer b values i hIndex

theorem write.spec_array {T : Type} (b : Buffer T) (values : List T) (i : Nat)
    (value : T) (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ Aeneas.Std.Buffer.write b i value
      ⦃⇓ b ↦ values.set i value⦄ :=
  Aeneas.Std.Buffer.write.spec_buffer b values i value hIndex

theorem mut_to_raw.spec {T : Type} (slice : Aeneas.Std.Slice T) :
    ⦃ emp ⦄ Aeneas.Std.Buffer.mut_to_raw slice
      ⦃⇓ b => b ↦ slice.val⦄ :=
  Aeneas.Std.Buffer.mut_to_raw.spec slice

theorem end_mut_to_raw.spec {T : Type} (original : Aeneas.Std.Slice T)
    (b : Buffer T) (values : List T) :
    ⦃ b ↦ values ⦄ Aeneas.Std.Buffer.end_mut_to_raw original b
      ⦃⇓ result =>
        ⌜result.val = original.val.setSlice! 0 values⌝⦄ :=
  Aeneas.Std.Buffer.end_mut_to_raw.spec original b values

end Buffer

end SepLogic
