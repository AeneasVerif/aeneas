import Aeneas.Std.RawPtr
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
Compatibility layer for the original separation-logic pointer prototype.
New code should use `Aeneas.Std.RawPtr`, `MutRawPtr`, and `ConstRawPtr`.
-/

open Aeneas
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Std.WP

theorem ispec_bind {α β : Type u} {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : Aeneas.Std.Result α}
    {next : α → Aeneas.Std.Result β}
    (hFirst : ispec P m Q₁)
    (hNext : ∀ value, ispec (Q₁ value) (next value) Q) :
    ispec P (m >>= next) Q :=
  Aeneas.Std.WP.ispec_bind hFirst (sep_emp_r P).mpr
    fun value => by rw [sep_emp_r_eq]; exact hNext value

theorem ispec_seq {α β : Type u} {P H : IPre} {Q : IPost β}
    {m₁ : Aeneas.Std.Result α} {m₂ : Aeneas.Std.Result β}
    (hFirst : ispec P m₁ (fun _ => H))
    (hSecond : ispec H m₂ Q) :
    ispec P (m₁ >>= fun _ => m₂) Q :=
  ispec_bind hFirst fun _ => hSecond

abbrev Ptr := Aeneas.Std.MutRawPtr

namespace Ptr

abbrev ref {T : Type} (q : Ptr T) : Aeneas.Std.Ref T :=
  Aeneas.Std.RawPtr.ref q

abbrev add {T : Type} (q : Ptr T) (i : Nat) : Ptr T :=
  Aeneas.Std.RawPtr.add q i

abbrev sameBase {T U : Type} (q₁ : Ptr T) (q₂ : Ptr U) : Prop :=
  Aeneas.Std.RawPtr.sameBase q₁ q₂

abbrev distance {T U : Type} (q₁ : Ptr T) (q₂ : Ptr U) : Nat :=
  Aeneas.Std.RawPtr.distance q₁ q₂

abbrev pointsToRange {T : Type} (q : Ptr T) (values : List T) :
    Aeneas.SepLogic.IProp :=
  Aeneas.Std.RawPtr.pointsToRange q values

abbrev singleton {T : Type} (q : Ptr T) (value : T) : Aeneas.Std.Heap :=
  Aeneas.Std.RawPtr.singleton q value

abbrev contains {T : Type} (h : Aeneas.Std.Heap) (q : Ptr T) : Prop :=
  Aeneas.Std.RawPtr.contains h q

export Aeneas.Std.RawPtr
  (base_add offset_add add_zero ref_add add_add pointsTo_eq_ref
   pointsTo_eq_range pointsToRange_append
   pointsToRange_split pointsToRange_eq_take_get_drop pointsToRange_cons
   pointsToRange_nil pointsTo_exclusive not_contains_empty
   contains_of_pointsTo ref_injective disjoint_singleton Readable
   readable_of_pointsTo take_set drop_set)

end Ptr

theorem pointsTo_exclusive {T : Type} (q : Ptr T) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ :=
  Aeneas.Std.RawPtr.pointsTo_exclusive q value₁ value₂

abbrev allocArray {T β : Type} (values : List T) (mk : Aeneas.Std.Ref T → β) :
    Aeneas.Std.Result β :=
  Aeneas.Std.RawPtr.allocArray values mk

theorem allocArray.spec {T β : Type} (values : List T)
    (mk : Aeneas.Std.Ref T → β) (post : β → Aeneas.SepLogic.IProp)
    (hPost : ∀ r : Aeneas.Std.Ref T,
      Aeneas.SepLogic.owns (Aeneas.Std.Heap.rangeHeap r values) ⊢ post (mk r)) :
    ⦃ emp ⦄ allocArray values mk ⦃⇓ result => post result⦄ :=
  Aeneas.Std.RawPtr.allocArray.spec values mk post hPost

abbrev alloc {T : Type} (value : T) : Aeneas.Std.Result (Ptr T) :=
  Aeneas.Std.MutRawPtr.alloc value

@[step]
theorem alloc.spec {T : Type} (value : T) :
    ⦃ emp ⦄ alloc value ⦃⇓ q => q ↦ value⦄ :=
  Aeneas.Std.MutRawPtr.alloc.spec value

abbrev read {T : Type} (q : Ptr T) : Aeneas.Std.Result T :=
  Aeneas.Std.RawPtr.read q

@[step]
theorem read.spec {T : Type} (q : Ptr T) (value : T) :
    ⦃ q ↦ value ⦄ read q
      ⦃⇓ result => ⌜result = value⌝ ∗ q ↦ value⦄ :=
  Aeneas.Std.RawPtr.read.spec q value

theorem read.spec_range {T : Type} (q : Ptr T) (values : List T)
    (i : Nat) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ read (Ptr.add q i)
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ :=
  Aeneas.Std.RawPtr.read.spec_range q values i hIndex

theorem read.spec_frame {T : Type} (q : Ptr T) (value : T)
    (H : Aeneas.SepLogic.IProp) :
    ⦃ q ↦ value ∗ H ⦄ read q
      ⦃⇓ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ :=
  Aeneas.Std.RawPtr.read.spec_frame q value H

abbrev free {T : Type} (q : Ptr T) : Aeneas.Std.Result Unit :=
  Aeneas.Std.MutRawPtr.free q

@[step]
theorem free.spec {T : Type} (q : Ptr T) (value : T) :
    ⦃ q ↦ value ⦄ free q ⦃⇓ emp⦄ :=
  Aeneas.Std.MutRawPtr.free.spec q value

abbrev freeRange {T : Type} (q : Ptr T) (n : Nat) : Aeneas.Std.Result Unit :=
  Aeneas.Std.MutRawPtr.freeRange q n

@[step]
theorem freeRange.spec {T : Type} (q : Ptr T) (values : List T) :
    ⦃ q ↦* values ⦄ freeRange q values.length ⦃⇓ emp⦄ :=
  Aeneas.Std.MutRawPtr.freeRange.spec q values

abbrev fillRange {T : Type} (q : Ptr T) (value : T) (n : Nat) :
    Aeneas.Std.Result Unit :=
  Aeneas.Std.MutRawPtr.fillRange q value n

@[step]
theorem fillRange.spec {T : Type} (q : Ptr T) (values : List T) (value : T) :
    ⦃ q ↦* values ⦄ fillRange q value values.length
      ⦃⇓ q ↦* List.replicate values.length value⦄ :=
  Aeneas.Std.MutRawPtr.fillRange.spec q values value

abbrev copyRange {T : Type} (dst src : Ptr T) (n : Nat) :
    Aeneas.Std.Result Unit :=
  Aeneas.Std.MutRawPtr.copyRange dst src n

@[step]
theorem copyRange.spec {T : Type} (dst src : Ptr T)
    (dstValues srcValues : List T)
    (hLength : dstValues.length = srcValues.length) :
    ⦃ dst ↦* dstValues ∗ src ↦* srcValues ⦄
      copyRange dst src srcValues.length
      ⦃⇓ dst ↦* srcValues ∗ src ↦* srcValues⦄ :=
  Aeneas.Std.MutRawPtr.copyRange.spec dst src dstValues srcValues hLength

abbrev compareRange {T : Type} [DecidableEq T] (left right : Ptr T) (n : Nat) :
    Aeneas.Std.Result Bool :=
  Aeneas.Std.RawPtr.compareRange left right n

@[step]
theorem compareRange.spec {T : Type} [DecidableEq T] (left right : Ptr T)
    (leftValues rightValues : List T)
    (hLength : leftValues.length = rightValues.length) :
    ⦃ left ↦* leftValues ∗ right ↦* rightValues ⦄
      compareRange left right leftValues.length
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦* leftValues ∗ right ↦* rightValues)⦄ :=
  Aeneas.Std.RawPtr.compareRange.spec left right leftValues rightValues hLength

abbrev mut_to_raw {T : Type} (value : T) : Aeneas.Std.Result (Ptr T) :=
  Aeneas.Std.MutRawPtr.mut_to_raw value

@[step]
theorem mut_to_raw.spec {T : Type} (value : T) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ q => q ↦ value⦄ :=
  Aeneas.Std.MutRawPtr.mut_to_raw.spec value

abbrev takeRange {T : Type} (q : Ptr T) (n : Nat) :
    Aeneas.Std.Result (List T) :=
  Aeneas.Std.MutRawPtr.takeRange q n

@[step]
theorem takeRange.spec {T : Type} (q : Ptr T) (values : List T) :
    ⦃ q ↦* values ⦄ takeRange q values.length
      ⦃⇓ result => ⌜result = values⌝⦄ :=
  Aeneas.Std.MutRawPtr.takeRange.spec q values

theorem takeRange.spec_of_length {T : Type} (q : Ptr T)
    (values : List T) (n : Nat) (hLength : values.length = n) :
    ⦃ q ↦* values ⦄ takeRange q n
      ⦃⇓ result => ⌜result = values⌝⦄ :=
  Aeneas.Std.MutRawPtr.takeRange.spec_of_length q values n hLength

abbrev end_mut_to_raw {T : Type} (q : Ptr T) : Aeneas.Std.Result T :=
  Aeneas.Std.MutRawPtr.end_mut_to_raw q

@[step]
theorem end_mut_to_raw.spec {T : Type} {value : T} (q : Ptr T) :
    ⦃ q ↦ value ⦄ end_mut_to_raw q
      ⦃⇓ result => ⌜result = value⌝⦄ :=
  Aeneas.Std.MutRawPtr.end_mut_to_raw.spec q

abbrev update {T : Type} (q : Ptr T) (value : T) : Aeneas.Std.Result Unit :=
  Aeneas.Std.MutRawPtr.write q value

@[step]
theorem update.spec {T : Type} (q : Ptr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ update q newValue ⦃⇓ q ↦ newValue⦄ :=
  Aeneas.Std.MutRawPtr.write.spec q oldValue newValue

theorem update.spec_range {T : Type} (q : Ptr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ update (Ptr.add q i) value
      ⦃⇓ q ↦* values.set i value⦄ :=
  Aeneas.Std.MutRawPtr.write.spec_range q values i value hIndex

end SepLogic
