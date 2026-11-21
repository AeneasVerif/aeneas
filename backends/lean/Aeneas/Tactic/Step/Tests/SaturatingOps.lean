module
import all Aeneas.Std.Scalar.SaturatingOps
import Aeneas.Tactic.Step.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.SaturatingOps

/- Test the specifications through the Rust-facing names for every scalar type. -/

example (x y : U8) :
    Aeneas.Std.lift (core.num.U8.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U8) ⦄ := by
  step
  assumption

example (x y : U16) :
    Aeneas.Std.lift (core.num.U16.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U16) ⦄ := by
  step
  assumption

example (x y : U32) :
    Aeneas.Std.lift (core.num.U32.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U32) ⦄ := by
  step
  assumption

example (x y : U64) :
    Aeneas.Std.lift (core.num.U64.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U64) ⦄ := by
  step
  assumption

example (x y : U128) :
    Aeneas.Std.lift (core.num.U128.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U128) ⦄ := by
  step
  assumption

example (x y : Usize) :
    Aeneas.Std.lift (core.num.Usize.saturating_add x y)
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .Usize) ⦄ := by
  step
  assumption

example (x y : U8) :
    Aeneas.Std.lift (core.num.U8.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : U16) :
    Aeneas.Std.lift (core.num.U16.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : U32) :
    Aeneas.Std.lift (core.num.U32.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : U64) :
    Aeneas.Std.lift (core.num.U64.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : U128) :
    Aeneas.Std.lift (core.num.U128.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : Usize) :
    Aeneas.Std.lift (core.num.Usize.saturating_sub x y)
      ⦃ r => r.val = x.val - y.val ⦄ := by
  step
  assumption

example (x y : I8) :
    Aeneas.Std.lift (core.num.I8.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .I8)
        (Min.min (IScalar.max .I8) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : I16) :
    Aeneas.Std.lift (core.num.I16.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .I16)
        (Min.min (IScalar.max .I16) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : I32) :
    Aeneas.Std.lift (core.num.I32.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .I32)
        (Min.min (IScalar.max .I32) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : I64) :
    Aeneas.Std.lift (core.num.I64.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .I64)
        (Min.min (IScalar.max .I64) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : I128) :
    Aeneas.Std.lift (core.num.I128.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .I128)
        (Min.min (IScalar.max .I128) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : Isize) :
    Aeneas.Std.lift (core.num.Isize.saturating_add x y)
      ⦃ r => r.val = Max.max (IScalar.min .Isize)
        (Min.min (IScalar.max .Isize) (x.val + y.val)) ⦄ := by
  step
  assumption

example (x y : I8) :
    Aeneas.Std.lift (core.num.I8.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .I8)
        (Min.min (IScalar.max .I8) (x.val - y.val)) ⦄ := by
  step
  assumption

example (x y : I16) :
    Aeneas.Std.lift (core.num.I16.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .I16)
        (Min.min (IScalar.max .I16) (x.val - y.val)) ⦄ := by
  step
  assumption

example (x y : I32) :
    Aeneas.Std.lift (core.num.I32.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .I32)
        (Min.min (IScalar.max .I32) (x.val - y.val)) ⦄ := by
  step
  assumption

example (x y : I64) :
    Aeneas.Std.lift (core.num.I64.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .I64)
        (Min.min (IScalar.max .I64) (x.val - y.val)) ⦄ := by
  step
  assumption

example (x y : I128) :
    Aeneas.Std.lift (core.num.I128.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .I128)
        (Min.min (IScalar.max .I128) (x.val - y.val)) ⦄ := by
  step
  assumption

example (x y : Isize) :
    Aeneas.Std.lift (core.num.Isize.saturating_sub x y)
      ⦃ r => r.val = Max.max (IScalar.min .Isize)
        (Min.min (IScalar.max .Isize) (x.val - y.val)) ⦄ := by
  step
  assumption

/- A pure saturating call underneath a monadic bind must expose its value specification. -/
example (x y : U32) :
    (do let z ← Aeneas.Std.lift (core.num.U32.saturating_add x y)
        Aeneas.Std.lift (core.num.U32.saturating_sub z y))
      ⦃ r => r.val = Min.min (x.val + y.val) (UScalar.max .U32) - y.val ⦄ := by
  step as ⟨z, hz⟩
  step as ⟨r, hr⟩
  omega

/- Boundary cases distinguish saturation from wrapping, including both signed directions.
Unfold only the existing models, so these checks do not depend on the new specifications. -/
example : (core.num.U8.saturating_add 255#u8 1#u8).val = 255 := by
  conv_lhs => simp only [core.num.U8.saturating_add, UScalar.saturating_add, UScalar.val, UScalar.max]
  decide

example : (core.num.U8.saturating_sub 0#u8 1#u8).val = 0 := by
  conv_lhs => simp only [core.num.U8.saturating_sub, UScalar.saturating_sub, UScalar.val]
  decide

example : (core.num.I8.saturating_add 127#i8 1#i8).val = 127 := by
  conv_lhs => simp only [core.num.I8.saturating_add, IScalar.saturating_add, IScalar.val,
    IScalar.min, IScalar.max]
  decide

example : (core.num.I8.saturating_add (-128)#i8 (-1)#i8).val = -128 := by
  conv_lhs => simp only [core.num.I8.saturating_add, IScalar.saturating_add, IScalar.val,
    IScalar.min, IScalar.max]
  decide

example : (core.num.I8.saturating_sub 127#i8 (-1)#i8).val = 127 := by
  conv_lhs => simp only [core.num.I8.saturating_sub, IScalar.saturating_sub, IScalar.val,
    IScalar.min, IScalar.max]
  decide

example : (core.num.I8.saturating_sub (-128)#i8 1#i8).val = -128 := by
  conv_lhs => simp only [core.num.I8.saturating_sub, IScalar.saturating_sub, IScalar.val,
    IScalar.min, IScalar.max]
  decide

end Aeneas.Tactic.Step.Tests.SaturatingOps
