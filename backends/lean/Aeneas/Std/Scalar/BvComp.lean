module
public import Aeneas.Std.Scalar.Core
public section

namespace Aeneas.Std

/-
Heterogeneous version of some `U8.bv ∘ UScalar.mk = id` lemmas in case `numBits` still gets rewritten eagerly.
This may seem overly specific, but the issue does happen, making some proofs extremely cumbersome.
-/

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem U8.bv_comp_UScalar_mk :
     @Function.comp (BitVec 8) U8 (BitVec 8) U8.bv (@UScalar.mk .U8) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem U16.bv_comp_UScalar_mk :
     @Function.comp (BitVec 16) U16 (BitVec 16) U16.bv (@UScalar.mk .U16) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem U32.bv_comp_UScalar_mk :
     @Function.comp (BitVec 32) U32 (BitVec 32) U32.bv (@UScalar.mk .U32) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem U64.bv_comp_UScalar_mk :
     @Function.comp (BitVec 64) U64 (BitVec 64) U64.bv (@UScalar.mk .U64) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem U128.bv_comp_UScalar_mk :
     @Function.comp (BitVec 128) U128 (BitVec 128) U128.bv (@UScalar.mk .U128) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem Usize.bv_comp_UScalar_mk :
     @Function.comp (BitVec System.Platform.numBits) Usize (BitVec System.Platform.numBits)
       Usize.bv (@UScalar.mk .Usize) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem I8.bv_comp_IScalar_mk :
     @Function.comp (BitVec 8) I8 (BitVec 8) I8.bv (@IScalar.mk .I8) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem I16.bv_comp_IScalar_mk :
     @Function.comp (BitVec 16) I16 (BitVec 16) I16.bv (@IScalar.mk .I16) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem I32.bv_comp_IScalar_mk :
     @Function.comp (BitVec 32) I32 (BitVec 32) I32.bv (@IScalar.mk .I32) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem I64.bv_comp_IScalar_mk :
     @Function.comp (BitVec 64) I64 (BitVec 64) I64.bv (@IScalar.mk .I64) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem I128.bv_comp_IScalar_mk :
     @Function.comp (BitVec 128) I128 (BitVec 128) I128.bv (@IScalar.mk .I128) = id := rfl

 @[simp, scalar_tac_simps, simp_lists_safe, simp_scalar_safe]
 theorem Isize.bv_comp_IScalar_mk :
     @Function.comp (BitVec System.Platform.numBits) Isize (BitVec System.Platform.numBits)
       Isize.bv (@IScalar.mk .Isize) = id := rfl

end Aeneas.Std
