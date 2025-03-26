import Aeneas.Arith.Lemmas
import Aeneas.Std.Scalar.Core
open Aeneas Arith Std

attribute [zify_simps] ZMod.val_natCast ZMod.val_intCast ZMod.castInt_val_sub ZMod.natCast_val
                       Int.ofNat_emod Nat.cast_ofNat
                       BitVec.toNat_mul BitVec.toNat_ofNat
                       UScalar.bv_toNat
