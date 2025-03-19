import Aeneas.Arith.Lemmas
open Aeneas.Arith

attribute [zify_simps] ZMod.val_natCast ZMod.val_intCast ZMod.castInt_val_sub ZMod.natCast_val
                       Int.ofNat_emod Nat.cast_ofNat
