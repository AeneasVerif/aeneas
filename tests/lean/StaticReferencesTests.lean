module
import StaticReferences
public meta import StaticReferences

open Aeneas Aeneas.Std Result static_references

private def owner : Buffer := { bytes := Array.make 3#usize [7#u8, 8#u8, 9#u8] }

-- These checks inspect the translated strings directly: Rust's str operations
-- have no model here, and adding one would be unrelated to lifetime translation.
#guard (update_static 7#u32).reducesTo (8#u32, 8#u32)
#guard static_label.reducesTo (toStr "NaN")
#guard (do let (s, _) ← Buffer.label owner; ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (s, _) ← required U32.Insts.Static_referencesLabel owner 42#u32;
           ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (s, _) ← provided U32.Insts.Static_referencesLabel owner 42#u32;
           ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (s, _) ← required Holder.Insts.Static_referencesLabel owner 1#u8;
           ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (s, _) ← provided Holder.Insts.Static_referencesLabel owner 1#u8;
           ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (s, _) ← borrowed owner 1#u8 1#u8;
           ok s : Result Str).reducesTo (toStr "NaN")
#guard (do let (_, owner') ← borrowed owner 1#u8 1#u8;
           ok owner'.bytes.val : Result (List Std.U8)).reducesTo [7#u8, 8#u8, 9#u8]
