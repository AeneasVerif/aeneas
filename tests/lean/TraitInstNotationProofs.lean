import TraitInstNotation
open Aeneas Aeneas.Std Result Error

/-! # Term-identity checks for the `-trait-inst-notation` extraction

The `({Trait<Args> for Type})` notation must elaborate to the implementation
constants and method definitions themselves, so that the terms are identical
to the ones the standard extraction produces (in particular, the `progress`
spec theorems keep applying). -/

namespace trait_inst_notation

-- The notation resolves to the registered implementation constant
example : ({ToU64 for Std.U64}) = U64.Insts.Trait_inst_notationToU64 := rfl

-- A generic implementation instantiated at concrete types resolves to the
-- implementation applied to its arguments, with the nested instance resolved
-- recursively
example :
    ({ToU64 for (Std.U64, Std.U64)})
    = Pair.Insts.Trait_inst_notationToU64 U64.Insts.Trait_inst_notationToU64
    := rfl

-- A method member access on the notation resolves to the method *definition*
-- (not a record projection): the terms are byte-identical to the direct calls
-- of the standard extraction
example :
    use_with_len
    = fun x => ArrayU3232.Insts.Trait_inst_notationWithLenU32.first x := rfl

-- Clause references resolve to the clause binders themselves
example {T : Type} (inst : ToU64 T) (x : T) :
    use_clause inst x = inst.to_u64 x := rfl

-- Parent-clause references resolve through the parent-clause fields
example {T : Type} (inst : Child T) (x : T) :
    use_parent_through_child inst x = inst.ParentInst.name x := rfl

end trait_inst_notation
