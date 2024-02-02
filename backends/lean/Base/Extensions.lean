import Lean
import Std.Lean.HashSet
import Base.Utils
import Base.Primitives.Base

import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp

/-! Various state extensions used in the library -/
namespace Extensions

open Lean Elab Term Meta
open Utils

-- This is not used anymore but we keep it here.
-- TODO: the original function doesn't define correctly the `addImportedFn`. Do a PR?
def mkMapDeclarationExtension [Inhabited α] (name : Name := by exact decl_name%) :
  IO (MapDeclarationExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insert k v) s) RBMap.empty,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

/- Discrimination trees map expressions to values. When storing an expression
   in a discrimination tree, the expression is first converted to an array
   of `DiscrTree.Key`, which are the keys actually used by the discrimination
   trees. The conversion operation is monadic, however, and extensions require
   all the operations to be pure. For this reason, in the state extension, we
   store the keys from *after* the transformation (i.e., the `DiscrTreeKey`
   below). The transformation itself can be done elsewhere.
 -/
abbrev DiscrTreeKey := Array DiscrTree.Key

abbrev DiscrTreeExtension (α : Type) :=
  SimplePersistentEnvExtension (DiscrTreeKey × α) (DiscrTree α)

def mkDiscrTreeExtention [Inhabited α] [BEq α] (name : Name := by exact decl_name%) :
  IO (DiscrTreeExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertCore k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertCore n.1 n.2 ,
  }

end Extensions
