import Lean
import AeneasMeta.Utils

import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp

namespace Aeneas

/-! Various state extensions used in the library -/
namespace Extensions

open Lean Elab Term Meta
open Utils

def ListDeclarationExtension (α : Type) := SimplePersistentEnvExtension α (List α)

instance : Inhabited (ListDeclarationExtension α) :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension ..))

def mkListDeclarationExtension [Inhabited α] (name : Name := by exact decl_name%) :
  IO (ListDeclarationExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun entries => entries.foldl (fun s l => l.toList ++ s) [],
    addEntryFn    := fun l x => x :: l,
    toArrayFn     := fun l => l.toArray
  }

def SetDeclarationExtension := SimplePersistentEnvExtension Name NameSet

def mkSetDeclarationExtension (name : Name := by exact decl_name%) :
  IO SetDeclarationExtension :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s v => s.insert v) s) NameSet.empty,
    addEntryFn    := fun s n => s.insert n,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a b)
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

def mkDiscrTreeExtension [Inhabited α] [BEq α] (name : Name := by exact decl_name%) :
  IO (DiscrTreeExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertCore k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertCore n.1 n.2 ,
  }

end Extensions

end Aeneas
