/- Utilities to have databases of theorems -/
import Lean
import Std.Lean.HashSet
import Base.Utils
import Base.Primitives.Base

namespace Lookup

open Lean Elab Term Meta
open Utils

-- TODO: the original function doesn't define correctly the `addImportedFn`. Do a PR?
def mkMapDeclarationExtension [Inhabited α] (name : Name := by exact decl_name%) :
  IO (MapDeclarationExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insert k v) s) RBMap.empty,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

-- Declare an extension of maps of maps (using [RBMap]).
-- The important point is that we need to merge the bound values (which are maps).
def mkMapMapDeclarationExtension [Inhabited β] (ord : α → α → Ordering)
  (name : Name := by exact decl_name%) :
  IO (MapDeclarationExtension (RBMap α β ord)) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a =>
      a.foldl (fun s a => a.foldl (
        -- We need to merge the maps
        fun s (k0, k1_to_v) =>
        match s.find? k0 with
        | none =>
          -- No binding: insert one
          s.insert k0 k1_to_v
        | some m =>
          -- There is already a binding: merge
          let m := RBMap.fold (fun m k v => m.insert k v) m k1_to_v
          s.insert k0 m)
          s) RBMap.empty,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

-- Declare an extension of maps of maps (using [HashMap]).
-- The important point is that we need to merge the bound values (which are maps).
def mkMapHashMapDeclarationExtension [BEq α] [Hashable α] [Inhabited β]
  (name : Name := by exact decl_name%) :
  IO (MapDeclarationExtension (HashMap α β)) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a =>
      a.foldl (fun s a => a.foldl (
        -- We need to merge the maps
        fun s (k0, k1_to_v) =>
        match s.find? k0 with
        | none =>
          -- No binding: insert one
          s.insert k0 k1_to_v
        | some m =>
          -- There is already a binding: merge
          let m := HashMap.fold (fun m k v => m.insert k v) m k1_to_v
          s.insert k0 m)
          s) RBMap.empty,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

end Lookup
