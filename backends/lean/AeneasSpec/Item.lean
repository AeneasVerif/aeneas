module

/-!
# Rust items

The data Aeneas keeps about each item of a Rust program (first approximation).
-/

@[expose] public section

namespace Aeneas.Spec

/-- An item of a Rust program is one of five things (as in Charon's `ItemId`). -/
inductive ItemKind
  | traitDecl
  | traitImpl
  | funDecl
  | typeDecl
  | globalDecl
  deriving DecidableEq, Repr

/-- How much of an item needs to be written in the translation. -/
inductive ItemOpacity
  /-- Signature and body need to be written -/
  | transparent
  /-- Only the signature needs to be written -/
  | opaque
  /-- Translated signature exists externally, only the import needs to be added. -/
  | external
  deriving DecidableEq, Repr

/-- A position in a source file. -/
structure SrcLoc where
  /-- 1-based line number. -/
  line : Nat
  /-- 0-based column offset. -/
  col : Nat
  deriving DecidableEq, Repr

/-- A span of source code within a file (cf. Charon's `SpanData`). -/
structure SrcSpan where
  /-- Path of the source file. -/
  file : String
  start : SrcLoc
  stop : SrcLoc
  deriving DecidableEq, Repr

/-- A Rust module, given by its path. The first segment is the name of its crate, as in
`core::slice`. -/
structure RustModule where
  /-- The path segments. -/
  path : List String
  deriving DecidableEq, Repr

/-- The crate a module belongs to: the first segment of its path. -/
def RustModule.crate? (m : RustModule) : Option String :=
  m.path.head?

/-- An item of a Rust program, as Charon presents it. -/
structure RustItem where
  /-- The item's name within `rustModule`: its Rust identifier, or the name Charon generates for
  items without one (trait impls, items declared inside function bodies). -/
  rustName : String
  kind : ItemKind
  opacity : ItemOpacity
  /-- The Rust module where the item was defined. -/
  rustModule : RustModule
  /-- Where the item's source code is. -/
  srcSpan : SrcSpan
  deriving DecidableEq, Repr

/-- The crate where an item is defined. -/
def RustItem.crate? (item : RustItem) : Option String :=
  item.rustModule.crate?

end Aeneas.Spec
