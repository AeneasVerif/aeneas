module

import AeneasSpec.Naming.Registry
meta import AeneasSpec.Naming.Registry

/-!
# Examples of names

The crate being translated is `ex`.
-/

namespace Aeneas.Spec.Naming.Examples

/-- An identifier with no disambiguator. -/
def id (s : String) : PathElem := .ident s 0

/-- No field projector. -/
def noProj : LeanName → Bool := fun _ => false

/-- The name of a function of the crate, with no loop. -/
def fn (p : RustPath) (src : FunSource := .plain) (projector := noProj)
    (rename? : Option String := none) : LeanName :=
  funName {} "ex" projector { path := id "ex" :: p, rename? } src 0 none

-- The crate is dropped from local items, and kept for external ones.
#guard typeName "ex" { path := [id "ex", id "m", id "Foo"] } == ["m", "Foo"]
#guard typeName "ex" { path := [id "core", id "option", id "Option"], isLocal := false } ==
  ["core", "option", "Option"]

-- A variant is in the namespace of its type, a field is not.
#guard variantName "ex" { path := [id "ex", id "E"] } { name := "A" } == ["E", "A"]
#guard fieldName { name? := none } 0 == "_0"
#guard fieldName { name? := some "x", rename? := some "y" } 0 == "y"

-- The `rename` attribute replaces the last identifier.
#guard fn [id "m", id "foo"] (rename? := some "bar") == ["m", "bar"]

-- A non-zero disambiguator is appended.
#guard fn [id "f", .ident "g" 1] == ["f", "g_1"]

-- A method is named after the self type of its impl block. If a field of the type has the same
-- name, the method goes in an `impl` namespace.
#guard fn [.impl "Foo" false, id "len"] == ["Foo", "len"]
#guard fn [.impl "Foo" false, id "len"] (projector := (· == ["Foo", "len"])) ==
  ["Foo", "impl", "len"]

-- Default methods and constructors used as functions get a suffix.
#guard fn [id "Trait", id "f"] .traitDefault == ["Trait", "f", "default"]
#guard fn [id "S"] .adtConstructor == ["S", "constructor"]

-- The items of a trait impl are named after the impl, not where it is.
#guard traitImplName (.ofSelf ["Foo"] ["trait", "u32"]) == ["Foo", "Insts", "TraitU32"]
#guard fn [id "m", .impl "Trait" false, id "f"] (.traitImplItem (.ofSelf ["Foo"] ["Trait"]) "f")
  == ["Foo", "Insts", "Trait", "f"]
#guard traitImplName (.blanket ["Trait"]) == ["Trait", "Blanket"]

-- Loops: the position is omitted if there is a single loop.
#guard withLoop 2 (some ⟨[0, 1], false⟩) ["m", "f"] == ["m", "f_loop0_loop1"]
#guard withLoop 2 (some ⟨[1], true⟩) ["m", "f"] == ["m", "f_loop1", "body"]
#guard withLoop 1 (some ⟨[0], false⟩) ["m", "f"] == ["m", "f_loop"]

/-- Some keywords. -/
def isKeyword (s : String) : Bool := s ∈ ["end", "fun", "def"]

-- Keywords are escaped only as a whole name, and `-` always.
#guard escape isKeyword false ["end"] == [.quoted "end"]
#guard escape isKeyword false ["Foo", "end"] == [.plain "Foo", .plain "end"]
#guard escape isKeyword true ["end"] == [.plain "end"]
#guard escape isKeyword false ["f", "x86-64"] == [.plain "f", .quoted "x86-64"]

-- `«end»` and `end` are different for Aeneas, but Lean reads both as `end`.
#guard (escape isKeyword false ["«end»"]).map Atom.denote ==
  (escape isKeyword false ["end"]).map Atom.denote

-- A function clashes with a function, a field does not.
#guard (register [(.normal, 0, ["f"]), (.normal, 1, ["f"])]).clashes == [(0, 1, ["f"])]
#guard (register [(.lax, 0, ["x"]), (.lax, 1, ["x"]), (.normal, 2, ["x"])]).clashes == []

end Aeneas.Spec.Naming.Examples
