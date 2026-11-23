module

import AeneasSpec.FileLayout
meta import AeneasSpec.FileLayout

/-!
# Examples of the file layout algorithm

Each example lists items in source order and dependencies by name, and shows the files the
algorithm produces: for each file, its first item (which identifies it), the files it imports, and
its blocks in order.
-/

namespace Aeneas.Spec.Examples

/-- An item for the examples, at the given line of `src/lib.rs`. -/
def item (name : String) (kind : ItemKind) (module : List String) (line : Nat)
    (opacity : ItemOpacity := .transparent) : RustItem where
  rustName := name
  kind := kind
  opacity := opacity
  rustModule := ⟨module⟩
  srcSpan := ⟨"src/lib.rs", ⟨line, 0⟩, ⟨line, 0⟩⟩

/-- A context with the given items, where `(a, b) ∈ edges` means `a` depends on `b`. -/
def mkCtx (items : List RustItem) (edges : List (String × String)) : TranslationCtx where
  crateName := "ex"
  items := items.toFinset
  deps := ⟨fun i j => (i.val.rustName, j.val.rustName) ∈ edges⟩

instance (items : List RustItem) (edges : List (String × String)) :
    DecidableRel (mkCtx items edges).deps.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val.rustName, j.val.rustName) ∈ edges))

/-- The items in source order (the order of the list). -/
def srcOrder (items : List RustItem) (edges : List (String × String)) :
    List (mkCtx items edges).items :=
  items.attach.map fun ⟨x, h⟩ => ⟨x, List.mem_toFinset.2 h⟩

/-- Run the algorithm and show each file as (first item, imported files, blocks). -/
def run (items : List RustItem) (edges : List (String × String)) :
    List (String × List String × List (List String)) :=
  let c := mkCtx items edges
  let src := srcOrder items edges
  (c.fileReps src).map fun f =>
    (f.val.rustName,
      ((c.fileReps src).filter (fun g => g ∈ c.fileImports src f)).map (·.val.rustName),
      (c.fileBlocks src f).map (·.map (·.val.rustName)))

-- One module; `a` depends on `c`, so `c` is moved forward to just before `a`.
#guard run [item "a" .funDecl ["ex"] 1, item "b" .funDecl ["ex"] 2, item "c" .funDecl ["ex"] 3]
  [("a", "c")] ==
    [("a", [], [["c"], ["a"], ["b"]])]

-- `x` needs `b`, so `b` is moved forward to just before `x`, and so before `a`, although `a` does
-- not need it: blocks are ordered by their first user (`FilesFollowModules.source_order`).
#guard run [item "x" .funDecl ["ex"] 1, item "a" .funDecl ["ex"] 2, item "b" .funDecl ["ex"] 3]
  [("x", "b")] ==
    [("x", [], [["b"], ["x"], ["a"]])]

-- `f` and `g` are mutually recursive, so they form one `mutual` block, which `h` needs.
#guard run [item "h" .funDecl ["ex"] 1, item "f" .funDecl ["ex"] 2, item "g" .funDecl ["ex"] 3]
  [("h", "f"), ("f", "g"), ("g", "f")] ==
    [("h", [], [["f", "g"], ["h"]])]

-- Modules `a` and `c` use each other, so they share a file; module `b` gets its own file, which
-- that file imports. Within the shared file, `a2` needs `c1`, which is moved forward.
#guard run [item "a1" .funDecl ["ex", "a"] 1, item "a2" .funDecl ["ex", "a"] 2,
    item "b1" .typeDecl ["ex", "b"] 3, item "c1" .funDecl ["ex", "c"] 4]
  [("a1", "b1"), ("c1", "a1"), ("a2", "c1")] ==
    [("a1", ["b1"], [["a1"], ["c1"], ["a2"]]), ("b1", [], [["b1"]])]

-- `len` is already in Aeneas's library (`external`), so it is not written.
#guard run [item "len" .funDecl ["core", "slice"] 1 .external, item "f" .funDecl ["ex"] 2]
  [("f", "len")] ==
    [("f", [], [["f"]])]

/--
info: 'Aeneas.Spec.TranslationCtx.algorithm_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TranslationCtx.algorithm_spec

end Aeneas.Spec.Examples
