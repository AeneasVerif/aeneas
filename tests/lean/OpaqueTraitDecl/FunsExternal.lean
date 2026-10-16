module
public import Aeneas
public import OpaqueTraitDecl.Types
@[expose] public section
open Aeneas Aeneas.Std Result

/-! The external functions of `OpaqueTraitDecl` (see `TypesExternal.lean`). -/

def shapes.circle (r : Std.U32) : Result shapes.Circle := ok { r }

def shapes.Circle.Insts.Opaque_trait_declShapesShape.area (c : shapes.Circle) : Result Std.U32 := do
  let a ← 3#u32 * c.r
  a * c.r

def shapes.total {S : Type _} (ShapeInst : shapes.Shape S) (a b : S) : Result Std.U32 := do
  let x ← ShapeInst.area a
  let y ← ShapeInst.area b
  x + y
