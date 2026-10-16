module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-! The external types of `OpaqueTraitDecl`: the model of the opaque module `shapes`, including its
trait declaration (in practice, they would be given by the model of the crate which defines them). -/

structure shapes.Shape (Self : Type _) where
  area : Self → Result Std.U32

structure shapes.Circle where
  r : Std.U32
