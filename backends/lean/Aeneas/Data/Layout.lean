module
public import Aeneas.Data.MTypes
public section

namespace Aeneas

inductive Discriminator (ty : IUScalarTy) where
  | known (n : IUScalar ty)
  | invalid
  -- the matcher is a finite total function
  | read (offset : Nat) (ty' : IUScalarTy) (matcher : BitVec ty'.numBits -> Discriminator ty)

structure TagToWrite where
  offset : Nat
  ty : IUScalarTy
  data : IUScalar ty

inductive MType.Layout : MType → Type 0 where
  | int : MType.Layout (.int ty)
  | tuple
      (field_offs : Fin ts.length → Nat)
      (field_layouts : (idx : Fin ts.length) → MType.Layout ts[idx])
      (size : Nat)
      (align : Nat) :
      MType.Layout (.tuple ts)
  | enum
      (variant_tags : Fin vs.length → TagToWrite)
      (variant_layouts : (idx : Fin vs.length) → MType.Layout vs[idx])
      (discr_ty : IUScalarTy)
      (discr : Discriminator discr_ty)
      (size : Nat)
      (align : Nat) :
      MType.Layout (.enum vs)

def MType.Layout.size_and_align : {ty : MType} → MType.Layout ty → Nat × Nat
  | .int ty, .int => (ty.numBits / 8, ty.numBits / 8) -- todo we should get this from somewhere..?
  | _, .tuple _ _ size align => (size, align)
  | _, .enum _ _ _ _ size align => (size, align)

end Aeneas
