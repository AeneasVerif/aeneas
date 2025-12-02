import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

inductive Mutability where
| Mut | Const

-- We don't really use raw pointers for now
structure RawPtr (T : Type) (M : Mutability) where
  v : T

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

-- TODO: we can properly define this once we have separation logic
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T'] (_ : RawPtr T M) :
  Result (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std
