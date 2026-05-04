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

/-- Generic raw-pointer cast.

Used to lower Rust raw-pointer casts whose pointee is not a scalar type
(for example casts of the form `*const u8 as *const __m128i`, which are
ubiquitous in SIMD intrinsics code). The source and target pointee
types are left implicit and inferred by Lean from the surrounding
context; only the target mutability is provided explicitly because it
cannot in general be deduced from the use site.

Like [RawPtr.cast_scalar], this is a placeholder: it always returns
[.fail .undef]. We can give it a meaningful definition once we have
separation logic. -/
def RawPtr.cast {T T' : Type} {M : Mutability} (M' : Mutability) (_ : RawPtr T M) :
  Result (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std
