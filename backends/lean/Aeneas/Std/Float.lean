import Aeneas.Std.Scalar.Core

namespace Aeneas
namespace Std

/-!
# Floating-Point Primitives

The Lean backend maps Rust `f32` and `f64` to Lean's native `Float32` and
`Float` types.  Lean provides the basic arithmetic, comparison and finite
literal machinery directly.  We keep operations that Lean does not expose
directly as opaque primitives so extracted code type-checks while leaving their
precise IEEE semantics to future specifications.
-/

abbrev F32 := Float32
abbrev F64 := Float

namespace F32

def ofUScalar {ty : UScalarTy} (x : UScalar ty) : F32 :=
  Float32.ofNat x.val

def ofIScalar {ty : IScalarTy} (x : IScalar ty) : F32 :=
  Float32.ofInt x.val

opaque toUScalar (ty : UScalarTy) (x : F32) : UScalar ty
opaque toIScalar (ty : IScalarTy) (x : F32) : IScalar ty

opaque rem (x y : F32) : F32

end F32

namespace F64

def ofUScalar {ty : UScalarTy} (x : UScalar ty) : F64 :=
  Float.ofNat x.val

def ofIScalar {ty : IScalarTy} (x : IScalar ty) : F64 :=
  Float.ofInt x.val

opaque toUScalar (ty : UScalarTy) (x : F64) : UScalar ty
opaque toIScalar (ty : IScalarTy) (x : F64) : IScalar ty

opaque rem (x y : F64) : F64

end F64

end Std
end Aeneas
