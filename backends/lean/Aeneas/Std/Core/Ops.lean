import Lean
import Aeneas.Std.Alloc

namespace Aeneas

namespace Std

open Result

@[rust_trait "core::ops::index::Index"]
structure core.ops.index.Index (Self Idx Output : Type) where
  index : Self → Idx → Result Output

@[rust_trait "core::ops::index::IndexMut" (parentClauses := ["indexInst"])]
structure core.ops.index.IndexMut (Self Idx Output : Type) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → Result (Output × (Output → Self))

@[rust_trait "core::ops::deref::Deref"]
structure core.ops.deref.Deref (Self Target : Type) where
  deref : Self → Result Target

@[rust_trait "core::ops::deref::DerefMut" (parentClauses := ["derefInst"])]
structure core.ops.deref.DerefMut (Self Target : Type) where
  derefInst : Deref Self Target
  deref_mut : Self → Result (Target × (Target → Self))

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefBoxInst (T : Type) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefMutBoxInst (T : Type) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

@[rust_trait "core::ops::bit::BitAnd"]
structure core.ops.bit.BitAnd (Self : Type) (Rhs : Type) (Self_Output : Type) where
  bitand : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::function::FnOnce"]
structure core.ops.function.FnOnce (Self : Type u) (Args : Type v) (Output : Type w) where
  call_once : Self → Args → Result Output

@[rust_trait "core::ops::function::FnMut" (parentClauses := ["FnOnceInst"])]
structure core.ops.function.FnMut (Self : Type u) (Args : Type v) (Output : Type w) where
  FnOnceInst : core.ops.function.FnOnce Self Args Output
  call_mut : Self → Args → Result (Output × Self)

@[rust_trait "core::ops::function::Fn" (parentClauses := ["FnMutInst"])]
structure core.ops.function.Fn (Self : Type u) (Args : Type v) (Output : Type w) where
  FnMutInst : core.ops.function.FnMut Self Args Output
  call : Self → Args → Result Output

def BuiltinFnOnce (Inputs : Type u) (Outputs : Type v) : core.ops.function.FnOnce (Inputs → Result Outputs) Inputs Outputs := {
  call_once f x := f x
}

def BuiltinFnMut (Inputs : Type u) (Outputs : Type v) : core.ops.function.FnMut (Inputs → Result Outputs) Inputs Outputs := {
  FnOnceInst := BuiltinFnOnce Inputs Outputs
  call_mut f x :=
    match f x with
    | ok y => ok (y, f)
    | fail e => fail e
    | div => div
}

def BuiltinFn (Inputs : Type u) (Outputs : Type v) : core.ops.function.Fn (Inputs → Result Outputs) Inputs Outputs := {
  FnMutInst := BuiltinFnMut Inputs Outputs
  call f x := f x
}

@[rust_trait "core::ops::try_trait::FromResidual"]
structure core.ops.try_trait.FromResidual (Self : Type u) (R : Type v) where
  from_residual : R → Result Self

@[rust_type "core::ops::control_flow::ControlFlow"]
inductive core.ops.control_flow.ControlFlow (B : Type) (C : Type) where
| Continue : C → core.ops.control_flow.ControlFlow B C
| Break : B → core.ops.control_flow.ControlFlow B C

@[rust_trait "core::ops::try_trait::Try" (parentClauses := ["FromResidualInst"])]
structure core.ops.try_trait.Try (Self Output Residual : Type) where
  FromResidualInst : core.ops.try_trait.FromResidual Self Residual
  from_output : Output → Result Self
  branch : Self → Result (core.ops.control_flow.ControlFlow Residual Output)

@[rust_trait "core::ops::try_trait::Residual" (parentClauses := ["TryInst"])]
structure core.ops.try_trait.Residual (Self O TryType: Type) where
  TryInst : core.ops.try_trait.Try TryType O Self

namespace Std

namespace Aeneas
