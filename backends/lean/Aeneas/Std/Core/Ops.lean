module
public import Lean
public meta import Aeneas.Extract.Extract
public import Aeneas.Std.Primitives
public section

namespace Aeneas

namespace Std

open Result

@[rust_trait "core::ops::index::Index"]
structure core.ops.index.Index (Self Idx Output : Type _) where
  index : Self → Idx → Result Output

@[rust_trait "core::ops::index::IndexMut" (parentClauses := ["indexInst"])]
structure core.ops.index.IndexMut (Self Idx Output : Type _) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → Result (Output × (Output → Self))

@[rust_trait "core::ops::deref::Deref"]
structure core.ops.deref.Deref (Self Target : Type _) where
  deref : Self → Result Target

@[rust_trait "core::ops::deref::DerefMut" (parentClauses := ["derefInst"])]
structure core.ops.deref.DerefMut (Self Target : Type _) where
  derefInst : Deref Self Target
  deref_mut : Self → Result (Target × (Target → Self))

@[rust_trait "core::ops::arith::Add"]
structure core.ops.arith.Add (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  add : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::arith::Sub"]
structure core.ops.arith.Sub (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  sub : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::arith::Mul"]
structure core.ops.arith.Mul (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  mul : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::arith::Div"]
structure core.ops.arith.Div (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  div : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::bit::BitAnd"]
structure core.ops.bit.BitAnd (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  bitand : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::bit::BitOr"]
structure core.ops.bit.BitOr (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  bitor : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::bit::BitXor"]
structure core.ops.bit.BitXor (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  bitxor : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::bit::Shl"]
structure core.ops.bit.Shl (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  shl : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::bit::Shr"]
structure core.ops.bit.Shr (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  shr : Self → Rhs → Result Self_Output

@[rust_trait "core::ops::arith::AddAssign"]
structure core.ops.arith.AddAssign (Self : Type _) (Rhs : Type _) where
  add_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::arith::SubAssign"]
structure core.ops.arith.SubAssign (Self : Type _) (Rhs : Type _) where
  sub_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::arith::MulAssign"]
structure core.ops.arith.MulAssign (Self : Type _) (Rhs : Type _) where
  mul_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::arith::DivAssign"]
structure core.ops.arith.DivAssign (Self : Type _) (Rhs : Type _) where
  div_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::bit::BitAndAssign"]
structure core.ops.bit.BitAndAssign (Self : Type _) (Rhs : Type _) where
  bitand_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::bit::BitOrAssign"]
structure core.ops.bit.BitOrAssign (Self : Type _) (Rhs : Type _) where
  bitor_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::bit::BitXorAssign"]
structure core.ops.bit.BitXorAssign (Self : Type _) (Rhs : Type _) where
  bitxor_assign : Self → Rhs → Result Self

@[rust_trait "core::ops::drop::Drop"]
structure core.ops.drop.Drop (Self : Type _) where
  drop : Self → Result Self

@[expose, rust_fun "core::ops::drop::Drop::drop"]
def core.ops.drop.Drop.drop.default {Self : Type _}
    (DropInst : core.ops.drop.Drop Self) : Self → Result Self :=
  fun s => DropInst.drop s

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
  call_mut f x := do
    bind (f x) λ v =>
    ok (v, f)
}

def BuiltinFn (Inputs : Type u) (Outputs : Type v) : core.ops.function.Fn (Inputs → Result Outputs) Inputs Outputs := {
  FnMutInst := BuiltinFnMut Inputs Outputs
  call f x := f x
}

@[rust_trait "core::ops::try_trait::FromResidual"]
structure core.ops.try_trait.FromResidual (Self : Type u) (R : Type v) where
  from_residual : R → Result Self

@[rust_type "core::ops::control_flow::ControlFlow"]
inductive core.ops.control_flow.ControlFlow (B : Type _) (C : Type _) where
| Continue : C → core.ops.control_flow.ControlFlow B C
| Break : B → core.ops.control_flow.ControlFlow B C

@[rust_trait "core::ops::try_trait::Try" (parentClauses := ["FromResidualInst"])]
structure core.ops.try_trait.Try (Self Output Residual : Type _) where
  FromResidualInst : core.ops.try_trait.FromResidual Self Residual
  from_output : Output → Result Self
  branch : Self → Result (core.ops.control_flow.ControlFlow Residual Output)

@[rust_trait "core::ops::try_trait::Residual" (parentClauses := ["TryInst"])]
structure core.ops.try_trait.Residual (Self O TryType: Type _) where
  TryInst : core.ops.try_trait.Try TryType O Self

namespace Std

namespace Aeneas
