import Aeneas.Std.Vec
import Aeneas.Std.Scalar.Fmt

/-! # Tests for the automatic trait-instance registration

Definitions carrying the `@[rust_trait_impl]` attribute are automatically
registered in the trait-instance registry (see `Aeneas.TraitInst`), so that
they can be referred to with the `{Trait for Type}` notation. -/

namespace Aeneas.Std.TraitInstTests

open Aeneas.TraitInst

/- The `Clone` impl for `Vec` is auto-registered, with the binder `T` as a
   pattern variable. -/
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some instId := findInstIdByDecl env ``core.clone.CloneallocvecVec
    | throwError "core.clone.CloneallocvecVec is not registered"
  unless instId.traitId == ``core.clone.Clone do
    throwError "unexpected trait: {instId}"

-- The notation resolves to the registered Std impls
example : {core.clone.Clone for alloc.vec.Vec<_>} = @core.clone.CloneallocvecVec := rfl
example : {core.fmt.Debug for U32} = core.fmt.DebugU32 := rfl

/-! Full instantiation: the type arguments are elaborated and the clause
    parameters are recursively resolved through the registry. -/

example : {core.clone.Clone for Bool} = core.clone.CloneBool := rfl
example : {core.clone.Clone for alloc.vec.Vec<Bool>}
    = core.clone.CloneallocvecVec core.clone.CloneBool := rfl

/-! Local clauses shadow the registered instances (the `Clone` structure is
    marked as a trait declaration through its `rust_trait` attribute). -/

example (CloneBoolInst : core.clone.Clone Bool) :
    {core.clone.Clone for Bool} = CloneBoolInst := rfl

/-! Method calls through the notation. -/

example (v : alloc.vec.Vec Bool) :
    {core.clone.Clone for alloc.vec.Vec<Bool>}.clone v
    = (core.clone.CloneallocvecVec core.clone.CloneBool).clone v := rfl

end Aeneas.Std.TraitInstTests
