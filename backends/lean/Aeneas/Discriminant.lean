import Lean
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Notations

namespace Aeneas

open Lean Elab Term Meta
open Lean.Parser.Term Command

namespace Std

/-- This typeclass models the discriminant reads which sometimes happen in Rust -/
class Discriminant (α : Type u) (β : outParam (Type v)) where
  read_discriminant : α → β

export Discriminant (read_discriminant)

end Std

namespace Discriminant

initialize registerTraceClass `Discriminant

inductive ScalarTy where
| U8 | U16 | U32 | U64 | U128 | Usize
| I8 | I16 | I32 | I64 | I128 | Isize

def mkScalarValue (ty : ScalarTy) (val : Nat) : TermElabM Term := do
  let value := Syntax.mkNumLit (toString val)
  match ty with
  | .U8 => `($(value)#u8)
  | .U16 => `($(value)#u16)
  | .U32 => `($(value)#u32)
  | .U64 => `($(value)#u64)
  | .U128 => `($(value)#u128)
  | .Usize => `($(value)#usize)
  | .I8 => `($(value)#i8)
  | .I16 => `($(value)#i16)
  | .I32 => `($(value)#i32)
  | .I64 => `($(value)#i64)
  | .I128 => `($(value)#i128)
  | .Isize => `($(value)#isize)

def mkScalarTy (ty : ScalarTy) : TermElabM Term := do
  match ty with
  | .U8 => `(_root_.Aeneas.Std.U8)
  | .U16 => `(_root_.Aeneas.Std.U16)
  | .U32 => `(_root_.Aeneas.Std.U32)
  | .U64 => `(_root_.Aeneas.Std.U64)
  | .U128 => `(_root_.Aeneas.Std.U128)
  | .Usize => `(_root_.Aeneas.Std.Usize)
  | .I8 => `(_root_.Aeneas.Std.I8)
  | .I16 => `(_root_.Aeneas.Std.I16)
  | .I32 => `(_root_.Aeneas.Std.I32)
  | .I64 => `(_root_.Aeneas.Std.I64)
  | .I128 => `(_root_.Aeneas.Std.I128)
  | .Isize => `(_root_.Aeneas.Std.Isize)

/-- Auxiliary helper for `generateReadDiscriminant`.

This function is adapted from `Lean.Elab.Deriving.BEq`.
-/
def generateReadDiscriminantCmds (declName : Name) (ty : ScalarTy) (discrValues : Option (List Nat)) :
  TermElabM (List Syntax) := do
  -- Lookup the declaration, which should be an inductive
  let env ← getEnv
  let some decl := env.findAsync? declName
    | throwError "Could not find declaration {declName}"
  let indVal ← match decl.constInfo.get with
    | .inductInfo const => pure const
    | _ => throwError "Declaration is not an inductive: {declName}"

  /- We try to piggyback as much as possible on the utilities introducing for `deriving`.
  In particular, the following helper generates the parameter names and binders we need.

  The only caveat is that it introduces typeclass instances for the generic types.
  For instance, if we give it type `inductive Foo (α β : Type)` it will generate binders:
  `{α β : Type} [Discriminant α] [Discriminant β] (x : Foo α β)`
  Because of this, we need to update the binders to drop `[Discriminant α]` and `[Discriminant β]`
  (TODO: this is rather inelegant).
  -/
  let header ← Lean.Elab.Deriving.mkHeader ``Std.Discriminant 2 indVal
  trace[Discriminant] "numParams: {indVal.numParams}"
  let header : Deriving.Header :=
    let binders := header.binders
    let binders := binders.extract 0 indVal.numParams ++ [binders[binders.size - 2]!]
    { header with binders }

  -- Generate the value of the discriminant for each variant
  let discrValues ← do
    match discrValues with
    | none => pure (indVal.ctors.mapIdx (fun n _ => n))
    | some values =>
      if values.length ≠ indVal.ctors.length then
        throwError "Invalid number of values provided ({discrValues}): got {values.length}, expected {indVal.ctors.length}"
      pure values

  -- Generate the match branches
  let alts : List (TSyntax `Lean.Parser.Term.matchAltExpr) ←
    indVal.ctors.mapIdxM fun i ctorName => do
    let ctorInfo ← getConstInfoCtor ctorName
    let value ← mkScalarValue ty discrValues[i]!
    let alt ← do
      -- Generate one `_` pattern for each index then for each field
      let mut patterns := #[]
      for _ in 0...(indVal.numIndices + ctorInfo.numFields) do
        patterns := patterns.push (← `(_))
      let pat ← `($(mkIdent ctorName):ident $patterns:term*)
      `(matchAltExpr| | $pat => $value:term)
    pure alt
  let alts := alts.toArray

  -- Generate the match itself
  let varName := header.targetNames[0]!
  let discr : TSyntax ``Parser.Term.matchDiscr ←
    `(Parser.Term.matchDiscr| $(mkIdent varName):term)
  let discrs : Array (TSyntax `Lean.Parser.Term.matchDiscr) := #[discr]
  let body ← `(match $[$discrs],* with $alts:matchAlt*)

  -- Generate the syntax for function definition
  let ty ← mkScalarTy ty
  let auxFunName := Name.mkStr declName "read_discriminant"
  let binders := header.binders
  let defStx ← `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $ty := $body:term)

  -- Generate the syntax for the instance
  let binders := binders.extract 0 indVal.numParams
  let args := header.argNames.map mkIdent
  let instStx ← `(instance $binders:bracketedBinder* : Aeneas.Std.Discriminant ($header.targetType) ($ty) where
      read_discriminant := @$(mkIdent auxFunName):ident $args*)

  --
  pure [defStx, instStx]

/-- Given an inductive declaration name and an optional list of values, generate an instance
of `Std.Discriminant`. If the list of values is not provided, we use values `0`, `1`, etc. -/
def generateReadDiscriminant (declName : Name) (ty : ScalarTy) (discrValues : Option (List Nat)) :
  CommandElabM Unit := do
  let cmds ← liftTermElabM (generateReadDiscriminantCmds declName ty discrValues)
  cmds.forM elabCommand

syntax (name := typeToken) ("u8" <|> "u16" <|> "u32" <|> "u64" <|> "u128" <|> "usize" <|>
                            "i8" <|> "i16" <|> "i32" <|> "i64" <|> "i128" <|> "isize") : term

syntax (name := readDiscriminant) "discriminant" typeToken ("["num,*"]")? : attr

def elabTypeToken (stx : Syntax) : AttrM ScalarTy :=
  match stx with
  | .node _ `token.u8 _ => pure ScalarTy.U8
  | .node _ `token.u16 _ => pure ScalarTy.U16
  | .node _ `token.u32 _ => pure ScalarTy.U32
  | .node _ `token.u64 _ => pure ScalarTy.U64
  | .node _ `token.u128 _ => pure ScalarTy.U128
  | .node _ `token.usize _ => pure ScalarTy.Usize
  | .node _ `token.i8 _ => pure ScalarTy.I8
  | .node _ `token.i16 _ => pure ScalarTy.I16
  | .node _ `token.i32 _ => pure ScalarTy.I32
  | .node _ `token.i64 _ => pure ScalarTy.I64
  | .node _ `token.i128 _ => pure ScalarTy.I128
  | .node _ `token.isize _ => pure ScalarTy.Isize
  | _ => throwUnsupportedSyntax

def elabReadDiscriminantAttribute (stx : Syntax) : AttrM (ScalarTy × Option (List Nat)) :=
  withRef stx do
    match stx with
    | `(attr| discriminant $ty) => do
      trace[Discriminant] "Elaborating discriminant attribute without values"
      pure (← elabTypeToken ty, none)
    | `(attr| discriminant $ty [$x,*]) => do
      trace[Discriminant] "Elaborating discriminant attribute with values: {x.getElems}"
      pure (← elabTypeToken ty, some ((x.getElems.toList.map Syntax.isNatLit?).map Option.get!))
    | _ => throwUnsupportedSyntax

initialize discriminantAttribute : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    name := `readDiscriminant
    descr := "Generates an instance of `Std.Discriminant` for the given inductive"
    add := fun declName stx attrKind => do
      -- Elaborate the attribute
      let (ty, values) ← elabReadDiscriminantAttribute stx
      -- Generate the definitions
      liftCommandElabM (generateReadDiscriminant declName ty values)
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

namespace Test

  open Std

  mutual

  inductive Foo (α β : Type) where
  | Bar (y : Nat)
  | Baz (x : α) (y : β)

  inductive Foo1 (α β : Type) where
  | Variant1 | Variant2

  end

  inductive Foo2 where
  | Variant1
  | Variant2

  inductive Foo3 where
  | Variant1
  | Variant2

  #eval generateReadDiscriminant ``Foo .U8 (some [3, 4])
  #eval generateReadDiscriminant ``Foo1 .I8 none
  #eval generateReadDiscriminant ``Foo2 .I16 none
  #eval generateReadDiscriminant ``Foo3 .Isize (some [3, 4])

  #assert read_discriminant Foo2.Variant1 = 0#i16
  #assert read_discriminant Foo3.Variant1 = 3#isize
  #assert read_discriminant Foo3.Variant2 = 4#isize

end Test

end Discriminant

end Aeneas
