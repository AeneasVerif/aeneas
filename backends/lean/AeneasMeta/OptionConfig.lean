import Lean
import Lean.Elab.Tactic.Config
import Lean.Elab.Eval

namespace Aeneas.Meta.OptionConfig

open Lean Elab Command Term Meta PrettyPrinter

/-!
# `decomposeOptConfig`
-/

/-- Decompose a `Lean.Parser.Tactic.optConfig` into an array of (fieldName, valueSyntax) pairs.

For instance: with input `+b (value := 3) -c`, it outputs: `#[("b", true), (value, 3), ("c", false)]` -/
partial def decomposeOptConfig (cfg : TSyntax `Lean.Parser.Tactic.optConfig) : Array (Name × Syntax) :=
  go cfg.raw #[]
where
  go (s : Syntax) (acc : Array (Name × Syntax)) : Array (Name × Syntax) :=
    match s with
    | .node _ `Lean.Parser.Tactic.posConfigItem #[_, name] =>
      if name.isIdent then acc.push (name.getId, mkIdent `true) else acc
    | .node _ `Lean.Parser.Tactic.negConfigItem #[_, name] =>
      if name.isIdent then acc.push (name.getId, mkIdent `false) else acc
    | .node _ `Lean.Parser.Tactic.valConfigItem #[_, name, _, val, _] =>
      if name.isIdent then acc.push (name.getId, val) else acc
    | .node _ _ children => children.foldl (fun a c => go c a) acc
    | _ => acc

-- ---------------------------------------------------------------------------
-- Tests for decomposeOptConfig
-- ---------------------------------------------------------------------------

/-!
# Tests for `decomposeOptConfig`
-/
section DecomposeOptConfigTests

/-- Tactic that prints each config entry it receives. -/
local elab "test_config" cfg:Lean.Parser.Tactic.optConfig : tactic => do
  let entries := decomposeOptConfig cfg
  if entries.isEmpty then
    Lean.logInfo "No config entries."
  else
    for (name, val) in entries do
      Lean.logInfo m!"{name} := {val}"

/--
info: foo := false
---
info: bar := 42
---
info: baz := true
-/
#guard_msgs in
example : True := by
  test_config -foo (bar := 42) +baz
  trivial

end DecomposeOptConfigTests

/-!
# `declare_partial_config_elab`

This is similar to `declare_config_elab` with the tweak that it allows registering
default values by using global options.

More precisely, given a structure:
```lean
structure Config where
  n : Nat  := 3
  b : Bool := false
```

The command `declare_partial_config_elab Config elabConfig optionPrefix` generates:
1. for each field `f : T` of `Config`, evaluates the command `register_option tacticName.f : T`, using
   the default value of `f` as the default value of the option.
   In the present case, it will do:
   ```
   register_option tacticName.n { defValue := 3 }
   register_option tacticName.b { defValue := false }
   ```
2. an elaborator `def elabConfig (cfg : TSyntax Lean.Parser.Tactic.optConfig) : TermElabM Config`
   This elaborator uses the default values stored in the options `tacticName.n` and `tacticName.b` to fill the
   fields not provided by the user.
-/

/--
Given a structure name, output the array (fieldName, fieldType, defaultValue)
-/
private def collectFieldInfo (structName : Name) :
    MetaM (Array (Name × Expr × Expr)) := do
  let env ← getEnv
  let some si := getStructureInfo? env structName
    | throwError "not a structure: {structName}"
  let mut out : Array (Name × Expr × Expr) := #[]
  for field in si.fieldNames do
    let some defFnName := getDefaultFnForField? env structName field
      | throwError "field '{structName}.{field}' has no default value"
    let defFnInfo ← getConstInfo defFnName
    let defVal    ← reduce (mkConst defFnName)
    out := out.push (field, defFnInfo.type, defVal)
  return out

/-- -/
syntax (name := declarePartialConfigElab)
  "declare_option_config_elab" ident ident ident : command


/-- -/
elab_rules : command
  | `(declare_option_config_elab $structId $elabFnId $optPrefixId) => do
    let ns         ← getCurrNamespace
    let structName := ns ++ structId.getId
    let elabFnName := elabFnId.getId
    let optPrefix  := optPrefixId.getId

    let fields ← liftTermElabM (collectFieldInfo structName)

    /- **1. Register the options** -/
    for (field, ty, defVal) in fields do
      let optName := optPrefix ++ field
      let alreadyExists ← pure ((← getOptionDecls).contains optName)
      if alreadyExists then throwError "Option {optName} already exists"
      let tySx  : Term ← liftTermElabM (delab ty)
      let defSx : Term ← liftTermElabM (delab defVal)
      let descr := "Default value for field " ++ structName.toString ++ "." ++ field.toString
      elabCommand (← `(command|
        initialize $(mkIdent optName) : Lean.Option $tySx ←
          Lean.Option.register $(Lean.quote optName)
            { defValue := $defSx, descr := $(Lean.quote descr) }))


    /- **2. Public elaborator** -/
    let helperTy    : Term ← `(Lean.Elab.Term.TermElabM $(mkIdent structName))
    let optConfigTy : Term ← `(Lean.TSyntax `Lean.Parser.Tactic.optConfig)
    let implName     := elabFnName ++ `impl
    let structNameQ  : Term := Lean.quote structName

    /- For each field f, generate:
    ```
    f_opt : Term ← delab (toExpr (Option.get opts optName)) -- fallback: read the option
    f : Term :=
      match pairs.find? field with
      | some (_, valStx) => ⟨valStx⟩ -- use the user provided value
      | none             => f        -- fallback: read the default value stored in the option
    ```
    -/
    let readOptName     : Array Name ← fields.mapM (fun (name, _) => liftCoreM (mkFreshUserName (Name.mkSimple (name.toString ++ "_opt"))))
    let fieldValueName  : Array Name ← fields.mapM (fun (name, _ ) => liftCoreM (mkFreshUserName name))

    -- Per-field fallback: Term for `Option.get opts optName` (typed value)
    let readOptBindings : Array Term ← fields.mapIdxM fun i (_, _, _) => do
      let (field, _, _) := fields[i]!
      let optName := optPrefix ++ field
      `(Lean.Option.get opts $(mkIdent optName))

    -- Per-field final value: picks user Syntax or fallback Term
    let fieldValExprs : Array Term ← fields.mapIdxM fun i (field, _, _) => do
      let fieldQ : Term := Lean.quote field
      let fbId   : Term := mkIdent readOptName[i]!
      `(match (pairs.find? fun p => p.1 == $fieldQ) with
        | some (_, valStx) => TSyntax.mk valStx
        | none             => $fbId)

    -- Put the field values together to create the structure (i.e., the `⟨f0, …, fn⟩` expression)
    let fieldValues : Array Term := fieldValueName.map fun n => (mkIdent n : Term)
    /- We build some syntax that has to be evaluated at runtime.
       More precisely, we emit: `Lean.Syntax.mkApp (mkIdent ``MyConfig.mk) (Array.mk [f0, …, fn])` -/
    let ctorQ : Term := Lean.quote (structName ++ `mk)
    let structLit : Term ← `(Lean.Syntax.mkApp (Lean.mkIdent $ctorQ) (Array.mk [$fieldValues,*]))

    -- Create the do elements for the let-bidnings
    let fieldValBinds : Array (TSyntax `Lean.Parser.Term.doSeqItem) ←
      (fieldValueName.zip fieldValExprs).mapM fun (fieldVaName, rhs) =>
        `(Lean.Parser.Term.doSeqItem| let $(mkIdent fieldVaName) : Lean.Term := $rhs)
    let readOptBinds : Array (TSyntax `Lean.Parser.Term.doSeqItem) ←
      (readOptName.zip readOptBindings).mapM fun (readOptName, rhs) =>
        `(Lean.Parser.Term.doSeqItem|
            let $(mkIdent readOptName) : Lean.Term ←
              Lean.PrettyPrinter.delab (Lean.toExpr $rhs))

    /- Put everything together by generating the body of the elaborator method -/
    let implBody : Term ← `(do
      let pairs := decomposeOptConfig cfg
      let opts  ← Lean.getOptions
      -- let f_opt ← liftM (delab (toExpr (Lean.Option.get opts optionPrefix.fi)))
      $[$(readOptBinds)]*
      /- let f : Term :=
            match Array.find? (fun p => p.fst == `f) pairs with
            | some (fst, valStx) => { raw := valStx }
            | none => f_opt -/
      $[$(fieldValBinds)]*
      --
      let ty   := Lean.mkConst $structNameQ
      -- structLit is the expression: ⟨ f0, ..., fn ⟩
      let expr ← Lean.Elab.Term.elabTermEnsuringType $structLit ty
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← Lean.instantiateMVars expr
      Lean.Meta.evalExpr $(mkIdent structName) ty expr)

    /- We need to use `evalExpr` to evaluate the syntax into a value, but this function is unsafe.
      In order not to have to declare our elaboration as unsafe, we do it in two steps:
      ```
      private unsafe def elabConfig.impl (cfg : TSyntax `Lean.Parser.Tactic.optConfig) : TermElabM Config :=
        ... -- call `evalExpr`

      @[implemented_by elabConfig.impl]
      opaque elabConfig : TSyntax `Lean.Parser.Tactic.optConfig → TermElabM Config
      ```
     -/
    elabCommand (← `(command|
      private unsafe def $(mkIdent implName)
          (cfg : $optConfigTy) : $helperTy := $implBody))
    elabCommand (← `(command|
      @[implemented_by $(mkIdent implName)]
      opaque $(mkIdent elabFnName)
          (cfg : $optConfigTy) : $helperTy))

/-!
# Tests
-/
namespace Example

structure Config where
  n    : Nat    := 3
  b    : Bool   := false
  name : String := "hello"

declare_option_config_elab Config elabConfig exampleOptionPrefix

/--
info: opaque Aeneas.Meta.OptionConfig.Example.elabConfig : TSyntax `Lean.Parser.Tactic.optConfig → TermElabM Config
-/
#guard_msgs in
#print elabConfig

/--
info: unsafe private def Aeneas.Meta.OptionConfig.Example.elabConfig.impl : TSyntax `Lean.Parser.Tactic.optConfig →
  TermElabM Config :=
fun cfg =>
  let pairs := decomposeOptConfig cfg;
  do
  let opts ← getOptions
  let n_opt ← liftM (delab (toExpr (Lean.Option.get opts exampleOptionPrefix.n)))
  let b_opt ← liftM (delab (toExpr (Lean.Option.get opts exampleOptionPrefix.b)))
  let name_opt ← liftM (delab (toExpr (Lean.Option.get opts exampleOptionPrefix.name)))
  let n : Term :=
    match Array.find? (fun p => p.fst == `n) pairs with
    | some (fst, valStx) => { raw := valStx }
    | none => n_opt
  let b : Term :=
    match Array.find? (fun p => p.fst == `b) pairs with
    | some (fst, valStx) => { raw := valStx }
    | none => b_opt
  let name : Term :=
    match Array.find? (fun p => p.fst == `name) pairs with
    | some (fst, valStx) => { raw := valStx }
    | none => name_opt
  let ty : Expr := Lean.mkConst `Aeneas.Meta.OptionConfig.Example.Config
  let expr ←
    elabTermEnsuringType
        (Syntax.mkApp { raw := (mkIdent `Aeneas.Meta.OptionConfig.Example.Config.mk).raw }
            { toList := [n, b, name] }).raw
        (some ty)
  synthesizeSyntheticMVarsNoPostponing
  let expr ← instantiateMVars expr
  liftM (evalExpr Config ty expr)
-/
#guard_msgs in
#print elabConfig.impl

end Example

end Aeneas.Meta.OptionConfig
