import Aeneas.GrindSimpTac.GrindSimpTac
import Aeneas.Bvify.Bvify
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.Grind.Init

/-!
# `gbvify`: like `bvify` but using `grind` as a discharger

Built on top of `grindSimpTac`.
-/

namespace Aeneas.GrindSimpTac.Bvify

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac
open Aeneas.Bvify

syntax (name := gsimp_lists) "gbvify" colGt term "only"? simpArgs (location)? : tactic
syntax (name := gsimp_lists?) "gbvify?" colGt term "only"? simpArgs (location)? : tactic

private def gbvifyElab (qmark : Bool)
  (n : Expr)
  (onlyTk : Option Syntax)
  (simpArgsStx : Option (TSyntax ``simpArgs))
  (loc : Option (TSyntax `Lean.Parser.Tactic.location))
  (stx : stx)
  : TacticM Unit := do
  withMainContext do
  let loc ← Utils.parseOptLocation loc
  let «only» := onlyTk.isSome
  let simpThms ← bvifySimpExt.getTheorems
  let simprocs ← bvifySimprocExt.getSimprocs
  let hypsSimpThms ← bvifyHypsSimpExt.getTheorems
  let hypsSimprocs ← bvifyHypsSimprocExt.getSimprocs
  let addSimpThms := bvifyAddSimpThms n
  standardGrindSimpTac loc «only» (simpThms, simprocs)
    (hypsSimpThms, hypsSimprocs) simpArgsStx addSimpThms

elab_rules : tactic
  | `(tactic| gbvify $n $[only%$onlyTk]? $args $[$loc:location]?) => do
    let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
    gbvifyElab false n onlyTk args loc (← getRef)
  | `(tactic| gbvify? $n $[only%$onlyTk]? $args $[$loc:location]?) => do
    let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
    gbvifyElab true n onlyTk args loc (← getRef)

/-
open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac (GrindSimpArgs grindSimpTac)
open Aeneas.Bvify (bvifyAddSimpThms bvifySimpExt bvifySimprocExt
  bvifyHypsSimpExt bvifyHypsSimprocExt)

def gbvifyTac (n : Expr) (loc : Utils.Location)
    («only» : Bool := false) (args : ScalarTac.CondSimpPartialArgs := {})
    (suggestion : Option (Syntax × String × String) := none) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  -- Add bvify-specific theorems instantiated with `n`
  let addedFVars ← bvifyAddSimpThms n
  let simpThms ← if «only» then pure #[] else
    pure #[← bvifySimpExt.getTheorems,
           ← SimpBoolProp.simpBoolPropSimpExt.getTheorems]
  let simprocs ← if «only» then pure #[] else
    pure #[← bvifySimprocExt.getSimprocs,
           ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs]
  let simpArgs : GrindSimpArgs := {
    simpThms, simprocs,
    declsToUnfold := args.declsToUnfold,
    addSimpThms := args.addSimpThms,
    addSimprocs := args.addSimprocs,
    hypsToUse := addedFVars ++ args.hypsToUse,
  }
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 5, splitMatch := false, splitIte := false,
    splitIndPred := false, funext := false, gen := 2, instances := 1000,
    canonHeartbeats := 1000
  }
  let extensions := #[Grind.agrindExt.getState (← getEnv)]
  grindSimpTac grindConfig (withGroundSimprocs := true) extensions
    { maxDischargeDepth := 2, failIfUnchanged := false, contextual := true }
    simpArgs loc
    (preprocessSimpThms := #[← ScalarTac.scalarTacSimpExt.getTheorems,
                              ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessSimprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs,
                              ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (preprocessHypsToUseSimpThms := #[← bvifyHypsSimpExt.getTheorems,
                                       ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessHypsToUseSimprocs := #[← bvifyHypsSimprocExt.getSimprocs,
                                       ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (genPreprocess := some 2)
    (suggestion := suggestion)
  -- Clear the added theorems from the remaining goal (if any)
  if (← getUnsolvedGoals).length > 0 then
    setGoals [← (← getMainGoal).tryClearMany addedFVars]

private def locToString (loc : Utils.Location) : MetaM String :=
  match loc with
  | .wildcard => return "at *"
  | .targets _ true => return "at *"
  | .targets hyps false =>
    if hyps.isEmpty then return ""
    else do
      let lctx ← getLCtx
      let names := hyps.toList.filterMap fun fv =>
        (lctx.find? fv).map (toString ·.userName)
      return s!"at {" ".intercalate names}"

syntax (name := gbvify) "gbvify" colGt term "only"? ("[" (simpLemma<|>"*"),* "]")? (location)? : tactic
syntax (name := gbvify?) "gbvify?" colGt term "only"? ("[" (simpLemma<|>"*"),* "]")? (location)? : tactic

/-- Extract the core term from a `simpLemma` or `*` entry, stripping any `↓`/`↑`/`←` prefixes. -/
private def extractSimpLemmaTerms (args : Array Syntax) : TSyntaxArray [`term, `token.«*»] :=
  args.map fun arg =>
    if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
      ⟨arg[2]⟩  -- The term part of simpLemma
    else
      ⟨arg⟩  -- `*` token

private def gbvifyElab (qmark : Bool) (nStx : TSyntax `term) (onlyTk : Option Syntax)
    (uargs : Option (Syntax.TSepArray [`Lean.Parser.Tactic.simpLemma, `token.«*»] ","))
    (loc : Option (TSyntax `Lean.Parser.Tactic.location)) (stx : Syntax) : TacticM Unit := do
  let n ← Elab.Term.elabTerm nStx (Expr.const ``Nat [])
  let loc ← Utils.parseOptLocation loc
  let rawArgs := uargs.map (·.getElems) |>.getD #[]
  let rawArgs := extractSimpLemmaTerms rawArgs
  let parsedArgs ← ScalarTac.condSimpParseArgs "gbvify" rawArgs
  let «only» := onlyTk.isSome
  let suggestion ← if qmark then do
    let locStr ← locToString loc
    -- Format the bit-width nicely (numeric literal → plain number, otherwise raw syntax)
    let nStr := match nStx.raw.isNatLit? with
      | some n => s!"{n}"
      | none => s!"{nStx}"
    pure (some (stx, s!"gbvify {nStr}", locStr))
  else pure none
  gbvifyTac n loc («only» := «only») (args := parsedArgs) (suggestion := suggestion)

elab_rules : tactic
  | `(tactic| gbvify $n:term $[only%$onlyTk]? $[[$uargs,*]]? $[$loc:location]?) => do
    gbvifyElab false n onlyTk uargs loc (← getRef)
  | `(tactic| gbvify? $n:term $[only%$onlyTk]? $[[$uargs,*]]? $[$loc:location]?) => do
    gbvifyElab true n onlyTk uargs loc (← getRef)-/

end Aeneas.GrindSimpTac.Bvify
