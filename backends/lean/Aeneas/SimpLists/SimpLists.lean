import Aeneas.SimpLists.Init
import Aeneas.ScalarTac.CondSimpTac

/-!
# `simp_lists` tactic

The `simp_lists` tactic is used to simplify expressions using lists, such as nested
List `get` and `set`.
-/

namespace Aeneas.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

attribute [simp_lists_simps]
  add_tsub_cancel_right add_tsub_cancel_left Bool.false_or Bool.or_false
  implies_true

structure Args where
  declsToUnfold : Array Name := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def simpListsTac (args : Args) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpListsSimpExt.getTheorems],
      simprocs := #[← simpListsSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_lists" {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} args addSimpThms false loc

syntax (name := simp_lists) "simp_lists" ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseArgs (args : TSyntaxArray [`term, `token.«*»]) : TacticM Args := do
  let mut declsToUnfold := #[]
  let mut addSimpThms := #[]
  let mut hypsToUse := #[]
  for arg in args do
    /- We have to make a case disjunction, because if we treat identifiers like
       terms, then Lean will not succeed in infering their implicit parameters. -/
    match arg with
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[SimpLists] "arg (local decl): {stx.raw}"
        -- Local declarations should be assumptions
        hypsToUse := hypsToUse.push decl.fvarId
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[SimpLists] "arg (theorem): {stx.raw}"
        let some e ← Lean.Elab.Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {arg}"
        if let .const name _ := e then
          addSimpThms := addSimpThms.push name
        else throwError m!"Unexpected: {arg}"
    | term => do
      trace[SimpLists] "term kind: {term.raw.getKind}"
      if term.raw.getKind == `token.«*» then
        trace[SimpLists] "found token: *"
        let decls ← (← getLCtx).getDecls
        let decls ← decls.filterMapM (
          fun d => do if (← inferType d.type).isProp then pure (some d.fvarId) else pure none)
        trace[SimpLists] "filtered decls: {decls.map Expr.fvar}"
        hypsToUse := hypsToUse.append decls.toArray
      else
        -- TODO: we need to make that work
        trace[SimpLists] "arg (term): {term}"
        throwError m!"Unimplemented: arbitrary terms are not supported yet as arguments to `simp_lists` (received: {arg})"
  pure ⟨ declsToUnfold, addSimpThms, hypsToUse ⟩

def parseSimpLists : TSyntax ``simp_lists -> TacticM (Args × Utils.Location)
| `(tactic| simp_lists $[[$args,*]]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← parseArgs args
  pure (args, Utils.Location.targets #[] true)
| `(tactic| simp_lists $[[$args,*]]? $[$loc:location]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← parseArgs args
  let loc ← Utils.parseOptLocation loc
  pure (args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic =>
  withMainContext do
  let (args, loc) ← parseSimpLists stx
  simpListsTac args loc

end Aeneas.SimpLists
