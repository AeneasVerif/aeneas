import Aeneas.SimpIfs.Init
import Aeneas.ScalarTac.CondSimpTac

/-!
# `simp_ifs` tactic

The `simp_ifs` tactic is used to simplify expressions `if then else` expressions
-/

namespace Aeneas.SimpIfs

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

structure Args where
  declsToUnfold : Array Name := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def simpIfsTac (args : Args) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpIfsSimpExt.getTheorems],
      simprocs := #[← simpIfsSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_ifs" {maxDischargeDepth := 2, failIfUnchanged := false} args addSimpThms false loc

syntax (name := simp_ifs) "simp_ifs" ("[" term,* "]")? (location)? : tactic

@[simp_ifs_simps]
theorem if_true {α} (b : Prop) [Decidable b] (x y : α) (hb : b) : (if b then x else y) = x := by
  simp only [hb, ↓reduceIte]

@[simp_ifs_simps]
theorem if_false {α} (b : Prop) [Decidable b] (x y : α) (hb : ¬ b) : (if b then x else y) = y := by
  simp only [hb, Bool.false_eq_true, ↓reduceIte]

def parseArgs (args : Array (TSyntax `term)) : TacticM Args := do
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
        trace[SimpIfs] "arg (local decl): {stx.raw}"
        -- Local declarations should be assumptions
        hypsToUse := hypsToUse.push decl.fvarId
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[SimpIfs] "arg (theorem): {stx.raw}"
        let some e ← Lean.Elab.Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {arg}"
        if let .const name _ := e then
          addSimpThms := addSimpThms.push name
        else throwError m!"Unexpected: {arg}"
    | term => do
      -- TODO: we need to make that work
      trace[SimpIfs] "arg (term): {term}"
      throwError m!"Unimplemented: arbitrary terms are not supported yet as arguments to `simp_ifs` (received: {arg})"
  pure ⟨ declsToUnfold, addSimpThms, hypsToUse ⟩

def parseSimpIfs : TSyntax ``simp_ifs -> TacticM (Args × Utils.Location)
| `(tactic| simp_ifs $[[$args,*]]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← parseArgs args
  pure (args, Utils.Location.targets #[] true)
| `(tactic| simp_ifs $[[$args,*]]? $[$loc:location]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← parseArgs args
  let loc ← Utils.parseOptLocation loc
  pure (args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_ifs : tactic =>
  withMainContext do
  let (args, loc) ← parseSimpIfs stx
  simpIfsTac args loc

example [Inhabited α] (i j : Nat) (h :i ≥ j ∧ i < j + 1) : (if i = j then 0 else 1) = 0 := by
  simp_ifs

end Aeneas.SimpIfs
