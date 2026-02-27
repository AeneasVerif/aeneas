import Aeneas.ScalarTac.CondSimpTac

namespace Aeneas.GrindSimpTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

/-- Arguments for `grindSimpTac`. Mirrors `ScalarTac.CondSimpArgs` but is kept
    separate so the two modules can evolve independently. -/
structure GrindSimpArgs where
  simpThms : Array SimpTheorems := #[]
  simprocs : Simp.SimprocsArray := #[]
  declsToUnfold : Array Name := #[]
  letDeclsToUnfold : Array FVarId := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def GrindSimpArgs.toSimpArgs (args : GrindSimpArgs) : Simp.SimpArgs := {
    simpThms := args.simpThms,
    simprocs := args.simprocs,
    declsToUnfold := args.declsToUnfold,
    letDeclsToUnfold := args.letDeclsToUnfold,
    addSimpThms := args.addSimpThms,
    hypsToUse := args.hypsToUse }

end Aeneas.GrindSimpTac
