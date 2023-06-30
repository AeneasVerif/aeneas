import Lean

namespace Diverge

open Lean Elab Term Meta

initialize registerTraceClass `Diverge.elab
initialize registerTraceClass `Diverge.def
initialize registerTraceClass `Diverge.def.sigmas
initialize registerTraceClass `Diverge.def.genBody

-- TODO: move
-- TODO: small helper
def explore_term (incr : String) (e : Expr) : MetaM Unit :=
  match e with
  | .bvar _ => do logInfo m!"{incr}bvar: {e}"; return ()
  | .fvar _ => do logInfo m!"{incr}fvar: {e}"; return ()
  | .mvar _ => do logInfo m!"{incr}mvar: {e}"; return ()
  | .sort _ => do logInfo m!"{incr}sort: {e}"; return ()
  | .const _ _ => do logInfo m!"{incr}const: {e}"; return ()
  | .app fn arg => do
    logInfo m!"{incr}app: {e}"
    explore_term (incr ++ "  ") fn
    explore_term (incr ++ "  ") arg
  | .lam _bName bTy body _binfo => do
    logInfo m!"{incr}lam: {e}"
    explore_term (incr ++ "  ") bTy
    explore_term (incr ++ "  ") body
  | .forallE _bName bTy body _bInfo => do
    logInfo m!"{incr}forallE: {e}"
    explore_term (incr ++ "  ") bTy
    explore_term (incr ++ "  ") body
  | .letE _dName ty val body _nonDep => do
    logInfo m!"{incr}letE: {e}"
    explore_term (incr ++ "  ") ty
    explore_term (incr ++ "  ") val
    explore_term (incr ++ "  ") body
  | .lit _ => do logInfo m!"{incr}lit: {e}"; return ()
  | .mdata _ e => do
    logInfo m!"{incr}mdata: {e}"
    explore_term (incr ++ "  ") e
  | .proj _ _ struct => do
    logInfo m!"{incr}proj: {e}"
    explore_term (incr ++ "  ") struct

def explore_decl (n : Name) : TermElabM Unit := do
  logInfo m!"Name: {n}"
  let env ← getEnv
  let decl := env.constants.find! n
  match decl with
  | .defnInfo val =>
     logInfo m!"About to explore defn: {decl.name}"
     logInfo m!"# Type:"
     explore_term "" val.type
     logInfo m!"# Value:"
     explore_term "" val.value
  | .axiomInfo _  => throwError m!"axiom: {n}"
  | .thmInfo _    => throwError m!"thm: {n}"
  | .opaqueInfo _ => throwError m!"opaque: {n}"
  | .quotInfo _   => throwError m!"quot: {n}"
  | .inductInfo _ => throwError m!"induct: {n}"
  | .ctorInfo _   => throwError m!"ctor: {n}"
  | .recInfo _    => throwError m!"rec: {n}"

syntax (name := printDecl) "print_decl " ident : command

open Lean.Elab.Command

@[command_elab printDecl] def elabPrintDecl : CommandElab := fun stx => do
  liftTermElabM do
    let id := stx[1]
    addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
    let cs ← resolveGlobalConstWithInfos id
    explore_decl cs[0]!

private def test1 : Nat := 0
private def test2 (x : Nat) : Nat := x

print_decl test1
print_decl test2

-- We adapted this from AbstractNestedProofs.visit
-- A map visitor function for expressions
partial def mapVisit (k : Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  let mapVisitBinders (xs : Array Expr) (k2 : MetaM Expr) : MetaM Expr := do
    let localInstances ← getLocalInstances
    let mut lctx ← getLCtx
    for x in xs do
      let xFVarId := x.fvarId!
      let localDecl ← xFVarId.getDecl
      let type      ← mapVisit k localDecl.type
      let localDecl := localDecl.setType type
      let localDecl ← match localDecl.value? with
         | some value => let value ← mapVisit k value; pure <| localDecl.setValue value
         | none       => pure localDecl
      lctx :=lctx.modifyLocalDecl xFVarId fun _ => localDecl
    withLCtx lctx localInstances k2
  -- TODO: use a cache? (Lean.checkCache)
  -- Explore
  let e ← k e
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ => pure e
  | .app .. => do e.withApp fun f args => return mkAppN f (← args.mapM (mapVisit k))
  | .lam .. =>
    lambdaLetTelescope e fun xs b =>
      mapVisitBinders xs do mkLambdaFVars xs (← mapVisit k b) (usedLetOnly := false)
  | .forallE .. => do
    forallTelescope e fun xs b => mapVisitBinders xs do mkForallFVars xs (← mapVisit k b)
  | .letE .. => do
    lambdaLetTelescope e fun xs b => mapVisitBinders xs do
      mkLambdaFVars xs (← mapVisit k b) (usedLetOnly := false)
  | .mdata _ b => return e.updateMData! (← mapVisit k b)
  | .proj _ _ b => return e.updateProj! (← mapVisit k b)

end Diverge
