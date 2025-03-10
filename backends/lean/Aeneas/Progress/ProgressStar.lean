import Lean
import Aeneas.Utils
import Aeneas.Progress.Progress
/- import Mathlib.Control.Sequence -/
open Aeneas
open Lean Meta Elab Tactic 

-- TODO: Merge with Aeneas.Diverge.Elab.isCasesExpr
def isCasesExpr [Monad m] [MonadEnv m](e : Expr) : m Bool := do
  let e := e.getAppFn
  if e.isConst then
    return isCasesOnRecursor (← getEnv) e.constName
  else return false

namespace Bifurcation/- {{{ -/
/-- Expression on which a branch depends -/
structure Discr where
  toExpr: Expr
  /-- Name under which to bind the discriminant equation, if provided -/
  name?: Option Name := none
  deriving Repr
instance: ToMessageData Discr where
  toMessageData discr := 
    let nameMD := if let some name := discr.name? then m!"(name {name }) " else ""
    m!"(discr {nameMD}{discr.toExpr})"

/-- One possible branch in a bifurcation -/
structure Branch where
  /-- The branch as a function -/
  toExpr: Expr

  /-- The number of arguments the bifurcation is 
      expected to provide. -/
  numArgs: Nat

  deriving Repr
instance: ToMessageData Branch where
  toMessageData br := m!"(branch (numArgs {br.numArgs}){br.toExpr}) "

/-- The kind of bifurcation -/
inductive Kind where
  /-- An `if-then-else` bifurcation -/
  | ite
  /-- A dependent `if-then-else` bifurcation -/
  | dite
  /-- A matcher or cases bifurcation, of name `name` -/
  | matcher (name: Name)
  deriving Repr
instance: ToString Kind where
  toString
  | .ite => "ite"
  | .dite => "dite"
  | .matcher name => s!"matcher {name}"
instance: ToMessageData Kind where toMessageData k := toString k

/-- Rough equivalent of `Lean.Meta.MatcherApp`, but which also includes if-then-else -/
structure Info where
  /-- The kind of bifurcation -/
  kind: Kind

  /-- The information on discriminants of the bifurcation -/
  discrs: Array Discr

  /-- The information on the branches of the bifurcation -/
  branches: Array Branch

  /-- The name of the function which implements the matcher -/
  matcher: Name

  /-- The motive of the bifurcation -/
  motive: Expr

  /-- The universe levels of the bifurcation -/
  uLevels: List Lean.Level

  /-- -/
  params: Array Expr
  deriving Repr
instance: ToMessageData Info where
  toMessageData 
  | {kind, discrs, branches, ..} =>
    let discr := MessageData.ofArray <| discrs.map (ToMessageData.toMessageData)
    let branches := MessageData.ofArray <| branches.map (ToMessageData.toMessageData)
    m!"(info {kind} {discr} {branches})"

def Info.ofExpr(e: Expr): MetaM (Option Info) := do
  let e := e.consumeMData
  if e.isIte || e.isDIte then
    let kind := if e.isIte then .ite else .dite
    --   ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t           e : α)      : α
    --  dite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : ¬c → α) : α
    /- let #[_ty, cond, _dec, brThen, brElse] := e.getAppArgs -/
    /- let e ← whnf e -/ 
    let e ← deltaExpand e (fun n => n == ``ite || n == ``dite)
    -- Decidable.casesOn.{u} {prop} {motive} dec (isFalse: (h:¬p) → motive (isFalse h)) (isTrue: (h:p) → motive (isTrue h)) : motive t
    let .const ``Decidable.casesOn uLevels := e.getAppFn
      | throwError "Expected ``Decidable.rec, found {←ppExpr e.getAppFn}"
    let #[prop, motive, dec, brFalse, brTrue] := e.getAppArgs
      | throwError "Wrong number of parameters for {e.getAppFn}: {e.getAppArgs.size} [{e.getAppArgs}]"
    return some {
      kind,
      discrs := #[{ toExpr := dec }]
      -- TODO: I should be able to retrieve the name given to
      --  the condition of a dite.
      branches  := #[
        { toExpr := brTrue,  numArgs := 1, },
        { toExpr := brFalse, numArgs := 1, }
      ]
      matcher := ``Decidable.casesOn,
      uLevels,
      params  := #[prop]
      motive,
    }
  else if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    return some {
      kind := .matcher ma.matcherName
      discrs := ma.discrs.zip ma.discrInfos 
        |>.map fun (toExpr, discrInfo) => {toExpr, name? := discrInfo.hName?}
      branches := ma.alts.zip ma.altNumParams 
        |>.map fun (toExpr, numArgs) => {toExpr, numArgs}
      matcher := ma.matcherName,
      motive := ma.motive,
      uLevels := ma.matcherLevels.toList,
      params := ma.params
    }
  else 
    /- e.withApp fun f args => logWarning s!"{f} {args}" -/
    return none

def Info.toExpr(info: Info): Expr :=
  let fn := Expr.const info.matcher info.uLevels
  let args := info.params ++
    #[info.motive] ++
    info.discrs.map (·.toExpr) ++
    info.branches.map (·.toExpr)
  mkAppN fn args

end Bifurcation/- }}} -/

-- TODO: Move to Utils
/-- Given ty := ∀ xs.., ∃ zs.., program = res ∧ post?, destruct and run continuation -/
def aeneasProgramTelescope(ty: Expr)
  (k: (xs:Array MVarId) → (zs:Array FVarId) → (program:Expr) → (res:Expr) → (post:Option Expr) → TacticM α)
: TacticM α := do
  unless ←isDefEq (←inferType ty) (mkSort 0) do
    throwError "Expected a proposition, got {←inferType ty}"
  let ty ← Utils.normalizeLetBindings ty
  -- ty := ∀ xs, ty₂
  let (xs, _xs_bi, ty₂) ← forallMetaTelescope ty.consumeMData
  -- ty₂ := ∃ zs, ty₃ ≃ Exists {α} (fun zs => ty₃)
  Utils.existsTelescope ty₂ fun zs ty₃ => do
    -- ty₃ := ty₄ ∧ post?
    let (ty₄, post?) ← Utils.optSplitConj ty₃
    -- ty₄ := ty₅ = res
    let (program, res) ← Utils.destEq ty₄
    k (xs.map (·.mvarId!)) (zs.map (·.fvarId!)) program res post?


partial 
def traverseProgram {α} [Monad m] [MonadError m] [Nonempty (m α)] 
  /- [MonadLog m] [AddMessageContext m] [MonadOptions m] -/ 
  [MonadLiftT MetaM m] [MonadControlT MetaM m] 
  (onResult: Expr -> m α)
  (onBind: Expr -> Name -> m α -> m α)
  (onBif: Bifurcation.Info -> Array (Array Name × m α) -> m α)
  (e: Expr)
: m α := do
  let e <- (Utils.normalizeLetBindings e)
  if let .const ``Bind.bind .. := e.getAppFn then
    let #[_m, _self, _α, _β, value, cont] := e.getAppArgs
      | throwError s!"Expected bind to have 4 arguments, found {<- e.getAppArgs.mapM (liftM ∘ ppExpr)}"
    Utils.lambdaOne cont fun x body => do
      let name ← x.fvarId!.getUserName
      let contVal: m α := traverseProgram onResult onBind onBif body
      onBind value name contVal
  else if let .some bfInfo ← Bifurcation.Info.ofExpr e then
    let contsTaggedVals <- 
      bfInfo.branches.mapM fun br => do
        Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs body => do
          let names ← xs.mapM (·.fvarId!.getUserName)
          let other := traverseProgram onResult onBind onBif body
          return (names, other)
    onBif bfInfo contsTaggedVals
  else
    onResult e

partial
def evalProgressStar: TacticM (Array Syntax.Tactic) := withMainContext do
  let goalTy <- getMainTarget
  aeneasProgramTelescope goalTy fun _xs _zs program _res _post => do
    trace[ProgressStar] s!"Generating suggestion script for {← ppExpr program}"
    traverseProgram onResult onBind onBif program
where
  endOfProcessing: TacticM (Array Syntax.Tactic) := pure #[]

  onResult _expr := do
    trace[ProgressStar] s!"onResult: encountered {←ppExpr _expr}"
    endOfProcessing

  onBind _curr _name? processRest := do
    trace[ProgressStar] s!"onBind: encountered {←ppExpr _curr}"
    let canMakeProgress ← do
      try
        Progress.evalProgress none none #[] *> pure true
      catch _ => pure false
    if canMakeProgress then
      trace[ProgressStar] s!"onBind: Can make progress!"
      let tacs ← processRest
      let curr ← `(tactic| progress)
      return #[curr] ++ tacs -- TODO: Optimize
    else endOfProcessing

  onBif bfInfo toBeProcessed := do
    trace[ProgressStar] s!"onBif: encountered {bfInfo.kind}"
    Tactic.focus do
      let splitStx ← `(tactic| split)
      evalSplit splitStx
      -- 
      let subgoals ← getUnsolvedGoals
      unless subgoals.length == toBeProcessed.size do
        throwError s!"Expected {toBeProcessed.size} cases, found {subgoals.length}"
      -- Gather suggestions from branches
      let mut unsolvedGoals: List (MVarId) := []
      let mut suggestions := #[splitStx]
      for (sg, (_, processBr)) in subgoals.zip toBeProcessed.toList do
        /- let tag ← sg.getTag -/
        setGoals [sg]
        let branchSuggestions ← processBr
        suggestions := suggestions.push <| ←`(tactic| case' _  => $(branchSuggestions)*)
        unsolvedGoals := unsolvedGoals ++ (←getUnsolvedGoals)

      setGoals unsolvedGoals
      return suggestions

-- NOTE: Credit to Aesop
def addTryThisTacticSeqSuggestion (ref : Syntax)
    (suggestion : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (origSpan? : Option Syntax := none) : MetaM Unit := do
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq suggestion
  let msgText := fmt.pretty (indent := 0) (column := 0)
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn map range
    let text := fmt.pretty (indent := indent) (column := column)
    let suggestion := {
      suggestion := .string $ dedent text
      messageData? := some msgText
      preInfo? := "  "
    }
    Lean.Meta.Tactic.TryThis.addSuggestion ref suggestion (origSpan? := origSpan?)
      (header := "Try this:\n")
where
  dedent (s : String) : String :=
    s.splitOn "\n"
    |>.map (λ line => line.dropPrefix? "  " |>.map (·.toString) |>.getD line)
    |> String.intercalate "\n"

elab "progress_all" : tactic => do 
  evalProgressStar *> pure ()

elab tk:"progress_all?" : tactic => do 
  let tacs ← evalProgressStar
  let suggestion ← `(tacticSeq| $(tacs)*)
  addTryThisTacticSeqSuggestion tk suggestion (origSpan? := ← getRef)
