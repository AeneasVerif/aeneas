import Lean
import Aeneas.Utils
import Aeneas.Progress.Progress
import Aeneas.Progress.Core
import Aesop.Util.Basic
open Aeneas
open Lean Meta Elab Tactic 

namespace Bifurcation
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
    let e ← deltaExpand e (fun n => n == ``ite || n == ``dite)
    -- Decidable.casesOn.{u} {prop} {motive} dec (isFalse: (h:¬p) → motive (isFalse h)) (isTrue: (h:p) → motive (isTrue h)) : motive t
    let .const ``Decidable.casesOn uLevels := e.getAppFn
      | throwError "Expected ``Decidable.casesOn, found {←ppExpr e.getAppFn}"
    let #[prop, motive, dec, brFalse, brTrue] := e.getAppArgs
      | throwError "Wrong number of parameters for {e.getAppFn}: {e.getAppArgs.size} [{e.getAppArgs}]"
    let name? ← if e.isDIte 
      then some <$> Utils.lambdaOne brFalse fun x _ => x.fvarId!.getUserName
      else pure none
    return some {
      kind,
      discrs := #[{ toExpr := dec, name?}]
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
  else return none

def Info.toExpr(info: Info): Expr :=
  let fn := Expr.const info.matcher info.uLevels
  let args := info.params ++
    #[info.motive] ++
    info.discrs.map (·.toExpr) ++
    info.branches.map (·.toExpr)
  mkAppN fn args

end Bifurcation

private partial 
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

namespace ProgressStar

structure Config where
  preconditionTac: Option Syntax.Tactic := none

structure Info where
  script: Array Syntax.Tactic := #[]
  unsolvedPreconditions: List MVarId := []

instance: Append Info where
  append inf1 inf2 := {
    script := inf1.script ++ inf2.script,
    unsolvedPreconditions := inf1.unsolvedPreconditions ++ inf2.unsolvedPreconditions,
  }

partial
def evalProgressStar(cfg: Config): TacticM Info := withMainContext do
  trace[ProgressStar] s!"Normalizing bind application in goal {←(getMainTarget >>= (liftM ∘ ppExpr))}"
  Utils.simpAt (simpOnly := true) (thms := [``Aeneas.Std.bind_assoc_eq]) 
    (loc := .targets #[] (type := true) )
    (config := {maxDischargeDepth:= 0}) (simprocs := []) (simpThms := [])
    (declsToUnfold := []) (hypsToUse := [])  
    <|> pure ()
  let goalTy <- getMainTarget
  trace[ProgressStar] s!"After bind normalization: {←ppExpr goalTy}"
  let res ← Progress.programTelescope goalTy fun _xs _zs program _res _post => do
    trace[ProgressStar] s!"Traversing {← ppExpr program}"
    let resultName := .str .anonymous "res"
    traverseProgram (onResult resultName) onBind onBif program
  setGoals (res.unsolvedPreconditions ++ (←getGoals))
  return res

where
  onResult resultName expr := do
    trace[ProgressStar] s!"onResult: Since (· >>= pure) = id, we treat this result as a bind on id"
    -- Since (· >>= pure) = id, we treat a result as a bind on id
    onBind expr resultName (pure {})

  onBind _curr name processRest := do
    trace[ProgressStar] s!"onBind: encountered {←ppExpr _curr}"
    if let some {usedTheorem, ..} ← tryProgress then
      trace[ProgressStar] s!"onBind: Can make progress! Binding {name}"
      let (preconditionTacs, unsolved) ← trySolvePreconditions
      if ¬ preconditionTacs.isEmpty then
        trace[ProgressStar] s!"onBind: Found {preconditionTacs.size} preconditions, left {unsolved.size} unsolved"
      let ids ← getIdsFromUsedTheorem name usedTheorem
      if ¬ ids.isEmpty && ¬ (←getGoals).isEmpty then
        replaceMainGoal [← renameInaccessibles (← getMainGoal) ids] -- NOTE: Taken from renameI tactic
      let currTac ← if ids.isEmpty 
        then `(tactic| progress with $(←usedTheorem.toSyntax))
        else `(tactic| progress with $(←usedTheorem.toSyntax) as ⟨$ids,*⟩)
      let restInfo ← processRest
      return {
        script := #[currTac]++ preconditionTacs, -- TODO: Optimize
        unsolvedPreconditions := unsolved.toList
      } ++ restInfo
    else return {script:=#[]}

  onBif bfInfo toBeProcessed := do
    trace[ProgressStar] s!"onBif: encountered {bfInfo.kind}"
    if (←getGoals).isEmpty then 
      trace[ProgressStar] s!"onBif: no goals to be solved!"
      -- Tactic.focus fails if there are no goals to be solved.
      return {}
    Tactic.focus do
      let splitStx ← `(tactic| split)
      evalSplit splitStx
      -- 
      let subgoals ← getUnsolvedGoals
      trace[ProgressStar] s!"onBif: Bifurcation generated {subgoals.length} subgoals"
      unless subgoals.length == toBeProcessed.size do
        throwError s!"onBif: Expected {toBeProcessed.size} cases, found {subgoals.length}"
      -- Gather suggestions from branches
      let mut unsolvedGoals: List (MVarId) := []
      let mut info := {script:=#[splitStx]}
      for (sg, (names, processBr)) in subgoals.zip toBeProcessed.toList do
        setGoals [sg]
        let branchInfo ← processBr

        let branchTacs ← if branchInfo.script.isEmpty 
          then pure #[←`(tactic| skip)]
          else pure branchInfo.script
        let caseArgs := makeCaseArgs (←sg.getTag) names
        info := {info ++ branchInfo with 
          script:=info.script.push <| ←`(tactic| case' $caseArgs => $branchTacs*),
        }
        unsolvedGoals := unsolvedGoals ++ (←getUnsolvedGoals)

      setGoals unsolvedGoals
      return info

  tryProgress := do
    try some <$> Progress.evalProgress none none #[]
    catch _ => pure none

  trySolvePreconditions: TacticM (Array Syntax.Tactic × Array MVarId) := do
    -- NOTE: Do I make the assumption that the preconditions appear before the final lemma, or
    -- that the names of the preconditions contain the final lemma as a prefix.
    -- For now, we have ←getUnsolvedGoals = preconditions ++ [final]
    let rec loop acc unsolved: List MVarId -> TacticM (Array Syntax.Tactic × Array MVarId) := fun
      | []  => pure (acc, unsolved)
      | [final] => do
          setGoals [final]
          return (acc, unsolved)
      | curr :: rest => do
        setGoals [curr]
        try
          if let .some tac := cfg.preconditionTac then
            evalTactic tac
            return ←loop (acc.push <| ←`(tactic| · $(#[tac])*)) unsolved rest
        catch _ => pure ()
        let defaultTac ← `(tactic| · skip)
        return ←loop (acc.push defaultTac) (unsolved.push curr) rest
    loop #[] #[] (← getUnsolvedGoals)

  getIdsFromUsedTheorem name usedTheorem: TacticM (Array _) := do
    let some thm ← usedTheorem.getType
      | throwError s!"Could not infer proposition of {usedTheorem}"
    let (numElem, numPost) ← Progress.programTelescope thm 
      fun _xs zs _program _res postconds => do
        let numPost := Utils.numOfConjuncts <$> postconds |>.getD 0
        trace[ProgressStar] s!"Number of conjuncts for {←liftM (Option.traverse ppExpr postconds)} is {numPost}"
        pure (zs.size, numPost)
    return makeIds (base := name) numElem numPost

  makeIds (base: Name) (numElem numPost : Nat) (defaultId := "x"): Array (TSyntax ``Lean.binderIdent) :=
    let (root, base?) := match base with
      | .str root base => (root, some base)
      | .num root _ => (root, none)
      | .anonymous => (.anonymous, none)
    let base := base?.getD defaultId
    let optionallyEnumerated base num := match num with
      | 0 => #[]
      | 1 => #[Name.str root base]
      | num => Array.ofFn fun (i: Fin num) => Name.str root s!"{base}_{i.val+1}"
    let elemNames := optionallyEnumerated base numElem
    let postNames := optionallyEnumerated s!"{base}_post" numPost
    elemNames ++ postNames |>.map (mkNode ``Lean.binderIdent #[mkIdent ·])

  makeCaseArgs tag names :=
    let tag := Lean.mkNode ``Lean.binderIdent #[mkIdent tag]
    let binderIdents := names.map fun n => if n.isInternalDetail 
      then mkNode ``Lean.binderIdent #[mkHole mkNullNode]
      else mkNode ``Lean.binderIdent #[mkIdent n]
    Lean.mkNode ``Lean.Parser.Tactic.caseArg #[tag, mkNullNode (args := binderIdents)]

syntax «progress*_args» := ("by" tactic)?

def parseArgs: TSyntax `ProgressStar.«progress*_args» → CoreM Config 
| `(«progress*_args»| $[by $preconditionTac:tactic]?) => do
  return {preconditionTac}
| _ => throwUnsupportedSyntax

elab "progress" noWs "*" stx:«progress*_args»: tactic => do 
  let cfg ← parseArgs stx
  evalProgressStar cfg *> pure ()

elab tk:"progress" noWs "*?" stx:«progress*_args»: tactic => do 
  let cfg ← parseArgs stx
  let info ← evalProgressStar cfg
  let suggestion ← `(tacticSeq| $(info.script)*)
  Aesop.addTryThisTacticSeqSuggestion tk suggestion (origSpan? := ← getRef)

end ProgressStar
