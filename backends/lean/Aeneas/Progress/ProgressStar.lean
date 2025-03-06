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
instance: ToMessageData Kind where
  toMessageData 
  | .ite => m!"ite"
  | .dite => m!"dite"
  | .matcher name => m!"matcher {name}"

structure Info where
  /-- The kind of bifurcation -/
  kind: Kind

  /-- The information on discriminants of the bifurcation -/
  discr: Array Discr

  /-- The information on the branches of the bifurcation -/
  branches: Array Branch

  /-/1-- The motive of the bifurcation -1/ -/
  /-motive: Expr -/

  /-/1-- The levels of the bifurcation -1/ -/
  /-levels: Array Lean.Level -/

  /-/1-- -1/ -/
  /-params: Array Expr -/
instance: ToMessageData Info where
  toMessageData 
  | {kind, discr,branches} =>
    let discr := MessageData.ofArray <| discr.map (ToMessageData.toMessageData)
    let branches := MessageData.ofArray <| branches.map (ToMessageData.toMessageData)
    m!"(info {kind} {discr} {branches})"

def Info.ofExpr(e: Expr): MetaM (Option Info) := do
  let e :=  e.consumeMData
  if e.isIte then
    let #[_ty, cond, _dec, brThen, brElse] := e.getAppArgs
      | throwError "Wrong number of parameters for {e.getAppFn}: {e.getAppArgs}"
    return some {
      kind := .ite
      discr := #[ {toExpr := cond} ]
      branches  := #[
        {
          toExpr := brThen,
          numArgs := 0,
        },
        {
          toExpr := brElse,
          numArgs := 0,
        }
      ]
    }
  else if e.isDIte then 
    let #[_ty, cond, _dec, brThen, brElse] := e.getAppArgs
      | throwError "Wrong number of parameters for {e.getAppFn}: {e.getAppArgs}"
    return some {
      kind := .dite
      discr := #[ {toExpr := cond, name? := none} ]
      -- TODO: I should be able to retrieve the name given to
      --  the condition of a dite.
      branches  := #[
        {
          toExpr := brThen,
          numArgs := 1,
        },
        {
          toExpr := brElse,
          numArgs := 1,
        }
      ]
    }
  else if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    return some {
      kind := .matcher ma.matcherName
      discr := ma.discrs.zip ma.discrInfos 
        |>.map fun (toExpr, discrInfo) => {toExpr, name? := discrInfo.hName?}
      branches := ma.alts.zip ma.altNumParams 
        |>.map fun (toExpr, numArgs) => {toExpr, numArgs}
    }
  else 
    /- e.withApp fun f args => logWarning s!"{f} {args}" -/
    return none

end Bifurcation/- }}} -/


inductive ProgramShape where
  | result (curr: Expr)
  | bifur  (bfInfo: Bifurcation.Info): ProgramShape
  | bind   (curr cont: Expr): ProgramShape

namespace ProgramShape /- {{{ -/
def ofExpr (e: Expr)
[Monad m] [MonadError m] [MonadLiftT MetaM m]
: m ProgramShape := do
  let e <- (Utils.normalizeLetBindings e)
  if let .const ``Bind.bind .. := e.getAppFn then
    -- Bind.bind {m : Type u → Type v} [self : Bind m] {α β : Type u} : m α → (α → m β) → m β
    let #[_m, _self, _α, _β, value, cont] := e.getAppArgs
      | throwError s!"Expected bind to have 4 arguments, found {<- e.getAppArgs.mapM (liftM ∘ ppExpr)}"
    return ProgramShape.bind value cont
  else if let .some bfInfo ← Bifurcation.Info.ofExpr e then
    return bifur bfInfo
  else
    return ProgramShape.result e

partial 
def fold {α} [Monad m] [MonadError m] [Nonempty (m α)]
  [MonadLiftT MetaM m] [MonadControlT MetaM m] 
  (onResult: Expr -> m α)
  (onBind: Expr -> Name -> m α -> m α)
  (onBif: Bifurcation.Info -> Array (Array Name × m α) -> m α)
: ProgramShape -> m α
| result expr => onResult expr
| bind curr cont => do 
  Utils.lambdaOne cont fun x body => do
    let name? ← x.fvarId!.getUserName
    let contVal: m α := do
      let shape <- ProgramShape.ofExpr body
      ProgramShape.fold onResult onBind onBif shape
    onBind curr name? contVal
| bifur bfInfo => do
    let contsTaggedVals <- 
      bfInfo.branches.mapM fun br => do
        Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs body => do
          let shape ← ProgramShape.ofExpr body
          let names ← xs.mapM (·.fvarId!.getUserName)
          let other := ProgramShape.fold onResult onBind onBif shape
          return (names, other)
    onBif bfInfo contsTaggedVals
end ProgramShape/- }}} -/

section Testing/- {{{ -/
partial
def ProgramShape.show(shape: ProgramShape): MetaM Format :=
  shape.fold onResult onBind onBif
where
  onResult expr := 
    ppExpr expr
  onBind expr name rest := do
    let binding := "let " ++ name.toString ++ " ← "
    return binding ++ (←ppExpr expr) ++ .line ++ (←rest)
  onBif bfInfo rests := do
      let name? := match bfInfo.kind with
        |.matcher name => s!"({name}) "
        | _ => ""
      let ppDiscr: Array Format ← bfInfo.discr
        |>.mapM fun d => do
          let ppName? := if let some name := d.name? then name.toString ++ ": " else ""
          let ppDiscr ← ppExpr d.toExpr
          return ppName? ++ ppDiscr
        /- |> (Format.joinSep · ",") -/
      let ppBranches ← rests.mapIdxM fun i (names,ppBr) => do
        let names := 
          if names.isEmpty then .nil else (Format.joinSep names.toList ", ") ++ " "
        return "case " ++ (toString i) ++ " "  ++ names ++ "=> " ++
          Format.nest 2 (.align false ++ (←ppBr))
      return name? ++ "match " ++ (Format.joinSep ppDiscr.toList ", ") ++
        " with" ++ .align false ++ 
        Format.joinSep ppBranches.toList Format.line
      
elab "uut2" stx:term : tactic => do
  let e <- elabTerm stx none
  let shape <- ProgramShape.ofExpr e
  withRef stx <| logInfo s!"{<- shape.show}"

set_option linter.unusedTactic false in
example 
(x: Nat)
(add: Nat -> Nat -> Except String Nat)
(max: Nat -> Nat -> Except String Nat)
: 1 = 0
:= by
  uut2 (do
  let aux₁ <- add 1 2
  let aux₂ <- max 1 aux₁
  let res <- add aux₂ aux₂
  let x := 10
  if res < x*x - x then
    return res
  else
    let res₂ <- add res x
    return res₂
  )

  uut2 (do
  let aux₁ <- add 1 2
  let aux₂ <- max 1 aux₁
  let res <- add aux₂ aux₂
  let x := 10
  match res with
  | 0 => pure 10
  | n+1 => pure $ if res > x * 10 then -3 else Int.ofNat n
  )

  uut2 (do
  let aux₁ <- add 1 2
  let aux₂ <- max 1 aux₁
  let res <- add aux₂ aux₂
  let x := 10
  match res with
  | 0 => pure 10
  | n+1 => do 
    if res > x * 10 then 
      return -3 
    else 
      return Int.ofNat n
  )
  sorry
end Testing/- }}} -/

open Lean.Parser.Tactic in
partial
def namingThingsIsHard(program: Expr): TacticM (Array Syntax.Tactic) := 
withoutModifyingState do
  let shape ← ProgramShape.ofExpr program
  shape.fold onResult onBind onBif
where
  endOfProcessing: TacticM (Array Syntax.Tactic) := do return #[←`(tactic| skip)]

  onResult _expr := endOfProcessing

  onBind _curr _name? processRest := do
    let canMakeProgress ← do
      try
        Progress.evalProgress none none #[] *> pure true
      catch _ => pure false
    if canMakeProgress then
      let tacs ← processRest
      let curr ← `(tactic| progress)
      return #[curr] ++ tacs -- TODO: Optimize
    else endOfProcessing

  onBif _bfInfo _toBeProcessed := do
    -- Split the goal in two according to bfInfo
    -- Proceed with the processing on each branch.
    -- We probably need to reset the state after every branch.
    throwError "Not yet implemented!"
    /- Tactic.evalSplit mkNullNode -/
    /- let goals ← getUnsolvedGoals -/
    /- if toBeProcessed.size != goals.length then -/
    /-   throwError s!"Expected {toBeProcessed.size} got {goals.length}" -/
    /- for ((names?,processBranch), goal) in toBeProcessed.toList.zip goals do -/
    /-   setGoals [goal] -/
    /-   let tacs ← processBranch -/
    /-   pure () -/

-- TODO: Move to Utils
/-- Given ty := ∀ xs.., ∃ zs.., program = res ∧ post?, destruct and run continuation -/
def progressSpecTelescope(ty: Expr)
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


def evalProgressStar: TacticM Unit := do
  withMainContext do
    let goalTy <- getMainTarget
    progressSpecTelescope goalTy fun _xs _zs prog _res _post? => do
      trace[ProgressStar] s!"{← ppExpr prog}"
      let tacs ← namingThingsIsHard prog
      let suggestion ← `(tacticSeq| $(tacs)*)
      TryThis.addSuggestion (←getRef) (TryThis.SuggestionText.tsyntax suggestion)
      pure ()


elab tk:"progressStar" : tactic => do withRef tk <| evalProgressStar
