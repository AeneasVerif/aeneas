import Lean
import Aeneas
/- import Mathlib.Control.Sequence -/
open Aeneas
open Lean Meta Elab Tactic 

namespace ExperimentingWithMatcher/- {{{ -/
/- open Std.Format in -/ 
def showMatcherApp(ma: MatcherApp): TacticM String := do
  let showArray: Array Expr -> TacticM (Array Format) := Array.mapM (liftM ∘ ppExpr)
  return (
    s!"matcherName: \n\t{ma.matcherName}\n" ++
    s!"matcherLevels: \n\t{ma.matcherLevels}\n" ++
    s!"uElimPos: \n\t{ma.uElimPos?}\n" ++
    s!"discrInfos: \n\t{<- ma.discrInfos.mapM (pure $ ·.hName?)}\n" ++
    s!"params: \n\t{<- showArray ma.params}\n" ++
    s!"motive: \n\t{<- ppExpr ma.motive}\n" ++
    s!"discrs: \n\t{<- showArray ma.discrs}\n" ++ 
    s!"alts: \n\t{<- showArray ma.alts}\n" ++ 
    s!"altNumParams: \n\t{ma.altNumParams}\n" ++ 
    s!"remaining: \n\t{<- showArray ma.remaining}\n"
  )

elab tac:"uut" stx:term : tactic => do 
    let e <- elabTerm stx.raw none
    if let some ma ← Lean.Meta.matchMatcherApp? e then
      withRef tac <|
        logInfo s!"{<- showMatcherApp ma}"
    if e.isIte || e.isDIte then
      logInfo s!"{if e.isDIte then "d" else ""}ite!"
      let #[_ty, cond, _dec, brThen, brElse] := e.getAppArgs
        | throwError "Expected 5 arguments, got {e.getAppArgs}"
      logInfo s!"cond: {<- ppExpr <| <- inferType cond} {<- ppExpr cond}"
      logInfo s!"brThen: {<- ppExpr <| <- inferType brThen} {<- ppExpr brThen}"
      logInfo s!"brElse: {<- ppExpr <| <- inferType brElse} {<- ppExpr brElse}"
    pure ()


inductive IndTy where
  | Single : IndTy
  | Pair   : Nat × Nat -> IndTy
  | Arr    : (Nat -> Nat) -> IndTy
  | Sum    : (Option Nat) -> IndTy
  | Rec    : IndTy -> IndTy

example
  {α}
  (x y z: IndTy)
  (xs ys zs: List IndTy)
  (αs βs γs: List α)
: 1 = 0 
:= by
  uut match x with 
    | .Single       => 1
    | .Pair (a,b)   => 2
    | .Arr k        => 3
    | .Sum (some _) => 4
    | .Sum (none)   => 5
    | .Rec i        => 6

  uut match x with 
    | .Single      
    | .Pair (a,b)   
    | .Arr k     
    | .Sum (some _) 
    | .Sum (none)
    | .Rec i        => 6

  uut match x with
    | .Single => true
    | _ =>  false

  uut match h: x with
    | .Single => true
    | _ =>  false

  uut match x, y with 
    | .Single, _ => true
    | _, _ =>  false

  uut match x with
    | .Rec (.Rec (.Rec x))
    | .Rec (.Rec x)
    | .Rec x
    | x => match x with
      | .Rec (.Rec (.Rec x))
      | .Rec (.Rec x)
      | .Rec x => 10
      | x => 0
  uut match xs with
    | x :: xs => 1
    | _ => 0

  uut match αs with
    | x :: xs => 0
    | _ => 1

  uut match αs with
    | x :: xs => fun y => 0
    | _ => sorry

  uut if true then
      10
    else 30

  uut if h:true then
      h
    else rfl

  uut if h: 10 > 0 then
    sorry
  else 
    sorry

  sorry
end ExperimentingWithMatcher/- }}} -/


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

namespace Testing/- {{{ -/
elab "getBfInfo" stx:term : tactic => do
  withRef stx do
    let e <- elabTerm stx.raw none
    logInfo m!"{<- Bifurcation.Info.ofExpr e}"

example(x y z: ExperimentingWithMatcher.IndTy) 
  (n m : Nat)
: 1 = 0 := by
  getBfInfo (if m > 10 then 0 else 1) -- FAILS
  getBfInfo (if h: m > 10 then 0 else 1) -- FAILS
  getBfInfo (if (match x with | .Rec _ => true | _ => false) then 0 else 1)
  getBfInfo (@Nat.casesOn (λ _ => Nat) 10 (10) (· + 10))

  sorry
end Testing/- }}} -/

inductive ProofShape where
  | result (curr: Expr)
  | bifur  (bfInfo: Bifurcation.Info): ProofShape
  | bind   (curr cont: Expr): ProofShape

def ProofShape.ofExpr (e: Expr)
[Monad m] [MonadError m] [MonadLiftT MetaM m]
: m ProofShape := do
  let e <- (Utils.normalizeLetBindings e)
  if let .const ``Bind.bind .. := e.getAppFn then
    -- Bind.bind {m : Type u → Type v} [self : Bind m] {α β : Type u} : m α → (α → m β) → m β
    let #[_m, _self, _α, _β, value, cont] := e.getAppArgs
      | throwError s!"Expected bind to have 4 arguments, found {<- e.getAppArgs.mapM (liftM ∘ ppExpr)}"
    return ProofShape.bind value cont
  else if let .some bfInfo ← Bifurcation.Info.ofExpr e then
    return bifur bfInfo
  else
    return ProofShape.result e

partial 
def ProofShape.fold {α} [Monad m] [MonadError m] [Nonempty (m α)]
  [MonadLiftT MetaM m] [MonadControlT MetaM m] 
  (onResult: Expr -> m α)
  (onBind: Expr -> Name -> m α -> m α)
  (onBif: Bifurcation.Info -> Array (Array Name × m α) -> m α)
: ProofShape -> m α
| result expr => onResult expr
| bind curr cont => do 
  Utils.lambdaOne cont fun x body => do
    let name? ← x.fvarId!.getUserName
    let contVal: m α := do
      let shape <- ProofShape.ofExpr body
      ProofShape.fold onResult onBind onBif shape
    onBind curr name? contVal
| bifur bfInfo => do
    let contsTaggedVals <- 
      bfInfo.branches.mapM fun br => do
        Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs body => do
          let shape ← ProofShape.ofExpr body
          let names ← xs.mapM (·.fvarId!.getUserName)
          let other := ProofShape.fold onResult onBind onBif shape
          return (names, other)
    onBif bfInfo contsTaggedVals

section Testing/- {{{ -/
partial
def ProofShape.show(shape: ProofShape): MetaM Format :=
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
  let shape <- ProofShape.ofExpr e
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

#check Syntax.node

open Lean.Parser.Tactic in
partial
def namingThingsIsHard(program: Expr): TacticM (TSyntax `tactic) := 
withoutModifyingState do
  let shape ← ProofShape.ofExpr program
  shape.fold onResult onBind onBif
where
  endOfProcessing := do 
    let tacs ← `(tactic| sorry;)
    match tacs.raw with
    | Syntax.node ni k #[Syntax.node ni2 `null args] =>
      return {raw := Syntax.node ni k #[Syntax.node ni2 `null args.pop]}
    | _ => return {raw:=tacs.raw}
  pushToTacList (tac tacSeq: TSyntax `tactic) := do
      match tacSeq.raw with
      | Syntax.node ni k #[Syntax.node ni2 `null args] =>
        return {raw := Syntax.node ni k #[Syntax.node ni2 `null ⟨tac :: args.toList⟩]}
      | _ => 
        logInfo s!"Didn't expect to get here..."
        return {raw:=tacSeq.raw}

  onResult expr := endOfProcessing
  onBind curr name? processRest := do
    let canMakeProgress ← do
      try
        Progress.evalProgress none none #[] *> pure true
      catch _ => pure false
    if canMakeProgress then
      let tacs ← processRest
      let curr ← `(tactic| progress)
      pushToTacList curr tacs
    else 
      endOfProcessing
  onBif bfInfo toBeProcessed:= do
    Tactic.evalSplit mkNullNode
    let goals ← getUnsolvedGoals
    if toBeProcessed.size != goals.length then
      throwError s!"Expected {toBeProcessed.size} got {goals.length}"
    for ((names?,processBranch), goal) in toBeProcessed.toList.zip goals do
      setGoals [goal]
      let tacs ← processBranch



      pure ()

    sorry

def evalProgressStar: TacticM Unit := do
  withMainContext do
    let goal <- getMainTarget
    let suggestion ← namingThingsIsHard sorry
    -- tacticSeq1Indented
    TryThis.addSuggestion (←getRef) (TryThis.SuggestionText.tsyntax suggestion)
    pure ()


elab tk:"progressStar" : tactic => do withRef tk <| evalProgressStar

open Lean.Parser.Tactic in 
elab rf:"print" tacs:tacticSeq1Indented : tactic => do 
  withRef rf <| logInfo s!"{repr tacs}"
  TryThis.addSuggestion (←getRef) (TryThis.SuggestionText.tsyntax tacs)

example : 1 = 0 := by
  /- progressStar -/
  print sorry
  case _ => sorry
  print
    · progress
      progress
      progress
