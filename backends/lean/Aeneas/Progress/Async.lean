import Aeneas.ScalarTac

open Lean Elab Term Meta Tactic
namespace Aeneas

open Utils

/-!
# Asynchronous execution
-/
/--
One issue with tactics like `omega` is that they wrap proofs in auxiliary theorems.
As a temporary workaround I'm using this helper to inline the proof terms.

Side question: how to properly handle this? I had a look at what is done
in `MutualDef.lean` but couldn't figure how to adapt what is being done there
(for instance with `env.addConstAsync`) to my setting.
-/
def inlineFreshProofs (env0 : Environment) (e : Expr) : MetaM Expr := do
  let rec inline (e : Expr) : MetaM Expr := do
    match e with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure e
    | .const declName us =>
      if env0.contains declName then pure e
      else
        -- We need to inline this constant
        let some const ← pure ((← getEnv).find? declName) | unreachable!
        let some body := const.value? (allowOpaque := true)
          | throwError "Could not inline constant: {e}"
        -- Replace the levels in the body
        let levels := const.levelParams
        let levels := Std.HashMap.ofList (List.zip (List.map Level.param levels) us)
        let body := body.replaceLevel (Std.HashMap.get? levels)
        pure body
    | .app fn arg => pure (.app (← inline fn) (← inline arg))
    | .lam name ty body info =>
      pure (.lam name (← inline ty) (← inline body) info)
    | .forallE name ty body info =>
      pure (.forallE name (← inline ty) (← inline body) info)
    | .letE name ty value body nonDep =>
      pure (.letE name (← inline ty) (← inline value) (← inline body) nonDep)
    | .mdata data e => pure (.mdata data (← inline e))
    | .proj name idx struct =>
      pure (.proj name idx (← inline struct))
  inline (← instantiateMVars e)

/-
I noticed a bit too late that I could have used `Lean.Elab.Term.wrapAsyncAsSnapshot` instead of
`Lean.Core.wrapAsyncAsSnapshot` but I guess it shouldn't make much difference.
-/
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken)  :
  TacticM (IO.Promise (Except Exception (Option Expr)) × (α → BaseIO Language.SnapshotTree)) := do
  let env0 ← getEnv
  withMainContext do
  -- The code below is adapted from `Lean.Elab.Tactic.tacticToDischarge` --
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let mvar ← mkFreshExprSyntheticOpaqueMVar (← getMainTarget) `simp.discharger
  let s ← ref.get
  let promise : IO.Promise (Except Exception (Option Expr)) ← IO.Promise.new
  let runTac? (x : α) : TermElabM Unit :=
    try
      --Term.withoutModifyingElabMetaStateWithInfo do
        let ngoals ← --Term.withSynthesize (postpone := .no) do
          Tactic.run mvar.mvarId! (tactic x)
        if ngoals.isEmpty then
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            promise.resolve (.ok none)
          else
            /- Inline the theorems introduced by `omega`. Note that doing this
               has an impact on the performance, but I would expect it to be
               compensated by the fact that: 1. we do this in parallel,
               2. checking the final proof term is also done asynchronously
               and should not have an impact on the time it takes to refresh
               the goals displayed to the user (correct?).
             -/
            let result ← inlineFreshProofs env0 result
            promise.resolve (.ok (some result))
        else promise.resolve (.ok none)
    catch e => promise.resolve (.error e)
  --------------------------------------------------------------------------
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let tac (x : α) := do
    MetaM.run' (ctx := metaCtx) (s := metaState)
    <| Term.TermElabM.run' (runTac? x) ctx s
  let tac ← Lean.Core.wrapAsyncAsSnapshot tac cancelTk?
  pure (promise, tac)

def asyncRunTactic (tactic : TacticM Unit) (cancelTk? : Option IO.CancelToken := none) :
  TacticM (IO.Promise (Except Exception (Option Expr))) := do
  let (promise, tactic) ← wrapTactic (fun () => tactic) cancelTk?
  let task ← BaseIO.asTask (tactic ())
  Core.logSnapshotTask { stx? := none, task := task, cancelTk? := cancelTk? }
  pure promise

/- Run `tac` on the current goals in parallel -/
def allGoalsAsync (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut results := #[]
  -- Create tasks
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      results := results.push (← asyncRunTactic tac)
  -- Wait for the tasks
  let mut unsolved := #[]
  for (i, (mvarId, result)) in (List.zip mvarIds results.toList).mapIdx (fun id x => (id, x)) do
    match result.result?.get with
    | none =>
      trace[Progress] "Promise got dropped"
      throwError "Promise got dropped"
    | some (.error e) =>
      trace[Progress] "Task {i}: exception: {e.toMessageData}"
      unsolved := unsolved.push mvarId
    | some (.ok x) =>
      -- TODO: how to propagate the information from the `Core.State`? (in particular, I
      -- want to preserve the log)
      match x with
      | .none =>
        trace[Progress] "Task {i}: tactic failed"
        unsolved := unsolved.push mvarId
      | .some x =>
        /- Successfully generated a proof! Assign the meta-variable -/
        --logInfo m!"Task {i}: solved!"
        /- TODO: would it be interesting to introduce theorems for all the proofs
           of the subgoals, so that they get type-checked in parallel? -/
        mvarId.assign x
  setGoals unsolved.toList

/-!
# Test
-/

/-!
## Small helpers, unrelated to asynchronous executions
-/

-- Repeatedly apply a tactic
partial def repeatTac (tac : TacticM Unit) : TacticM Unit := do
  try
    tac
    allGoals (focus (repeatTac tac))
  -- TODO: does this restore the state?
  catch _ => pure ()

def optSplitConj (e : Expr) : Expr × Option Expr :=
  e.consumeMData.withApp fun f args =>
  if f.isConstOf ``And ∧ args.size = 2 then (args[0]!, some (args[1]!))
  else (e, none)

-- Split the goal if it is a conjunction
def splitConjTarget : TacticM Unit := do
  withMainContext do
  let g ← getMainTarget
  -- The tactic was initially implemened with `_root_.Lean.MVarId.apply`
  -- but it tended to mess the goal by unfolding terms, even when it failed
  let (l, r) := optSplitConj g
  match r with
  | none => do throwError "The goal is not a conjunction"
  | some r => do
    let lmvar ← mkFreshExprSyntheticOpaqueMVar l
    let rmvar ← mkFreshExprSyntheticOpaqueMVar r
    let and_intro ← mkAppM ``And.intro #[lmvar, rmvar]
    let g ← getMainGoal
    g.assign and_intro
    let goals ← getUnsolvedGoals
    setGoals (lmvar.mvarId! :: rmvar.mvarId! :: goals)

/-!
## The test
-/

/- Solve the goal by splitting the conjunctions.
Note that `scalarTac` does quite a few things, so it tends to be expensive (in the example below,
looking at the trace for the synchronous case, it requires ~0.016s for every subgoal).
-/
def trySync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoals (do
    ScalarTac.scalarTac {})

syntax "sync_solve" : tactic
elab "sync_solve" : tactic => do trySync

def tryAsync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (do
    ScalarTac.scalarTac {})

syntax "async_solve" : tactic
elab "async_solve" : tactic => do tryAsync

end Aeneas
