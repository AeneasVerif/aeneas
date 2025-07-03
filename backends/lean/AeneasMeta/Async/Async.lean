import AeneasMeta.Utils

namespace Aeneas.Async

open Lean Elab Term Meta Tactic
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
partial def inlineFreshProofs (env0 : Environment) (e : Expr) (rec := false) : MetaM Expr := do
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
        /- Note that we don't re-explore the body: we don't expect tactics to
           introduce nested theorems -/
        let body :=
          if levels.isEmpty then body
          else
            let levels := Std.HashMap.ofList (List.zip (List.map Level.param levels) us)
            let body := body.replaceLevel (Std.HashMap.get? levels)
            body
        /- Re-explore the body -/
        if rec then inline body else pure body
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
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken)
  (inlineProofs : Bool) :
  TacticM (IO.Promise (Option Expr) × (α → BaseIO Language.SnapshotTree)) := do
  let env0 ← getEnv
  withMainContext do
  -- The code below is adapted from `Lean.Elab.Tactic.tacticToDischarge` --
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let mvar ← mkFreshExprSyntheticOpaqueMVar (← getMainTarget) `simp.discharger
  let s ← ref.get
  let promise : IO.Promise (Option Expr) ← IO.Promise.new
  let runTac? (x : α) : TermElabM Unit :=
    try
      --Term.withoutModifyingElabMetaStateWithInfo do
        let ngoals ← --Term.withSynthesize (postpone := .no) do
          Tactic.run mvar.mvarId! (tactic x)
        if ngoals.isEmpty then
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            promise.resolve none
          else
            /- Inline the proof of auxiliary theorems introduced by tactics like `omega`. -/
            let result ← if inlineProofs then inlineFreshProofs env0 result else pure result
            promise.resolve (some result)
        else promise.resolve none
    catch _ => promise.resolve none
  --------------------------------------------------------------------------
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let tac ← Lean.Elab.Term.wrapAsyncAsSnapshot runTac? cancelTk?
  pure (promise, tac)

def asyncRunTactic (tactic : TacticM Unit) (cancelTk? : Option IO.CancelToken := none)
  (prio : Task.Priority := Task.Priority.default) (inlineFreshProofs := true)
  (stx? : Option Syntax := none) :
  TacticM (IO.Promise (Option Expr)) := do
  let (promise, tactic) ← wrapTactic (fun () => tactic) cancelTk? inlineFreshProofs
  let task ← BaseIO.asTask (tactic ()) prio
  Core.logSnapshotTask { stx?, task := task, cancelTk? := cancelTk? }
  pure promise

/- Run `tac` on the current goals in parallel -/
def asyncRunTacticOnGoals (tac : TacticM Unit) (mvarIds : List MVarId)
  (cancelTk? : Option IO.CancelToken := none) (prio : Task.Priority := Task.Priority.default)
  (inlineFreshProofs : Bool := true) (stx? : Option Syntax := none) :
  TacticM (Array (IO.Promise (Option Expr))) := do
  let mut results := #[]
  -- Create tasks
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      results := results.push (← asyncRunTactic tac cancelTk? prio inlineFreshProofs stx?)
  pure results

/- Run `tac` on the current goals in parallel -/
def allGoalsAsync (tac : TacticM Unit)
  (cancelTk? : Option IO.CancelToken := none)
  (prio : Task.Priority := Task.Priority.default)
  (inlineFreshProofs : Bool := true) (stx? : Option Syntax := none) :
  TacticM Unit := do
  let mvarIds ← getGoals
  let promises ← asyncRunTacticOnGoals tac mvarIds cancelTk? prio inlineFreshProofs stx?
  -- Wait for the tasks
  let mut unsolved := #[]
  for (mvarId, promise) in List.zip mvarIds promises.toList do
    match promise.result?.get with
    | none =>
      unsolved := unsolved.push mvarId
    | some x =>
      match x with
      | .none =>
        unsolved := unsolved.push mvarId
      | .some x =>
        /- Successfully generated a proof! Assign the meta-variable -/
        mvarId.assign x
  setGoals unsolved.toList

end Aeneas.Async
