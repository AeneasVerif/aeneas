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
        /- Note that we don't re-explore the body: we don't expect tactics to
           introduce nested theorems -/
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
            /- Inline the theorems introduced by `omega`. Note that doing this
               has an impact on the performance, but I would expect it to be
               compensated by the fact that: 1. we do this in parallel,
               2. checking the final proof term is also done asynchronously
               and should not have an impact on the time it takes to refresh
               the goals displayed to the user (correct?).
             -/
            let result ← inlineFreshProofs env0 result
            promise.resolve (some result)
        else promise.resolve none
    catch e => promise.resolve none
  --------------------------------------------------------------------------
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let tac (x : α) := do
    MetaM.run' (ctx := metaCtx) (s := metaState)
    <| Term.TermElabM.run' (runTac? x) ctx s
  let tac ← Lean.Core.wrapAsyncAsSnapshot tac cancelTk?
  pure (promise, tac)

def asyncRunTactic (tactic : TacticM Unit) (cancelTk? : Option IO.CancelToken := none)
  (prio : Task.Priority := Task.Priority.default) :
  TacticM (IO.Promise (Option Expr)) := do
  let (promise, tactic) ← wrapTactic (fun () => tactic) cancelTk?
  let task ← BaseIO.asTask (tactic ()) prio
  Core.logSnapshotTask { stx? := none, task := task, cancelTk? := cancelTk? }
  pure promise

/- Run `tac` on the current goals in parallel -/
def asyncRunTacticOnGoals (tac : TacticM Unit) (mvarIds : List MVarId)
  (cancelTk? : Option IO.CancelToken := none) (prio : Task.Priority := Task.Priority.default) :
  TacticM (Array (IO.Promise (Option Expr))) := do
  let mut results := #[]
  -- Create tasks
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      results := results.push (← asyncRunTactic tac cancelTk? prio)
  pure results

end Aeneas.Async
