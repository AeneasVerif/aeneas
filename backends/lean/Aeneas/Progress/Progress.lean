import Lean
import Aeneas.ScalarTac
import Aeneas.Progress.Init
import Aeneas.Std
import Aeneas.FSimp
import AeneasMeta.Async

namespace Aeneas

namespace Progress

open Lean Elab Term Meta Tactic
open Utils

/-- A special definition that we use to introduce pretty-printed terms in the context.

Note that we should have `α = β`, but we allow the types to not be equal in case `progress` has
a bug and doesn't give the proper arguments: this way we make sure tactics like `progress*?`
will not crash if there is a bug in the code which adds the pretty equality (this is only useful
information for the user).
-/
@[irreducible] def prettyMonadEq {α : Type u} {β : Type v} (_ : Std.Result α) (_ : β) : Type := Unit

macro:max "[> " "let" y:term " ← " x:term " <]"   : term => `(prettyMonadEq $x $y)

@[app_unexpander prettyMonadEq]
def unexpPrettyMonadEqofNat : Lean.PrettyPrinter.Unexpander | `($_ $x $y) => `([> let $y ← $x <]) | _ => throw ()

example (x y z : Std.U32) (_ : [> let z ← x + y <]) : True := by simp

def eq_imp_prettyMonadEq {α : Type u} {β : Type v} (x : Std.Result α) (y : β) : prettyMonadEq x y := by
  unfold prettyMonadEq
  constructor

def traceGoalWithNode (msg : String) : TacticM Unit := Utils.traceGoalWithNode `Progress msg

-- TODO: the scalar types annoyingly often get reduced when we use the progress
-- tactic. We should find a way of controling reduction. For now we use rewriting
-- lemmas to make sure the goal remains clean, but this complexifies proof terms.
-- It seems there used to be a `fold` tactic. Update: there is a `refold_let` in Mathlib
@[defeq] theorem uscalar_u8_eq    : Std.UScalar .U8 = Std.U8 := by rfl
@[defeq] theorem uscalar_u16_eq   : Std.UScalar .U16 = Std.U16 := by rfl
@[defeq] theorem uscalar_u32_eq   : Std.UScalar .U32 = Std.U32 := by rfl
@[defeq] theorem uscalar_u64_eq   : Std.UScalar .U64 = Std.U64 := by rfl
@[defeq] theorem uscalar_u128_eq  : Std.UScalar .U128 = Std.U128 := by rfl
@[defeq] theorem uscalar_usize_eq : Std.UScalar .Usize = Std.Usize := by rfl

@[defeq] theorem iscalar_i8_eq    : Std.IScalar .I8 = Std.I8 := by rfl
@[defeq] theorem iscalar_i16_eq   : Std.IScalar .I16 = Std.I16 := by rfl
@[defeq] theorem iscalar_i32_eq   : Std.IScalar .I32 = Std.I32 := by rfl
@[defeq] theorem iscalar_i64_eq   : Std.IScalar .I64 = Std.I64 := by rfl
@[defeq] theorem iscalar_i128_eq  : Std.IScalar .I128 = Std.I128 := by rfl
@[defeq] theorem iscalar_isize_eq : Std.IScalar .Isize = Std.Isize := by rfl
def scalar_eqs := #[
  ``uscalar_usize_eq, ``uscalar_u8_eq, ``uscalar_u16_eq, ``uscalar_u32_eq, ``uscalar_u64_eq, ``uscalar_u128_eq,
  ``iscalar_isize_eq, ``iscalar_i8_eq, ``iscalar_i16_eq, ``iscalar_i32_eq, ``iscalar_i64_eq, ``iscalar_i128_eq
]

/-- Note that `forall_const` is too general: it can eliminate unused outputs that we actually
want to introduce in the context -/
theorem forall_unit {p : Prop} : (Unit → p) ↔ p := by simp

attribute [progress_simps]
  bind_assoc Std.bind_tc_ok Std.bind_tc_fail Std.bind_tc_div
  /- Those are quite useful to simplify the goal further by eliminating existential quantifiers for instance. -/
  and_assoc Std.Result.ok.injEq Prod.mk.injEq
  exists_eq_left exists_eq_left' exists_eq_right exists_eq_right' exists_eq exists_eq' true_and and_true
  Std.WP.spec_ok
  -- This one gets only applied to full applications of `predn`, which are typically revealed after applying `spec_ok`
  Std.WP.predn_eq

attribute [progress_post_simps]
  -- We often see expressions like `Int.ofNat 3`
  Int.reduceToNat

inductive TheoremOrLocal where
| Theorem (thName : Name)
| Local (asm : LocalDecl)

instance : ToMessageData TheoremOrLocal where
  toMessageData := λ x => match x with | .Theorem thName => m!"{thName}" | .Local asm => m!"{asm.userName}"

instance : Coe TheoremOrLocal Name where
  coe := λ x => match x with | .Theorem thName => thName | .Local asm => asm.userName

inductive UsedTheorem where
  | givenExpr: Expr → UsedTheorem
  | localHyp: LocalDecl → UsedTheorem
  | progressThm : Name → UsedTheorem

namespace UsedTheorem

instance: ToString UsedTheorem where
  toString
  | .givenExpr _e => "given expression"
  | .localHyp decl => s!"local hypothesis {decl.userName.toString}"
  | .progressThm name => s!"progress theorem {name}"

def toSyntax: UsedTheorem → MetaM Syntax.Term
| givenExpr e =>
  -- Remark: exprToSyntax doesn't give the expected result
  Lean.Meta.Tactic.TryThis.delabToRefinableSyntax e
| localHyp decl    => pure <| mkIdent decl.userName
| progressThm name => do
  /- Unresolve the name to make sure that the name is valid, and it is
     as short as possible -/
  let name ← Lean.unresolveNameGlobalAvoidingLocals name
  pure <| mkIdent name

def getType: UsedTheorem -> MetaM (Option Expr)
| givenExpr e => inferType e
| localHyp decl =>inferType decl.toExpr
| progressThm name => do
  if let some cinfo := (←getEnv).find? name then
    let expr := cinfo.value! (allowOpaque := true)
    inferType expr
  else
    return none

end UsedTheorem

structure MainGoal where
  goal : MVarId
  /-- The variables "output" by the monadic function call and introduced in the context -/
  outputs : Array FVarId
  /-- The post-conditions introduced in the context -/
  posts : Array FVarId

inductive OptTask α where
| task (t : Task α)
| none

def OptTask.get (x : OptTask α) : Option α :=
  match x with
  | .task t => some t.get
  | .none => .none

def OptTask.map (f : α → β) (x : OptTask α) (prio : Task.Priority := Task.Priority.default) (sync : Bool := false) : OptTask β :=
  match x with
  | .task t => .task (t.map f prio sync)
  | .none => .none

def OptTask.bind (x : OptTask α) (f : α → Task β) (prio : Task.Priority := Task.Priority.default) (sync : Bool := false) : OptTask β :=
  match x with
  | .task t => .task (t.bind f prio sync)
  | .none => .none

structure Goals where
  /-- The variables for which we could not infer an instantiation -/
  unassignedVars : Array MVarId
  /-- The preconditions that are left to prove.
      We may run tactics asynchronously, which is why we pair the meta variables with promises:
      if the tactic succeeds, the promise gets field with the proof that the meta-variable should get
      assigned to.
   -/
  preconditions : Array (MVarId × OptTask (Option Expr))
  /-- The main goal, if it was not proven -/
  mainGoal : Option MainGoal
deriving Inhabited

structure Stats extends Goals where
  usedTheorem : UsedTheorem

attribute [progress_post_simps]
  Std.IScalar.toNat Std.UScalar.ofNat_val_eq Std.IScalar.ofInt_val_eq

structure Args where
  /-- Asynchronously solve the preconditions? -/
  async : Bool
  /-- Same as `keep`, but use a special wrapper so that the equality gets pretty printed to:
     `[> let z ← x + y <]`
   -/
  keepPretty : Option Name
  /-- Identifiers to use when introducing fresh variables -/
  ids : Array (Option Name)
  /-- Tactic to use to prove preconditions while instantiating meta-variables by
     matching those preconditions with the assumptions in the context. -/
  assumTac : TacticM Unit
  /- Tactic to use to solve the preconditions -/
  solvePreconditionTac : TacticM Unit
  /- Syntax of the tactic provided by the user to solve the remaining proof obligations -/
  byTacSyntax : Option Syntax

/- Analyze a goal comp

   If comp = bind m k then return true and m
   Else return false and comp
-/
def getFirstBind (goalTy : Expr) : MetaM (Bool × Expr) := do
  forallTelescope goalTy fun nvars goalTy => do

  let (spec?, args) := goalTy.consumeMData.withApp (fun f args => (f, args))
  let compTy ← if h: spec?.isConstOf ``Std.WP.spec ∧ args.size = 3
               then pure (args[1])
               else throwError "Goal is not a `spec m P`"

  trace[Progress] "compTy: {compTy}"

  let (bind?, args) := compTy.consumeMData.withApp (fun f args => (f, args))
  trace[Progress] "bind?: {bind?}"
  if h: bind?.isConstOf ``bind ∧ args.size = 6
  then pure (true, args[4])
  else pure (false, compTy)

/-- Attempt to resolve typeclasses. -/
def trySolveTypeclasses (mvarsIds : List MVarId) : TacticM (List MVarId) := do
  withTraceNode `Progress (fun _ => pure m!"trySolveTypeclasses") do
  mvarsIds.filterMapM fun (mvar : MVarId) => do
    trace[Progress] "goal: {mvar}"
    let ty ← instantiateMVars (← mvar.getType)
    ty.withApp fun app _ => do
    if let some (name, _) := app.const? then
      trace[Progress] "Checking application: {name}"
      if not (← isProp (← inferType ty)) then
        /- We eagerly consider the application to be a typeclass
           TODO: this might be dangerous -/
        trace[Progress] "not a prop"
        try
          mvar.withContext do
          let inst ← synthInstance ty
          trace[Progress] "Solved the typeclass"
          let _ ← isDefEq (.mvar mvar) inst
          pure none
        catch _ =>
          trace[Progress] "Could not solve the typeclass"
          pure mvar
      else
        trace[Progress] "Ignoring a prop"
        pure mvar
    else
      trace[Progress] "Could not decompose application"
      pure mvar

/-- Attempt to match a given theorem with the monadic call in the target.
The resulting target should be of the shape:
`qimp_spec P k Q` (or `qimp P Q`)
-/
def tryMatch (isLet : Bool) (th : Expr) :
  TacticM (Array MVarId) := do
  withTraceNode `Progress (fun _ => pure m!"tryMatch") do
  /- Apply the theorem
     We try to match the theorem with the goal
     In order to match the theorem with the goal, we introduce meta-variables for all
     the parameters (i.e., quantified variables and assumpions), and unify those with the goal.
   -/
  /- There might be meta-variables in the type if the theorem comes from a local declaration,
     especially if this declaration was introduced by a tactic -/
  let thTy ← instantiateMVars (← inferType th)
  trace[Progress] "Looked up theorem/assumption type: {thTy}"
  -- Normalize to inline the let-bindings
  let thTy ← normalizeLetBindings thTy
  trace[Progress] "After normalizing the let-bindings: {thTy}"
  trace[Progress] "Theorem: {th}: {← inferType th}"
  -- Introduce the meta-variables for the quantified parameters
  let (mvars, _, thTy) ← forallMetaTelescope thTy
  let th := mkAppN th mvars
  trace[Progress] "Uninstantiated theorem: {th}: {← inferType th}"

  -- `thTy` should be of the shape `spec program post`: we need to retrieve `program`
  let (thHead, thArgs) := thTy.consumeMData.withApp (fun f args => (f, args))
  if !thHead.isConst || thHead.constName! != ``Std.WP.spec then
    throwError "Not a spec theorem"
  let (program, P) ←
    if h: thArgs.size = 3
    then pure (thArgs[1], thArgs[2])
    else throwError "Not a spec theorem"

  let (specMonoBindName, varNum) :=
    if isLet
    then (``Std.WP.spec_bind', 4)
    else (``Std.WP.spec_mono', 2)
  let specMonoBind ← Term.mkConst specMonoBindName
  let specMonoBindTy ← inferType specMonoBind
  trace[Progress] "specMonoBind (isLet:{isLet}): {specMonoBind}: {← inferType specMonoBind}"
  let (specMonoBindMVars, _, specMonoBindTy) ← forallMetaBoundedTelescope specMonoBindTy varNum
  let specMonoBind ← mkAppOptM' specMonoBind (specMonoBindMVars.map some)
  trace[Progress] "Uninstantiated specMonoBind: {specMonoBind}: {← inferType specMonoBind}"

  let specMonoBind := mkAppN specMonoBind #[program, P, th]
  let specMonoBindTy ← inferType specMonoBind
  trace[Progress] "Applied specMonoBind with theorem: {specMonoBind}: {specMonoBindTy}"

  let (specMonoBindMVars, _, specMonoBindTy) ← forallMetaBoundedTelescope specMonoBindTy 1
  if (specMonoBindMVars.size ≠ 1) then throwError "Unreachable"
  let ngoal := specMonoBindMVars[0]!.mvarId!
  let specMonoBind ← mkAppOptM' specMonoBind (specMonoBindMVars.map some)
  trace[Progress] "Applied specMonoBind with theorem: {specMonoBind}: {specMonoBindTy}"

  let mgoal ← Tactic.getMainGoal
  let specMonoBindTy ← inferType specMonoBind
  let goalTy ← mgoal.getType
  trace[Progress] "About to check defeq:\n- specMonoBindTy: {specMonoBindTy}\n- goalTy: {goalTy}"
  let ok ← isDefEq specMonoBindTy goalTy
  if ¬ ok then
    trace[Progress] "Could not unify the theorem with the target"
    throwError "Could not unify the theorem with the target:\n- theorem: {specMonoBindTy}\n- target: {goalTy}"

  mgoal.assign specMonoBind
  trace[Progress] "New goal: {ngoal}"

  let env ← getEnv
  let mvarsIds := mvars.map Expr.mvarId!
  let mvarsIds ← mvarsIds.filterM (fun mvar => do pure (not (← mvar.isAssigned)))

  -- Attempt to resolve the typeclass instances
  let mvarsIds ← trySolveTypeclasses mvarsIds.toList
  let mvarsIds := mvarsIds.toArray

  -- Update the goal and return
  setGoals [ngoal]

  --
  pure mvarsIds

/-- Small helper: introduce the pretty equality (e.g., `[> let z ← x + y <]`) -/
def introPrettyEquality (args : Args) (fExpr : Expr) (outputFVars : Array Expr) :
  TacticM Unit := do
  withTraceNode `Progress (fun _ => pure m!"introPrettyEquality") do
  withMainContext do
  trace[Progress] "fExpr: {fExpr},\noutputFVars: {outputFVars}"
  let some name := args.keepPretty
    | return
  -- Construct the tuple of outputs
  let pat ← mkProdsVal outputFVars.toList
  trace[Progress] "Constructed the pattern: {pat}"
  -- Create the equality
  let e ← mkAppM ``eq_imp_prettyMonadEq #[fExpr, pat]
  trace[Progress] "Created the equality expression: {e}"
  -- Introduce it
  Utils.addDeclTac name e (← inferType e) (asLet := false) fun e => do
    trace[Progress] "Introduced the \"pretty\" let binding: {← inferType e}"

/-- After application of the progress theorem, the target should be of the shape:
  `qimp_spec P k Q` (or `qimp P Q`)

  We transform it to a target of the shape:
  `∀ x₀ ... xₙ, P₀ → ... → Pₘ → k ⦃ Q ⦄`

  Then we introduce `x₀`, ..., `xₙ`, `P₀`, ..., `Pₘ` in the context, by using the names
  provided by the user.

  TODO: we use `simp` a lot, which uselessely explores the monadic term and the post-condition.
  We might want to optimize this.
-/
def introOutputsAndPost (args : Args) (fExpr : Expr) :
  TacticM (Option MainGoal) := do
  withTraceNode `Progress (fun _ => pure m!"introOutputsAndPost") do
  /- Decompose nested uses of `predn` to introduce a sequence of universal quantifiers.
     Note that at the same time we simplify the (monadic) continuation by using
     some monad simp theorems. -/
  let some _ ← withTraceNode `Progress (fun _ => pure m!"simpAt: decomposing nested uses of `predn`") do
    Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false, iota := false}
            { simpThms := #[← progressSimpExt.getTheorems],
              addSimpThms :=
                #[``Std.WP.qimp_spec_predn, ``Std.WP.qimp_spec_unit,
                  ``Std.WP.qimp_predn, ``Std.WP.qimp_unit,
                  ``Std.WP.qimp_spec_exists, ``Std.WP.qimp_exists,
                  ``forall_unit, ``true_imp_iff] }
            (.targets #[] true)
    | trace[Progress] "The main goal was solved!"; return none
  traceGoalWithNode "goal after decomposing the nested `predn`"

  /- Eliminate `qimp_spec`/`qimp` to reveal `imp` and decompose the post-condition into a sequence
     of implications -/
  let some _ ← withTraceNode `Progress (fun _ => pure m!"simpAt: eliminating `qimp_spec` and `qimp`") do
    Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false, iota := false}
            { declsToUnfold := #[``Std.WP.curry, ``Std.WP.predn]
              addSimpThms :=
                #[``Std.WP.qimp_spec_iff, ``Std.WP.qimp_iff,
                  ``Std.WP.imp_and_iff, ``forall_unit, ``true_imp_iff] }
            (.targets #[] true)
    | trace[Progress] "The main goal was solved!"; return none
  traceGoalWithNode "goal after aliminating `qimp_spec` and `qimp` and decomposing the post-condition"

  /- Eliminate `imp`

  Some types get unfolded too much (e.g., `U32` sometimes gets unfolded to `U32) so we use this call
  to `dsimp` to also fold them back. -/
  withTraceNode `Progress (fun _ => pure m!"dsimpAt: eliminating `imp` and folding back scalar types") do
    Simp.dsimpAt true {implicitDefEqProofs := true, failIfUnchanged := false, iota := false}
      { declsToUnfold := #[``Std.WP.imp], addSimpThms := scalar_eqs } (.targets #[] true)
  if (← getUnsolvedGoals).isEmpty then trace[Progress] "The main goal was solved!"; return none
  traceGoalWithNode "goal after aliminating `imp` and folding back the scalar types"

  /- Intro the output variables and the post-conditions.

  We do this in two steps to intro first the output variables, then the pretty equality, and finally
  the post-conditions.
  -/
  let goal ← getMainGoal
  let (nOutputs, nPosts) ← do
    let type ← goal.getType
    let type ← instantiateMVars type
    forallTelescope type.consumeMData fun fvars _ => do
    let n := fvars.size
    if n < args.ids.size then
      logWarning m!"Too many ids provided ({args.ids}): expected ≤ {n} ids, got {args.ids.size}"
    /- Split the fvars between the output variables and the post-conditions -/
    let i? ← fvars.findIdxM? (fun e => do isProp (← inferType e))
    match i? with
    | none => pure (fvars.size, 0)
    | some i => pure (i, fvars.size - i)
  trace[Progress] "Number of output vars: {nOutputs}, number of posts: {nPosts}"
  let mkFreshName (i : Nat) :=
    if i < nOutputs then mkFreshUserName `x
    else mkFreshAnonPropUserName
  let ids ← args.ids.mapIdxM fun i o =>
    match o with
    | some n => pure n
    | none => mkFreshName i
  let ids' ← (Array.range (nOutputs + nPosts - ids.size)).mapIdxM fun i _ => mkFreshName (ids.size + i)
  let ids := ids ++ ids'
  trace[Progress] "ids: {ids}"
  let (outputIds, postsIds) := ids.toList.splitAt nOutputs

  -- Introduce the outputs
  let (outputs, goal) ← goal.introN nOutputs outputIds
  setGoals [goal]
  traceGoalWithNode "goal after introducing the outputs"

  -- Introduce the pretty equality
  introPrettyEquality args fExpr (outputs.map Expr.fvar)
  traceGoalWithNode "goal after introducing the pretty equality"

  -- Introduce the postconditions
  let goal ← getMainGoal
  let (posts, goal) ← goal.introN nPosts postsIds
  setGoals [goal]
  traceGoalWithNode "goal after introducing the post-conditions"

  --
  pure (some ⟨ ← getMainGoal, outputs, posts⟩)

/-- Attempt to solve the preconditions.

    We do this in several phases:
    - we first use the "assumption" tactic to instantiate as many meta-variables as possible,
      and we do so by starting with the preconditions with the highest number of meta-variables
      (this is a way of avoiding spurious instantiations). This helps with the second phase.
    - we then use the other tactic on the preconditions
 -/
def trySolvePreconditions (args : Args) (newPropGoals : List MVarId) : TacticM (List (MVarId × OptTask (Option Expr))) := do
  withTraceNode `Progress (fun _ => pure m!"trySolvePreconditions") do
  let ordPropGoals ←
    newPropGoals.mapM (fun g => do
      let ty ← g.getType
      pure ((← Utils.getMVarIds ty).size, g))
  let ordPropGoals := (ordPropGoals.mergeSort (fun (mvars0, _) (mvars1, _) => mvars0 ≤ mvars1)).reverse
  setGoals (ordPropGoals.map Prod.snd)
  /- First attempt to solve the preconditions in a *synchronous* manner by using the `singleAssumptionTac`.
     We do this to instantiate meta-variables -/
  allGoalsNoRecover (tryTac args.assumTac)
  /- Attempt to resolve the typeclass instances again (we already tried once, but maybe we couldn't
     because some meta-variables were not resolved) -/
  setGoals (← trySolveTypeclasses (← getGoals))
  /- Retrieve the unsolved preconditions - make sure we recover them in the original order -/
  let goals ← newPropGoals.filterMapM (fun g => do if ← g.isAssigned then pure none else pure (some g))
  /- Then attempt to solve the remaining preconditions *asynchronously* -/
  if args.async then
    let promises ← Async.asyncRunTacticOnGoals args.solvePreconditionTac goals (cancelTk? := ← IO.CancelToken.new) (inlineFreshProofs := false)
    let promises : Array (Task _) := promises.map IO.Promise.result?
    let promises : Array (Task _) := promises.map (
        fun o => o.map (sync := true) (fun o => match o with | none | some none => none | some (some o) => some o))
    pure (List.zip goals (promises.toList.map OptTask.task))
  else
    setGoals goals
    allGoalsNoRecover args.solvePreconditionTac
    pure ((← getUnsolvedGoals).map fun g => (g, OptTask.none))

/-- Post-process the main goal.

The main thing we do is simplify the post-conditions.

TODO: simplify or remove this function.
-/
def postprocessMainGoal (mainGoal : Option MainGoal) : TacticM (Option MainGoal) := do
  withTraceNode `Progress (fun _ => pure m!"postprocessMainGoal") do
  match mainGoal with
  | none => pure none
  | some mainGoal =>
    setGoals [mainGoal.goal]
    traceGoalWithNode "current goal"
    -- Simplify the post-conditions
    let args : Simp.SimpArgs :=
      {simpThms := #[← progressPostSimpExt.getTheorems],
       simprocs := #[← progressPostSimprocExt.getSimprocs] }
    let posts ← Simp.simpAt true { maxDischargeDepth := 0, failIfUnchanged := false }
          args (.targets mainGoal.posts false)
    match posts with
    | none =>
      -- We actually closed the goal: we shouldn't get there
      -- TODO: make this more robust
      trace[Progress] "Goal closed by simplifying the introduced post-conditions"
      pure none
    | some posts =>
      /- Simplify the goal again

      Note that we want to simplify targets of the shape:
      `ok ... ⦃ x₀ ... xₙ => ... ⦄`
      -/
      let r ← Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
        {simpThms := #[← progressSimpExt.getTheorems], declsToUnfold := #[``pure]} (.targets #[] true)
      if r.isSome then
        pure (some ({mainGoal with goal := ← getMainGoal, posts} : MainGoal))
      else pure none

def progressWith (args : Args) (isLet:Bool) (fExpr : Expr) (th : Expr) :
  TacticM Goals := do
  withTraceNode `Progress (fun _ => pure m!"progressWith") do
  -- Attempt to instantiate the theorem and introduce it in the context
  let newGoals ← tryMatch isLet th
  --
  withMainContext do
  traceGoalWithNode "current goal"
  let mainGoal ← getMainGoal
  /- Process the pre-conditions as soon as possible (we want to start processing them
     in parallel) -/
  -- Split between the sub-goals which are propositions and the others
  let newGoals ← newGoals.filterM fun mvar => not <$> mvar.isAssigned
  withTraceNode `Progress (fun _ => pure m!"new goals") do trace[Progress] "{newGoals}"
  let (newPropGoals, newNonPropGoals) ←
    newGoals.toList.partitionM fun mvar => do isProp (← mvar.getType)
  withTraceNode `Progress (fun _ => pure m!"prop goals") do trace[Progress] "{newPropGoals}"
  withTraceNode `Progress (fun _ => pure m!"non prop goals") do
    trace[Progress] "{← newNonPropGoals.mapM fun mvarId => do pure ((← mvarId.getDecl).userName, mvarId)}"
  -- Attempt to solve the goals which are propositions
  let newPropGoals ← trySolvePreconditions args newPropGoals
  /- Process the main goal -/
  -- Introduce the outputs and the post-conditions into the context
  setGoals [mainGoal]
  let mainGoal ← introOutputsAndPost args fExpr
  /- Simplify the post-conditions in the main goal - note that we waited until now
      because by solving the preconditions we may have instantiated meta-variables.
      We also simplify the goal again (to simplify let-bindings, etc.) -/
  let mainGoal ← postprocessMainGoal mainGoal
  if let some mainGoal := mainGoal then
    withTraceNode `Progress
      (fun _ => pure m!"Main goal after simplifying the post-conditions and the target") do
      trace[Progress] "{mainGoal.goal}"
  /- Put everything together -/
  let newNonPropGoals ← newNonPropGoals.filterM fun mvar => not <$> mvar.isAssigned
  pure ({ unassignedVars := newNonPropGoals.toArray, preconditions := newPropGoals.toArray, mainGoal })

/-- Small utility: if `args` is not empty, return the name of the app in the first
    arg, if it is a const. -/
def getFirstArgAppName (args : Array Expr) : MetaM (Option Name) := do
  if args.size = 0 then pure none
  else
    args[0]!.withApp fun f _ => do
    if f.isConst then pure (some f.constName)
    else pure none

def getFirstArg (args : Array Expr) : Option Expr := do
  if args.size = 0 then none
  else some args[0]!

/-- Helper: try to apply a theorem.

    Return the list of post-conditions we introduced if it succeeded. -/
def tryApply (args : Args) (isLet:Bool) (fExpr : Expr) (kind : String) (th : Option Expr) :
  TacticM (Option Goals) := do
  let res ← do
    match th with
    | none =>
      trace[Progress] "Could not find a {kind}"
      pure none
    | some th => do
      trace[Progress] "Lookuped up {kind}: {th}"
      -- Apply the theorem
      let res ← do
        try
          let res ← progressWith args isLet fExpr th
          pure (some res)
        catch _ => pure none
  match res with
  | some res => pure (some res)
  | none => pure none

/-- Try to progress with an assumption.
    Return `some` if we succeed, `none` otherwise.
-/
def tryAssumptions (args : Args) (isLet:Bool) (fExpr : Expr) :
  TacticM (Option (Goals × UsedTheorem)) := do
  withTraceNode `Progress (fun _ => pure m!"tryAssumptions") do run
where
  run :=
  withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getAssumptions
  for decl in decls.reverse do
    trace[Progress] "Trying assumption: {decl.userName} : {decl.type}"
    try
      let goal ← progressWith args isLet fExpr decl.toExpr
      return (some (goal, .localHyp decl))
    catch _ => continue
  pure none

def progressAsmsOrLookupTheorem (args : Args) (withTh : Option Expr) :
  TacticM (Goals × UsedTheorem) := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  /- There might be uninstantiated meta-variables in the goal that we need
     to instantiate (otherwise we will get stuck). -/
  let goalTy ← instantiateMVars goalTy
  trace[Progress] "progressAsmsOrLookupTheorem: target: {goalTy}"
  /- Dive into the goal to lookup the theorem
     Remark: if we don't isolate the call to `withProgressSpec` to immediately "close"
     the terms immediately, we may end up with the error:
     "(kernel) declaration has free variables"
     I'm not sure I understand why.
     TODO: we should also check that no quantified variable appears in fExpr.
     If such variables appear, we should just fail because the goal doesn't
     have the proper shape. -/
  let (goalIsLet, fExpr) ← do
    withTraceNode `Progress (fun _ => pure m!"Calling getFirstBind to deconstruct the target") do
    getFirstBind goalTy
  /- If the user provided a theorem/assumption: use it.
     Otherwise, lookup one. -/
  match withTh with
  | some th => do
    let goals ← progressWith args goalIsLet fExpr th
    return (goals, .givenExpr th)
  | none =>
    -- Try all the assumptions one by one and if it fails try to lookup a theorem.
    if let some res ← tryAssumptions args goalIsLet fExpr then return res
    /- It failed: lookup the pspec theorems which match the expression *only
       if the function is a constant* -/
    let fIsConst ← do
      fExpr.consumeMData.withApp fun mf _ => do
      pure mf.isConst
    if ¬ fIsConst then
      trace[Progress] "Progress failed: the target function is not a constant"
      throwError "Progress failed"
    else do
      trace[Progress] "No assumption succeeded: trying to lookup a pspec theorem"
      let pspecs : Array Name ← do
        let thNames ← progressAttr.find? fExpr
        /- TODO: because of reduction, there may be several valid theorems (for
           instance for the scalars). We need to sort them from most specific to
           least specific. For now, we assume the most specific theorems are at
           the end. -/
        let thNames := thNames.reverse
        trace[Progress] "Looked up pspec theorems: {thNames}"
        pure thNames
      -- Try the theorems one by one
      for pspec in pspecs do
        let pspecExpr ← Term.mkConst pspec
        match ← tryApply args goalIsLet fExpr "pspec theorem" pspecExpr with
        | some goals => return (goals, .progressThm pspec)
        | none => pure ()
      -- It failed: try to use the recursive assumptions
      trace[Progress] "Failed using a pspec theorem: trying to use a recursive assumption"
      -- We try to apply the assumptions of kind "auxDecl"
      let ctx ← Lean.MonadLCtx.getLCtx
      let decls ← ctx.getAllDecls
      let decls := decls.filter (λ decl => match decl.kind with
        | .default | .implDetail => false | .auxDecl => true)
      -- TODO: introduce a helper for this
      for decl in decls.reverse do
        trace[Progress] "Trying recursive assumption: {decl.userName} : {decl.type}"
        try
          let goals ← progressWith args goalIsLet fExpr decl.toExpr
          return (goals, .localHyp decl)
        catch _ => continue
      -- Nothing worked: failed
      let msg := "Progress failed: could not find a local assumption or a theorem to apply"
      trace[Progress] msg
      throwError msg

syntax progressArgs := ("with" term)? ("as" " ⟨ " binderIdent,* " ⟩")? ("by" tacticSeq)?

def parseProgressArgs
: TSyntax ``Aeneas.Progress.progressArgs -> TacticM (Option Expr × Array (Option Name) × Option Syntax.Tactic)
| args@`(progressArgs| $[with $pspec:term]? $[as ⟨ $ids,* ⟩]? $[by $byTac]? ) => withMainContext do
  trace[Progress] "Progress arguments: {args.raw}"
  let withTh?: Option Expr ← Option.sequence <| pspec.map fun
    /- We have to make a case disjunction, because if we treat identifiers like
       terms, then Lean will not succeed in infering their implicit parameters
       (`progress` does that by matching against the goal). -/
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[Progress] "With arg (local decl): {stx.raw}"
        return decl.toExpr
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[Progress] "With arg (theorem): {stx.raw}"
        let some e ← Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {pspec}"
        return e
    | term => do
      trace[Progress] "With arg (term): {term}"
      Tactic.elabTerm term none
  if let .some pspec := withTh? then trace[Progress] "With arg: elaborated expression {pspec}"
  let ids := ids.getD ∅
    |>.getElems.map fun
      | `(binderIdent| $name:ident) => some name.getId
      | _ => none
  trace[Progress] "User-provided ids: {ids}"
  let byTac : Option Syntax.Tactic := match byTac with
    | none => none
    | some byTac => some ⟨byTac.raw⟩
  return (withTh?, ids, byTac)
| _ => throwUnsupportedSyntax

def evalProgressCore (async : Bool) (keepPretty : Option Name) (withArg: Option Expr) (ids: Array (Option Name))
  (byTacStx : Option Syntax.Tactic)
  : TacticM Stats := do
  withTraceNode `Progress (fun _ => pure m!"evalProgress") do
  /- Simplify the goal -- TODO: this might close it: we need to check that and abort if necessary,
     and properly track that in the `Stats` -/
  let _ ← Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← progressSimpExt.getTheorems]} (.targets #[] true)
  withMainContext do
  /- Preprocessing step for `singleAssumptionTac` -/
  let singleAssumptionTacDtree ← singleAssumptionTacPreprocess
  /- For scalarTac we have a fast track: if the goal is not a linear
     arithmetic goal, we skip (note that otherwise, scalarTac would try
     to prove a contradiction) -/
  let scalarTac : TacticM Unit := do
    withTraceNode `Progress (fun _ => pure m!"Attempting to solve with `scalarTac`") do
    if ← ScalarTac.goalIsLinearInt then
      /- Also: we don't try to split the goal if it is a conjunction
         (it shouldn't be), but we split the disjunctions. -/
      ScalarTac.scalarTac { split := false, auxTheorem := false }
    else
      throwError "Not a linear arithmetic goal"
  let simpLemmas ← Aeneas.ScalarTac.scalarTacSimpExt.getTheorems
  let localAsms ← pure ((← (← getLCtx).getAssumptions).map LocalDecl.fvarId)
  let simpArgs : Simp.SimpArgs := {simpThms := #[simpLemmas], hypsToUse := localAsms.toArray}
  let simpTac : TacticM Unit := do
    withTraceNode `Progress (fun _ => pure m!"Attempting to solve with `simp [*]`") do
    -- Simplify the goal
    let r ← Simp.simpAt false { maxDischargeDepth := 1 } simpArgs (.targets #[] true)
    -- Raise an error if the goal is not proved
    if r.isSome then throwError "Goal not proved"
  /- We use our custom assumption tactic, which instantiates meta-variables only if there is a single
     assumption matching the goal. -/
  let customAssumTac : TacticM Unit := do
    withTraceNode `Progress (fun _ => pure m!"Attempting to solve with `singleAssumptionTac`") do
    singleAssumptionTacCore singleAssumptionTacDtree
  let env ← getEnv -- We need the original environment below
  /- Also use the tactic provided by the user, if there is -/
  let byTac := match byTacStx with
    | none => []
    | some tacticCode => [
      withTraceNode `Progress (fun _ => pure m!"Attempting to solve with the user tactic: `{byTacStx}`") do
      /- It may happen that the tactic introduces auxiliary theorems to hide some proofs details: because
         the environment containing those proofs will get discarded, we need to inline them -/
      let g ← getMainGoal
      g.withContext do
      let type ← g.getType
      let g' ← mkFreshExprSyntheticOpaqueMVar type
      setGoals [g'.mvarId!]
      evalTactic tacticCode
      g.assign (← Async.inlineFreshProofs env (← instantiateMVarsProfiling g') (rec := true))
    ]
  let solvePreconditionTac :=
    withMainContext do
    withTraceNode `Progress (fun _ => pure m!"Trying to solve a precondition") do
    trace[Progress] "Precondition: {← getMainGoal}"
    try
      firstTacSolve ([simpTac, scalarTac] ++ byTac)
      trace[Progress] "Precondition solved!"
    catch _ =>
      trace[Progress] "Precondition not solved"
  let args : Args := {
    async, keepPretty, ids, assumTac := customAssumTac, solvePreconditionTac, byTacSyntax := byTacStx
  }
  let (goals, usedTheorem) ← progressAsmsOrLookupTheorem args withArg
  trace[Progress] "Progress done"
  return ⟨ goals, usedTheorem ⟩

def asyncOption : Bool := false

def evalProgress
  (async : Bool)
  (keepPretty : Option Name) (withArg: Option Expr) (ids: Array (Option Name))
  (byTac : Option Syntax.Tactic)
  : TacticM UsedTheorem := do
  focus do
  let ⟨goals, usedTheorem⟩ ← evalProgressCore async keepPretty withArg ids byTac
  -- Wait for all the proof attempts to finish
  let mut sgs := #[]
  for (mvarId, proof) in goals.preconditions do
    match proof.get with
    | none | some none => sgs := sgs.push mvarId
    | some (some proof) => mvarId.withContext do
      -- Introduce an auxiliary theorem
      mvarId.withContext do
      let e ← mkAuxTheorem (← mvarId.getType) proof (zetaDelta := true)
      mvarId.assign e
  let mainGoal := match goals.mainGoal with
    | none => []
    | some goal => [goal.goal]
  setGoals (goals.unassignedVars.toList ++ sgs.toList ++ mainGoal)
  pure usedTheorem

/-- The `progress` tactic is used to reason about monadic goals.
It is a bit equivalent to the `mvcgen` tactic from the Lean standard library.

The `progress`tactic works by looking for a suitable theorem (either provided by the user
or looked up in the database of `progress` theorems) which describes the behavior of a monadic
function, then applying it to the current goal. It then introduces the
existentially quantified variables and splits the conjunctions in the
post-condition, before trying to solve the preconditions.

For instance, given the goal:
```lean
h : 2 * (a.val + 1) < U32.max
⊢ ∃ c, (do
  let b ← a + 1#u32
  2 * b) = ok c ∧ c > 0
```
`progress as ⟨ b ⟩` will lookup the theorem:
```lean
theorem UScalar.add_spec (x y : UScalar ty) (h : x.val + y.val < UScalar.max ty) :
  ∃ z, UScalar.add x y = ok z ∧
  z.val = x.val + y.val
```
instantiate it with `x := a` and `y := 1#u32`, (attempt to) prove the precondition
`a.val + 1 < U32.max`, introduce the free variable `b` in the context together
with the assumption `b.val = a.val + 1`, and simplify the goal to remove `let b ← a + 1#u32`,
resulting in:
```lean
h : 2 * (a.val + 1) < U32.max
b : U32
h_b : b.val = a.val + 1
⊢ ∃ c, 2 * b = ok c ∧ c > 0
```

Note that `progress` is able to use the current theorem when doing recursive proofs.

*Remark:** `progress` actually also introduces a dummy variable in the context,
which is pretty printed to display information to the user. For instance, in the
goal above we actually insert a variable `_ : [> b ← a + 1#u32 <]` so that the user keeps
track of the origin of `b`.

**Options:**
The user can provide several optional arguments:
- `with <thm>`: if provided, use the given theorem or local assumption
  to make progress. Otherwise, look for a suitable theorem/assumption.
  The user can provide either the name of a local assumption/theorem,
  or a term representing it.
- `as ⟨ id1, id2, ... ⟩`: provide names for the introduced
  variables and for the post-conditions (in order). If there are more
  variables/conditions than names provided by the user, fresh names are generated.
  If there are more names than variables/conditions, a warning is displayed.
- `by <tactic>`: use the given tactic to solve the preconditions.
- `progress?`: displays the name of the theorem/assumption used.

**`progress?`**: displays the name of the theorem used.

**Alternative syntax:**
The `progress` tactic also supports the following syntax:
`let ⟨ id1, id2, ... ⟩ ← <withArg> by <tactic>`
which is equivalent to:
`progress with <withArg> as ⟨ id1, id2, ... ⟩ by <tactic>`

**The `progress` attribute:**
To make a theorem available for `progress`, the user can tag it with the
`@[progress]` attribute. The theorem must have the following shape:
```lean
theorem thm_name (arg1 : ty1) ... (argn : tyn)
  (h_pre1 : precondition_1) ... (h_prem : precondition_m) :
  ∃ (res1 : res_ty1) ... (resk : res_tyk),
    f arg1 ... argn = ok res1 ∧ postcondition_1 ∧ ... ∧ postcondition_k
```
where `f` is a monadic function with type `Result ...`.

**Ghost Variables:**
It is possible to write progress theorems which use ghost variables, i.e., variables
which do not appear as an input of the monadic function. For instance, in the theorem
below, `map` is a ghost variable as it does not appear in the arguments of `hashmap_insert`.
```lean
theorem hashmap_insert_spec {k v : Type} [BEq k] [Hashable k]
  (hmap : HashMap k v) (key : k) (val : v) (map : k → Option v)
  (hInv : HashMap.inv hmap map) :
  ∃ (newMap : HashMap k v),
    HashMap.insert hmap key val = ok newMap ∧
    ...
```
When encoutering ghost variables, `progress` will try to instantiate them by looking
for local assumptions which match the theorem assumptions, using heuristics to find
the best instantiation when several are possible.

**Progress\*:**
When the user wants to make progress by several step, they can use the `progress*` tactic,
which repeatedly calls `progress` until no further progress can be made. See the documentation
of `progress*` for more details.
-/
elab (name := progress) "progress" args:progressArgs : tactic => do
  let (withArg, ids, byTac) ← parseProgressArgs args
  evalProgress asyncOption none withArg ids byTac *> return ()

@[inherit_doc progress]
elab tk:"progress?" args:progressArgs : tactic => do
  let (withArg, ids, byTac) ← parseProgressArgs args
  let stats ← evalProgress asyncOption none withArg ids byTac
  let mut stxArgs := args.raw
  if stxArgs[0].isNone then
    let withArg := mkNullNode #[mkAtom "with", ← stats.toSyntax]
    stxArgs := stxArgs.setArg 0 withArg
  let tac := mkNode `Aeneas.Progress.progress #[mkAtom "progress", stxArgs]
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq tac
  Meta.Tactic.TryThis.addSuggestion tk fmt.pretty (origSpan? := ← getRef)

@[inherit_doc progress]
syntax (name := letProgress) "let" noWs "*" " ⟨ " binderIdent,* " ⟩" colGe
  " ← " colGe (term <|> "*" <|> "*?") ("by" tacticSeq)? : tactic

def parseLetProgress
: TSyntax ``Aeneas.Progress.letProgress ->
  TacticM (Option Expr × Bool × Array (Option Name) × Option Syntax.Tactic)
| args@`(tactic| let* ⟨ $ids,* ⟩ ← $pspec $[by $byTac]?) =>  withMainContext do
  trace[Progress] "Progress arguments: {args.raw}"
  let ((withThm, suggest) : (Option Expr × Bool)) ← do
    /- We have to make a case disjunction, because if we treat identifiers like
      terms, then Lean will not succeed in infering their implicit parameters
      (`progress` does that by matching against the goal). -/
    match pspec with
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[Progress] "With arg (local decl): {stx.raw}"
        pure (some decl.toExpr, false)
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[Progress] "With arg (theorem): {stx.raw}"
        let some e ← Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {pspec}"
        pure (some e, false)
    | term => do
      trace[Progress] "term.raw.getKind: {term.raw.getKind}"
      if term.raw.getKind = `token.«*» then
        trace[Progress] "With arg: *"
        pure (none, false)
      else if term.raw.getKind = `token.«*?» then
        trace[Progress] "With arg: ?"
        pure (none, true)
      else
        trace[Progress] "With arg (term): {term}"
        pure (some (← Tactic.elabTerm term none), false)
  let ids := ids.getElems.map fun
      | `(binderIdent| $name:ident) => some name.getId
      | _ => none
  let byTac : Option Syntax.Tactic := match byTac with
    | none => none
    | some byTac => some ⟨byTac.raw⟩
  trace[Progress] "User-provided ids: {ids}"
  return (withThm, suggest, ids, byTac)
| _ => throwUnsupportedSyntax

elab tk:letProgress : tactic => do
  withMainContext do
  let (withArg, suggest, ids, byTac) ← parseLetProgress tk
  let stats ← evalProgress asyncOption (some (.str .anonymous "_")) withArg ids byTac
  let mut stxArgs := tk.raw
  if suggest then
    trace[Progress] "suggest is true"
    let withArg ← stats.toSyntax
    stxArgs := stxArgs.setArg 6 withArg
    let stxArgs' : TSyntax `Aeneas.Progress.letProgress := ⟨ stxArgs ⟩
    trace[Progress] "stxArgs': {stxArgs}"
    Meta.Tactic.TryThis.addSuggestion tk stxArgs' (origSpan? := ← getRef)

namespace Test
  open Std Result

  -- Show the traces:
  -- set_option trace.Progress true
  -- set_option pp.rawOnError true

  set_option says.verify true

  -- The following command displays the database of theorems:
  -- #eval showStoredProgressThms
  open alloc.vec

  /- This test case checks what happens when `progress`:
     - manages to solve the current goal
     - but doesn't solve some preconditions
     At some point there was a bug with the goal management.
  -/
  /--
  error: unsolved goals
case hmax
ty : UScalarTy
x y : UScalar ty
⊢ ↑x + ↑y ≤ UScalar.max ty
  -/
  #guard_msgs in
  example {ty} {x y : UScalar ty} :
    x + y ⦃ _ => True ⦄ := by
    progress as ⟨ z, h1 ⟩

  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ _ => True ⦄ := by
    progress as ⟨ z, h1 ⟩

  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ _ => True ⦄ := by
    let* ⟨ z, h1 ⟩ ← *

  -- Checking that we properly handle tuple decomposition in post-conditions
  def addToPair (x : Nat) := Result.ok (x + 1, x + 2)
  theorem  addToPair_spec (x : Nat) : addToPair x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
    by simp [addToPair]

  /--
error: unsolved goals
case a
x y z : ℕ
h : y = x + 1
_✝¹ : z = x + 2
y1 z1 : ℕ
h1 : y1 = y + 1
_✝ : z1 = y + 2
⊢ y1 = x + 2
  -/
  #guard_msgs in
  example (x : Nat) :
    (do
      let (y, _) ← addToPair x
      addToPair y) ⦃ y _ => y = x + 2 ⦄ := by
    progress with addToPair_spec as ⟨ y, z, h ⟩
    progress with addToPair_spec as ⟨ y1, z1, h1 ⟩

  /--
  info: Try this:
  [apply] let* ⟨ z, h1 ⟩ ← UScalar.add_spec
  -/
  #guard_msgs in
  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ _ => True ⦄ := by
    let* ⟨ z, h1 ⟩ ← *?

  /--
info: example
  (ty : UScalarTy)
  (x : UScalar ty)
  (y : UScalar ty)
  (h : ↑x + ↑y ≤ UScalar.max ty)
  (z : UScalar ty)
  (_ : [> let z ← x + y <])
  (h1 : ↑z = ↑x + ↑y) :
  ↑z = ↑x + ↑y
  := by sorry
-/
  #guard_msgs in
  set_option linter.unusedTactic false in
  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    let* ⟨ z, h1 ⟩ ← UScalar.add_spec
    extract_goal0
    scalar_tac

  /--
info: example
  (ty : UScalarTy)
  (x : UScalar ty)
  (y : UScalar ty)
  (h : 2 * ↑x + ↑y ≤ UScalar.max ty)
  (z1 : UScalar ty)
  (__1 : [> let z1 ← x + y <])
  (h1 : ↑z1 = ↑x + ↑y)
  (z2 : UScalar ty)
  (_ : [> let z2 ← z1 + x <])
  (h2 : ↑z2 = ↑z1 + ↑x) :
  ↑z2 = 2 * ↑x + ↑y
  := by sorry
-/
  #guard_msgs in
  set_option linter.unusedTactic false in
  example {ty} {x y : UScalar ty} (h : 2 * x.val + y.val ≤ UScalar.max ty) :
    (do
      let z1 ← x + y
      z1 + x) ⦃ z => z.val = 2 * x.val + y.val ⦄ := by
    let* ⟨ z1, h1 ⟩ ← UScalar.add_spec
    let* ⟨ z2, h2 ⟩ ← UScalar.add_spec
    extract_goal0
    scalar_tac

  example {ty} {x y : UScalar ty} (h : 2 * x.val + y.val ≤ UScalar.max ty) :
    (do
      let z1 ← x + y
      z1 + x) ⦃ z => z.val = 2 * x.val + y.val ⦄ := by
    progress with UScalar.add_spec as ⟨ z1, h1 ⟩
    progress with UScalar.add_spec as ⟨ z2, h2 ⟩
    scalar_tac

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress as ⟨ z, h1 ⟩
    scalar_tac

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress as ⟨ z, h1 ⟩
    scalar_tac

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress? as ⟨ z, h1 ⟩ says progress with UScalar.add_spec as ⟨ z, h1 ⟩
    scalar_tac

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress? as ⟨ z, h1 ⟩ says progress with IScalar.add_spec as ⟨ z, h1 ⟩
    scalar_tac

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress with UScalar.add_spec as ⟨ z ⟩
    scalar_tac

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress with IScalar.add_spec as ⟨ z ⟩
    scalar_tac

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    -- This spec theorem is suboptimal (compared to `U32.add_spec`), but it is good to check that it works
    progress with UScalar.add_spec as ⟨ z, h1 ⟩
    scalar_tac

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress with U32.add_spec as ⟨ z, h1 ⟩
    scalar_tac

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    progress as ⟨ z, h1 ⟩
    scalar_tac

  /- Checking that universe instantiation works: the original spec uses
     `α : Type u` where u is quantified, while here we use `α : Type 0` -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    v.update i x ⦃ nv => nv.val = v.val.set i.val x ⦄ := by
    progress
    simp [*]

  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    v.update i x ⦃ nv => nv.val = v.val.set i.val x ⦄ := by
    progress? says progress with Vec.update_spec
    simp [*]

  /- Checking that progress can handle nested blocks -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    (do
        (do
          let _ ← v.update i x
          .ok ())
        .ok ()) ⦃ _ => True ⦄
      := by
    progress

  /- Checking the case where simplifying the goal after instantiating the
     pspec theorem actually solves it, and where the function is not a constant.
     We also test the case where the function under scrutinee is not a constant. -/
  example {x : U32}
    (f : U32 → Std.Result Unit) (h : ∀ x, f x ⦃ _ => True ⦄) :
    f x ⦃ _ => True ⦄ := by
    progress

  example {x : U32}
    (f : U32 → Std.Result Unit) (h : ∀ x, f x ⦃ _ => True ⦄) :
    f x ⦃ _ => True ⦄ := by
    progress? says progress with h

  /- The use of `right` introduces a meta-variable in the goal, that we
     need to instantiate (otherwise `progress` gets stuck) -/
  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    False ∨ x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    right
    progress as ⟨ z, h1 ⟩
    scalar_tac

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    False ∨ x + y ⦃ z => z.val = x.val + y.val ⦄ := by
    right
    progress? as ⟨ z, h1 ⟩ says progress with IScalar.add_spec as ⟨ z, h1 ⟩
    scalar_tac

  /--
error: unsolved goals
case a
x y : U32
f : U32 → U32 → Result U32
hf : ∀ (x y : U32), ↑x < 10 → ↑y < 10 → f x y ⦃ x✝ => True ⦄
⊢ ↑x < 10

case a
x y : U32
f : U32 → U32 → Result U32
hf : ∀ (x y : U32), ↑x < 10 → ↑y < 10 → f x y ⦃ x✝ => True ⦄
⊢ ↑y < 10
  -/
  #guard_msgs in
  example {x y} (f : U32 → U32 → Result U32) (hf : ∀ x y, x.val < 10 → y.val < 10 → f x y ⦃ _ => True⦄) :
    f x y ⦃ _ => True⦄ := by
    progress

  -- Testing with mutually recursive definitions
  mutual
    inductive Tree
    | mk : Trees → Tree

    inductive Trees
    | nil
    | cons : Tree → Trees → Trees
  end

  mutual
    def Tree.size (t : Tree) : Std.Result Int :=
      match t with
      | .mk trees => trees.size

    def Trees.size (t : Trees) : Std.Result Int :=
      match t with
      | .nil => ok 0
      | .cons t t' => do
        let s ← t.size
        let s' ← t'.size
        ok (s + s')
  end

  section
    mutual
      @[local progress]
      theorem Tree.size_spec (t : Tree) :
        t.size ⦃ i => i ≥ 0 ⦄ := by
        cases h: t -- TODO: `cases t` doesn't work
        simp [Tree.size]
        progress
        scalar_tac

      @[local progress]
      theorem Trees.size_spec (t : Trees) :
        t.size ⦃ i => i ≥ 0 ⦄ := by
        cases h: t <;> simp [Trees.size] -- TODO: `cases t` doesn't work
        progress
        progress? says progress with Trees.size_spec
        scalar_tac
    end
  end

  -- Testing progress on theorems containing local let-bindings
  def add (x y : U32) : Std.Result U32 := x + y

  section
    /- Testing progress on theorems containing local let-bindings as well as
       the `local` attribute kind -/
    @[local progress] theorem add_spec' (x y : U32) (h : x.val + y.val ≤ U32.max) :
      let tot := x.val + y.val
      x + y ⦃ z => z.val = tot ⦄ := by
      simp
      progress with U32.add_spec
      scalar_tac

    def add1 (x y : U32) : Std.Result U32 := do
      let z ← x + y
      z + z

    example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
      add1 x y ⦃ _ => True ⦄ := by
      rw [add1]
      progress? as ⟨ z1, h ⟩ says progress with add_spec' as ⟨ z1, h ⟩
      progress? as ⟨ z2, h ⟩ says progress with add_spec' as ⟨ z2, h ⟩

    /--
    error: unsolved goals
case h
x y x✝ : U32
_✝ : ↑x✝ = ↑x + ↑y
⊢ ↑x✝ + ↑x✝ ≤ U32.max

case h
x y : U32
⊢ ↑x + ↑y ≤ U32.max
    -/
    #guard_msgs in
    example (x y : U32) :
      add1 x y ⦃ z => True ⦄ := by
      unfold add1
      progress
      swap; progress
  end

  /- Checking that `add_spec'` went out of scope -/
  example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
    add1 x y ⦃ _ => True ⦄ := by
    rw [add1]
    progress? as ⟨ z1, h ⟩ says progress with U32.add_spec as ⟨ z1, h ⟩
    progress? as ⟨ z2, h ⟩ says progress with U32.add_spec as ⟨ z2, h ⟩
end Test

namespace Test
  open Std Result

  variable {α} (P : ℕ → List α → Prop)
  variable (f : List α → Std.Result Bool)
  variable (f_spec : ∀ l i, P i l → f l ⦃ _ => True ⦄)

  example {i} (l : List α) (h : P i l) :
    f l ⦃ _ => True ⦄ := by
    progress? as ⟨ b ⟩ says progress with f_spec as ⟨ b ⟩

  /- Progress using a term -/
  example {x: U32}
    (f : U32 → Std.Result Unit)
    (h : ∀ x, f x ⦃ _ => True ⦄):
      f x ⦃ () => True ⦄ := by
      progress? with (show ∀ x, f x ⦃ _ => True ⦄ by exact h) says progress with(show ∀ x, f x ⦃ _ => True ⦄ by exact h)
end Test

namespace Test
  open Std Result

  /- Progress using a term -/
  example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
    add1 x y ⦃ _ => True ⦄ := by
    rw [add1]
    have h1 := add_spec'
    progress with h1 as ⟨ z1, h ⟩
    progress with add_spec' z1 as ⟨ z2, h ⟩

  /- Pretty equality when the output type is unit -/
  /--
  info: example
  (y : U32)
  (h1 : ↑y < 100) :
  massert (y < 100#u32) ⦃ x✝ => True ⦄
  := by sorry
  -/
  #guard_msgs in
  example (x y : U32) (h0 : x.val < 100) (h1 : y.val < 100) :
    (do
      massert (x < 100#u32)
      massert (y < 100#u32)) ⦃ _ => True ⦄
    := by
    let* ⟨⟩ ← massert_spec
    extract_goal0
    let* ⟨⟩ ← massert_spec

  set_option linter.unusedTactic false in
  /--
info: example
  (c : U32)
  (c' : U32)
  (_✝ : (↑c' : ℕ) = (↑c : ℕ) >>> 16)
  (hc' : c'.bv = c.bv >>> 16) :
  c'.bv = c.bv >>> 16
  := by sorry
  -/
  #guard_msgs in
  example (c : U32) :
    (do
          let c1 ← c >>> 16#i32
          ok c1) ⦃ c' => c'.bv = c.bv >>> 16 ⦄
    := by
    progress as ⟨ c', _, hc' ⟩ -- we have: `hc' : c'.bv = c.bv >>> 16`
    extract_goal1
    fsimp [hc']

  example (x y : U32) (h : x.val + y.val < U32.max) :
    (do
      let z ← x + y
      ok (x, y, z)) ⦃ x y z => z.val = x.val + y.val ⦄ := by
    progress as ⟨ z ⟩
    scalar_tac

  /- Example with an existential -/
  /--
  error: unsolved goals
case a
x : U32
f : U32 → Result U32
h : ∀ (x : U32), f x ⦃ y => ∃ z > 0, ↑y = ↑x + z ⦄
y : ℕ
z : U32
_✝¹ : y > 0
_✝ : ↑z = ↑x + y
⊢ ↑z > ↑x
  -/
  #guard_msgs in
  example (x : U32) (f : U32 → Result U32) (h : ∀ x, f x ⦃ y => ∃ z, z > 0 ∧ y.val = x.val + z ⦄) :
    f x ⦃ y => y.val > x.val ⦄ := by
    progress as ⟨ y, z ⟩

  /- Inhabited -/
  def get (x : Option α) : Result α :=
    match x with
    | none => fail .panic
    | some x => ok x

  -- `Inhabited α` is not necessary: we add it for the purpose of testing
  theorem get_spec [Inhabited α] (x : Option α) (h : x.isSome) : get x ⦃ _ => True ⦄ := by
    cases x <;> grind [get]

  example [Inhabited α] (x : Option α) (h : x.isSome) : get x ⦃ _ => True ⦄ := by
    progress with get_spec

  namespace Ntt
    def wfArray (_ : Array U16 256#usize) : Prop := True

    def nttLayer (a : Array U16 256#usize) (_k : Usize) (_len : Usize) : Std.Result (Array U16 256#usize) := ok a

    def toPoly (a : Array U16 256#usize) : List U16 := a.val

    def Spec.nttLayer (a : List U16) (_ : Nat) (len : Nat) (_ : Nat) (_ : 0 < len) : List U16 := a

    @[local progress]
    theorem nttLayer_spec
      (peSrc : Array U16 256#usize)
      (k : Usize) (len : Usize)
      (_ : wfArray peSrc)
      (_ : k.val = 2^(k.val.log2) ∧ k.val.log2 < 7)
      (_ : len.val = 128 / k.val)
      (hLenPos : 0 < len.val) :
      nttLayer peSrc k len ⦃ peSrc' =>
        toPoly peSrc' = Spec.nttLayer (toPoly peSrc) k.val len.val 0 hLenPos ∧
        wfArray peSrc' ⦄ := by
      simp [wfArray, nttLayer, toPoly, Spec.nttLayer]

    def ntt (x : Array U16 256#usize) : Std.Result (Array U16 256#usize) := do
      let x ← nttLayer x 1#usize 128#usize
      let x ← nttLayer x 2#usize 64#usize
      let x ← nttLayer x 4#usize 32#usize
      let x ← nttLayer x 8#usize 16#usize
      let x ← nttLayer x 16#usize 8#usize
      let x ← nttLayer x 32#usize 4#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      let x ← nttLayer x 64#usize 2#usize
      ok x

    set_option maxHeartbeats 800000
    theorem ntt_spec (peSrc : Std.Array U16 256#usize)
      (hWf : wfArray peSrc) :
      ntt peSrc ⦃ peSrc1 => wfArray peSrc1 ⦄
      := by
      unfold ntt
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      assumption

    set_option maxHeartbeats 800000
    theorem ntt_spec' (peSrc : Std.Array U16 256#usize)
      (hWf : wfArray peSrc) :
      ntt peSrc ⦃ peSrc1 => wfArray peSrc1 ⦄
      := by
      unfold ntt
      progress
      progress;
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      progress
      assumption

  end Ntt

end Test

end Progress

end Aeneas
