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

/-- A special definition that we use to introduce pretty-printed terms in the context -/
@[irreducible] def prettyMonadEq {α : Type u} (_ : Std.Result α) (_ : α) : Type := Unit

macro:max "[> " "let" y:term " ← " x:term " <]"   : term => `(prettyMonadEq $x $y)

@[app_unexpander prettyMonadEq]
def unexpPrettyMonadEqofNat : Lean.PrettyPrinter.Unexpander | `($_ $x $y) => `([> let $y ← $x <]) | _ => throw ()

example (x y z : Std.U32) (_ : [> let z ← (x + y) <]) : True := by simp

def eq_imp_prettyMonadEq {α : Type u} {x : Std.Result α} {y : α} (_ : x = .ok y) : prettyMonadEq x y := by
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

attribute [progress_simps]
  Std.bind_tc_ok Std.bind_tc_fail Std.bind_tc_div
  /- Those are quite useful to simplify the goal further by eliminating existential quantifiers for instance. -/
  and_assoc Std.Result.ok.injEq Prod.mk.injEq
  exists_eq_left exists_eq_left' exists_eq_right exists_eq_right' exists_eq exists_eq' true_and and_true

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
  /-- Should we preserve the monadic equality in the context?

     For instance, if making progress on: `let z ← x + y; ...`
     We would introduce an assumption: `h : x + y = ok z`
   -/
  keep : Option Name
  /-- Same as `keep`, but use a special wrapper so that the equality gets pretty printed to:
     `[> let z ← x + y <]`
   -/
  keepPretty : Option Name
  /-- Identifiers to use when introducing fresh variables -/
  ids : Array (Option Name)
  /-- Should we split the conjunctions in the post-condition? -/
  splitPost : Bool
  /-- Tactic to use to prove preconditions while instantiating meta-variables by
     matching those preconditions with the assumptions in the context. -/
  assumTac : TacticM Unit
  /- Tactic to use to solve the preconditions -/
  solvePreconditionTac : TacticM Unit
  /- Syntax of the tactic provided by the user to solve the remaining proof obligations -/
  byTacSyntax : Option Syntax

/-- Attempt to match a given theorem with the monadic call in the goal,
    and introduce the instantiated theorem in the context if it succeeds.

    If the instantiation succeeds, we return the introduced meta-variables as
    well as the new assumption corresponding to the instantiated theorem (the
    expression is an fvar). We raise an exception otherwise.
 -/
def tryMatch (args : Args) (fExpr : Expr) (th : Expr) :
  TacticM (Array MVarId × Expr) := do
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
  monadTelescope thTy fun xs _zs thBody _ _ => do
  let (mvars, binders) := xs.unzip
  let mvars := mvars.map .mvar
  -- Match the body with the target
  trace[Progress] "Matching:\n- body:\n{thBody}\n- target:\n{fExpr}"
  let ok ← isDefEq thBody fExpr
  if ¬ ok then
    trace[Progress] "Could not unify the theorem with the target"
    throwError "Could not unify the theorem with the target:\n- theorem: {thBody}\n- target: {fExpr}"
  let mgoal ← Tactic.getMainGoal
  postprocessAppMVars `progress mgoal mvars binders true true
  Term.synthesizeSyntheticMVarsNoPostponing
  let thBody ← instantiateMVars thBody
  trace[Progress] "thBody (after instantiation): {thBody}"
  -- Add the instantiated theorem to the assumptions (we apply it on the metavariables).
  let th := mkAppN th mvars
  trace[Progress] "Instantiated theorem reusing the metavariables: {th}"
  let asmName ← do match args.keep with | none => mkFreshAnonPropUserName | some n => do pure n
  let thTy ← inferType th
  trace[Progress] "thTy (after application): {thTy}"
  /- Normalize the let-bindings (note that we already inlined the let bindings once above when analizing
     the theorem, now we do it again on the instantiated theorem - there is probably a smarter way to do,
     but it doesn't really matter). -/
  -- TODO: actually we might want to let the user insert them in the context
  let thTy ← normalizeLetBindings thTy
  trace[Progress] "thTy (after normalizing let-bindings): {thTy}"
  Utils.addDeclTac asmName th thTy (asLet := false) fun thAsm => pure (mvars.map Expr.mvarId!, thAsm)

/-- Under the condition that `thAsm` is of the shape:
   `∃ x1 ... xn, f args = ... ∧ ...`

  introduce the existentially quantified variables and split the top-most
  conjunction if there is one. We use the provided `ids` list to name the
  introduced variables.
-/
def splitExistsEqAndPost (args : Args) (thAsm : Expr) :
  TacticM (Option MainGoal) := do
  withTraceNode `Progress (fun _ => pure m!"splitExistsEqAndPost") do
  splitAllExistsTac thAsm args.ids.toList fun fvarIds h ids => do
  /- Introduce the pretty equality if the user requests it.
      We take care of introducing it *before* splitting the post-conditions, so that those appear
      after it.
    -/
  match args.keepPretty with
  | none => pure ()
  | some name =>
    trace[Progress] "About to introduce the pretty equality"
    let hTy ← inferType h
    trace[Progress] "introPrettyEq: h: {hTy}"
    let h ← do
      if ← isConj hTy then do
        mkAppM ``And.left #[h]
      else do pure h
    /- Do *not* introduce an equality if the return type is `()` -/
    let hTy ← inferType h
    hTy.withApp fun _ args => do -- Deconstruct the equality
    trace[Progress] "Checking if type is (): after deconstructing the equality: {args}"
    args[0]!.withApp fun _ args => do -- Deconstruct the `Result`
    trace[Progress] "Checking if type is (): after deconstructing Result: {args}"
    let arg0 := args[0]!
    if arg0.isConst ∧ (arg0.constName == ``Unit ∨ arg0.constName == ``PUnit) then
      trace[Progress] "Not introducing a pretty equality because the output type is `()`"
    else
      trace[Progress] "h: {← inferType h}"
      trace[Progress] "Introducing the \"pretty\" let binding"
      let e ← mkAppM ``eq_imp_prettyMonadEq #[h]
      Utils.addDeclTac name e (← inferType e) (asLet := false) fun _ => do
      traceGoalWithNode "Introduced the \"pretty\" let binding"

  /- Split the conjunctions.
      For the conjunctions, we split according once to separate the equality `f ... = .ret ...`
      from the postcondition, if there is, then continue to split the postcondition if there
      are remaining ids. -/
  let splitEqAndPost (k : Expr → Option Expr → List (Option Name) → TacticM (Option MainGoal)) :
    TacticM (Option MainGoal) := do
    let hTy ← inferType h
    if ← isConj hTy then
      let hName := (← h.fvarId!.getDecl).userName
      let (optIds, ids) ← do
        match ids with
        | [] => do pure (some (hName, ← mkFreshAnonPropUserName), [])
        | none :: ids => do pure (some (hName, ← mkFreshAnonPropUserName), ids)
        | some id :: ids => do pure (some (hName, id), ids)
      splitConjTac h optIds (fun hEq hPost => k hEq (some hPost) ids)
    else
      k h none ids
  /- Simplify the target by using the equality and some monad simplifications,
      then continue splitting the post-condition -/
  -- TODO: this is dangerous if we want to use a local assumption to make progress.
  -- We shouldn't simplify the goal with the equality, then simplify again.
  splitEqAndPost fun hEq hPost ids => do
  trace[Progress] "eq and post:\n{hEq} : {← inferType hEq}\n{hPost}"
  traceGoalWithNode "current goal"
  let r ← withTraceNode `Progress (fun _ => pure m!"simpAt target") do
    Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← progressSimpExt.getTheorems], hypsToUse := #[hEq.fvarId!]} (.targets #[] true)
  /- It may happen that at this point the goal is already solved (though this is rare)
      TODO: not sure this is the best way of checking it -/
  if r.isNone then trace[Progress] "The main goal was solved!"; return none
  traceGoalWithNode "goal after applying the eq and simplifying the binds"
  -- TODO: remove this? (some types get unfolded too much: we "fold" them back)
  withTraceNode `Progress (fun _ => pure m!"simpAt: folding back scalar types") do
    Simp.dsimpAt true {implicitDefEqProofs := true, failIfUnchanged := false} {addSimpThms := scalar_eqs} (.targets (fvarIds.map Expr.fvarId!) false)
  if (← getUnsolvedGoals).isEmpty then trace[Progress] "The main goal was solved!"; return none
  traceGoalWithNode "goal after folding back scalar types"
  -- Clear the equality, unless the user requests not to do so
  if args.keep.isSome then pure ()
  else do
    let mgoal ← getMainGoal
    let mgoal ← mgoal.tryClear hEq.fvarId!
    setGoals [mgoal]
  withMainContext do
  withTraceNode `Progress (fun _ => pure m!"Unsolved goals") do trace[Progress] "Unsolved goals: {← getUnsolvedGoals}"
  traceGoalWithNode "Goal after clearing the equality"
  -- Continue splitting following the post following the user's instructions
  match hPost with
  | none =>
    -- Sanity check
    if ¬ ids.isEmpty then
      logWarning m!"Too many ids provided ({ids}): there is no postcondition to split"
    trace[Progress] "No post to split"
    pure (some { goal := ← getMainGoal, posts := #[]})
  | some hPost => do
    trace[Progress] "Post to split: {hPost}"
    let rec splitPostWithIds (prevId : Name) (hPosts : List FVarId) (hPost : Expr) (ids0 : List (Option Name)) :
      TacticM (Array FVarId) := do
      match ids0 with
      | [] =>
        /- We used all the user provided ids.
            Split the remaining conjunctions by using fresh ids if the user
            instructed to fully split the post-condition, otherwise stop -/
        if args.splitPost then
          splitFullConjTac true hPost (λ asms => do
            pure (hPosts.reverse ++ (asms.map (fun x => x.fvarId!))).toArray)
        else pure (hPost.fvarId! :: hPosts).reverse.toArray
      | nid :: ids => do
        trace[Progress] "Splitting post: {← inferType hPost}"
        -- Split
        let nid ← do
          match nid with
          | none => mkFreshAnonPropUserName
          | some nid => pure nid
        trace[Progress] "\n- prevId: {prevId}\n- nid: {nid}\n- remaining ids: {ids}"
        if ← isConj (← inferType hPost) then
          splitConjTac hPost (some (prevId, nid)) (λ nhAsm nhPost => splitPostWithIds nid (nhAsm.fvarId! :: hPosts) nhPost ids)
        else
        logWarning m!"Too many ids provided ({ids0}) not enough conjuncts to split in the postcondition"
        pure (hPost.fvarId! :: hPosts).reverse.toArray
    let curPostId := (← hPost.fvarId!.getDecl).userName
    let posts ← splitPostWithIds curPostId [] hPost ids
    pure (some ⟨ ← getMainGoal, posts⟩)

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

  The main thing we do is simplify the post-conditions. -/
def postprocessMainGoal (mainGoal : Option MainGoal) : TacticM (Option MainGoal) := do
  withTraceNode `Progress (fun _ => pure m!"postprocessMainGoal") do
  match mainGoal with
  | none => pure none
  | some mainGoal =>
    setGoals [mainGoal.goal]
    -- Simplify the post-conditions
    let args : Simp.SimpArgs :=
      {simpThms := #[← progressPostSimpExt.getTheorems],
        simprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs]}
    let posts ← Simp.simpAt true { maxDischargeDepth := 0, failIfUnchanged := false }
          args (.targets mainGoal.posts false)
    match posts with
    | none =>
      -- We actually closed the goal: we shouldn't get there
      -- TODO: make this more robust
      trace[Progress] "Goal closed by simplifying the introduced post-conditions"
      pure none
    | some posts =>
      -- Simplify the goal again
      let r ← Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
        {simpThms := #[← progressSimpExt.getTheorems], declsToUnfold := #[``pure]} (.targets #[] true)
      if r.isSome then
        pure (some ({ goal := ← getMainGoal, posts} : MainGoal))
      else pure none

def progressWith (args : Args) (fExpr : Expr) (th : Expr) :
  TacticM Goals := do
  withTraceNode `Progress (fun _ => pure m!"progressWith") do
  -- Attempt to instantiate the theorem and introduce it in the context
  let (newGoals, thAsm) ← tryMatch args fExpr th
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
  -- Destruct the existential quantifiers and split the conjunctions
  setGoals [mainGoal]
  let mainGoal ← splitExistsEqAndPost args thAsm
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
def tryApply (args : Args) (fExpr : Expr) (kind : String) (th : Option Expr) :
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
          let res ← progressWith args fExpr th
          pure (some res)
        catch _ => pure none
  match res with
  | some res => pure (some res)
  | none => pure none

/-- Try to progress with an assumption.
    Return `some` if we succeed, `none` otherwise.
-/
def tryAssumptions (args : Args) (fExpr : Expr) :
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
      let goal ← progressWith args fExpr decl.toExpr
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
  let fExpr ← do
    let isGoal := true
    withTraceNode `Progress (fun _ => pure m!"Calling withProgressSpec to deconstruct the target") do
    withProgressSpec isGoal goalTy fun {fArgsExpr := fExpr, ..} => do
    trace[Progress] "Expression to match: {fExpr}"
    pure fExpr
  -- If the user provided a theorem/assumption: use it.
  -- Otherwise, lookup one.
  match withTh with
  | some th => do
    let goals ← progressWith args fExpr th
    return (goals, .givenExpr th)
  | none =>
    -- Try all the assumptions one by one and if it fails try to lookup a theorem.
    if let some res ← tryAssumptions args fExpr then return res
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
        match ← tryApply args fExpr "pspec theorem" pspecExpr with
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
          let goals ← progressWith args fExpr decl.toExpr
          return (goals, .localHyp decl)
        catch _ => continue
      -- Nothing worked: failed
      let msg := "Progress failed: could not find a local assumption or a theorem to apply"
      trace[Progress] msg
      throwError msg

syntax progressArgs := ("keep" binderIdent)? ("with" term)? ("as" " ⟨ " binderIdent,* " ⟩")? ("by" tacticSeq)?

def parseProgressArgs
: TSyntax ``Aeneas.Progress.progressArgs -> TacticM (Option Name × Option Expr × Array (Option Name) × Option Syntax.Tactic)
| args@`(progressArgs| $[keep $x]? $[with $pspec:term]? $[as ⟨ $ids,* ⟩]? $[by $byTac]? ) =>  withMainContext do
  trace[Progress] "Progress arguments: {args.raw}"
  let keep?: Option Name ← Option.sequence <| x.map fun
    | `(binderIdent| _) => mkFreshAnonPropUserName
    | `(binderIdent| $name:ident) => pure name.getId
    | _ => throwUnsupportedSyntax
  trace[Progress] "Keep: {keep?}"
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
  return (keep?, withTh?, ids, byTac)
| _ => throwUnsupportedSyntax

def evalProgressCore (async : Bool) (keep keepPretty : Option Name) (withArg: Option Expr) (ids: Array (Option Name))
  (byTacStx : Option Syntax.Tactic)
  : TacticM Stats := do
  withTraceNode `Progress (fun _ => pure m!"evalProgress") do
  /- Simplify the goal -- TODO: this might close it: we need to check that and abort if necessary,
     and properly track that in the `Stats` -/
  let _ ← Simp.simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← progressSimpExt.getTheorems]} (.targets #[] true)
  withMainContext do
  let splitPost := true
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
    async, keep, keepPretty, ids, splitPost, assumTac := customAssumTac, solvePreconditionTac, byTacSyntax := byTacStx
  }
  let (goals, usedTheorem) ← progressAsmsOrLookupTheorem args withArg
  trace[Progress] "Progress done"
  return ⟨ goals, usedTheorem ⟩

def asyncOption : Bool := false

def evalProgress
  (async : Bool)
  (keep keepPretty : Option Name) (withArg: Option Expr) (ids: Array (Option Name))
  (byTac : Option Syntax.Tactic)
  : TacticM UsedTheorem := do
  let ⟨goals, usedTheorem⟩ ← evalProgressCore async keep keepPretty withArg ids byTac
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

elab (name := progress) "progress" args:progressArgs : tactic => do
  let (keep?, withArg, ids, byTac) ← parseProgressArgs args
  evalProgress asyncOption keep? none withArg ids byTac *> return ()

elab tk:"progress?" args:progressArgs : tactic => do
  let (keep?, withArg, ids, byTac) ← parseProgressArgs args
  let stats ← evalProgress asyncOption keep? none withArg ids byTac
  let mut stxArgs := args.raw
  if stxArgs[1].isNone then
    let withArg := mkNullNode #[mkAtom "with", ← stats.toSyntax]
    stxArgs := stxArgs.setArg 1 withArg
  let tac := mkNode `Aeneas.Progress.progress #[mkAtom "progress", stxArgs]
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)

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
  let stats ← evalProgress asyncOption none (some (.str .anonymous "_")) withArg ids byTac
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
    ∃ z, x + y = ok z := by
    progress keep _ as ⟨ z, h1 ⟩

  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z := by
    let* ⟨ z, h1 ⟩ ← *

  /--
  info: Try this: let* ⟨ z, h1 ⟩ ← UScalar.add_spec
  -/
  #guard_msgs in
  example {ty} {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z := by
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
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
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
    ∃ z, (do
      let z1 ← x + y
      z1 + x) = ok z ∧ z.val = 2 * x.val + y.val := by
    let* ⟨ z1, h1 ⟩ ← UScalar.add_spec
    let* ⟨ z2, h2 ⟩ ← UScalar.add_spec
    extract_goal0
    scalar_tac

  example {ty} {x y : UScalar ty} (h : 2 * x.val + y.val ≤ UScalar.max ty) :
    ∃ z, (do
      let z1 ← x + y
      z1 + x) = ok z ∧ z.val = 2 * x.val + y.val := by
    progress with UScalar.add_spec as ⟨ z1, h1 ⟩
    progress with UScalar.add_spec as ⟨ z2, h2 ⟩
    scalar_tac

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 ⟩
    simp [*]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 ⟩
    simp [*]

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with UScalar.add_spec as ⟨ z, h1 ⟩
    simp [*]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with IScalar.add_spec as ⟨ z, h1 ⟩
    simp [*]

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep h with UScalar.add_spec as ⟨ z ⟩
    simp [*]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep h with IScalar.add_spec as ⟨ z ⟩
    simp [*]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    -- This spec theorem is suboptimal, but it is good to check that it works
    progress with UScalar.add_spec as ⟨ z, h1 ⟩
    simp [*]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress with U32.add_spec as ⟨ z, h1 ⟩
    simp [*]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 ⟩
    simp [*]

  /- Checking that universe instantiation works: the original spec uses
     `α : Type u` where u is quantified, while here we use `α : Type 0` -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv, v.update i x = ok nv ∧
    nv.val = v.val.set i.val x := by
    progress
    simp [*]

  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv, v.update i x = ok nv ∧
    nv.val = v.val.set i.val x := by
    progress? says progress with Vec.update_spec
    simp [*]

  /- Checking that progress can handle nested blocks -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv,
      (do
         (do
            let _ ← v.update i x
            .ok ())
         .ok ()) = ok nv
      := by
    progress
    simp [*]

  /- Checking the case where simplifying the goal after instantiating the
     pspec theorem the goal actually solves it, and where the function is
     not a constant. We also test the case where the function under scrutinee
     is not a constant. -/
  example {x : U32}
    (f : U32 → Std.Result Unit) (h : ∀ x, f x = .ok ()) :
    f x = ok () := by
    progress

  example {x : U32}
    (f : U32 → Std.Result Unit) (h : ∀ x, f x = .ok ()) :
    f x = ok () := by
    progress? says progress with h

  /- The use of `right` introduces a meta-variable in the goal, that we
     need to instantiate (otherwise `progress` gets stuck) -/
  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    False ∨ (∃ z, x + y = ok z ∧ z.val = x.val + y.val) := by
    right
    progress keep _ as ⟨ z, h1 ⟩
    simp [*]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    False ∨ (∃ z, x + y = ok z ∧ z.val = x.val + y.val) := by
    right
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with IScalar.add_spec as ⟨ z, h1 ⟩
    simp [*]

  /--
error: unsolved goals
case a
x y : U32
f : U32 → U32 → Result U32
hf : ∀ (x y : U32), ↑x < 10 → ↑y < 10 → ∃ z, f x y = ok z
⊢ ↑x < 10

case a
x y : U32
f : U32 → U32 → Result U32
hf : ∀ (x y : U32), ↑x < 10 → ↑y < 10 → ∃ z, f x y = ok z
⊢ ↑y < 10
  -/
  #guard_msgs in
  example {x y} (f : U32 → U32 → Result U32) (hf : ∀ x y, x.val < 10 → y.val < 10 → ∃ z, f x y = ok z) : ∃ z, f x y = ok z := by
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
        ∃ i, t.size = ok i ∧ i ≥ 0 := by
        cases t
        simp [Tree.size]
        progress
        omega

      @[local progress]
      theorem Trees.size_spec (t : Trees) :
        ∃ i, t.size = ok i ∧ i ≥ 0 := by
        cases t <;> simp [Trees.size]
        progress
        progress? says progress with Trees.size_spec
        omega
    end
  end

  -- Testing progress on theorems containing local let-bindings
  def add (x y : U32) : Std.Result U32 := x + y

  section
    /- Testing progress on theorems containing local let-bindings as well as
       the `local` attribute kind -/
    @[local progress] theorem add_spec' (x y : U32) (h : x.val + y.val ≤ U32.max) :
      let tot := x.val + y.val
      ∃ z, x + y = ok z ∧ z.val = tot := by
      simp
      progress with U32.add_spec
      scalar_tac

    def add1 (x y : U32) : Std.Result U32 := do
      let z ← x + y
      z + z

    example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
      ∃ z, add1 x y = ok z := by
      rw [add1]
      progress? as ⟨ z1, h ⟩ says progress with add_spec' as ⟨ z1, h ⟩
      progress? as ⟨ z2, h ⟩ says progress with add_spec' as ⟨ z2, h ⟩
  end

  /- Checking that `add_spec'` went out of scope -/
  example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
    ∃ z, add1 x y = ok z := by
    rw [add1]
    progress? as ⟨ z1, h ⟩ says progress with U32.add_spec as ⟨ z1, h ⟩
    progress? as ⟨ z2, h ⟩ says progress with U32.add_spec as ⟨ z2, h ⟩

  variable (P : ℕ → List α → Prop)
  variable (f : List α → Std.Result Bool)
  variable (f_spec : ∀ l i, P i l → ∃ b, f l = ok b)

  example (l : List α) (h : P i l) :
    ∃ b, f l = ok b := by
    progress? as ⟨ b ⟩ says progress with f_spec as ⟨ b ⟩

  /- Progress using a term -/
  example {x: U32}
    (f : U32 → Std.Result Unit)
    (h : ∀ x, f x = .ok ()):
      f x = ok () := by
      progress? with (show ∀ x, f x = .ok () by exact h) says progress with(show ∀ x, f x = .ok () by exact h)

  /- Progress using a term -/
  example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
    ∃ z, add1 x y = ok z := by
    rw [add1]
    have h1 := add_spec'
    progress with h1 as ⟨ z1, h ⟩
    progress with add_spec' z1 as ⟨ z2, h ⟩

  /- Pretty equality when the output type is unit -/
  /--
  info: example
  (y : U32)
  (h1 : ↑y < 100) :
  massert (y < 100#u32) = ok ()
  := by sorry
  -/
  #guard_msgs in
  example (x y : U32) (h0 : x.val < 100) (h1 : y.val < 100) :
    (do
      massert (x < 100#u32)
      massert (y < 100#u32))
    = ok ()
    := by
    let* ⟨⟩ ← massert_spec
    extract_goal0
    let* ⟨⟩ ← massert_spec

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
    ∃ c',
    (do
          let c1 ← c >>> 16#i32
          ok c1) =
        ok c' ∧ c'.bv = c.bv >>> 16
    := by
    progress as ⟨ c', _, hc' ⟩ -- we have: `hc' : c'.bv = c.bv >>> 16`
    extract_goal1
    fsimp [hc']


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
      ∃ peSrc', nttLayer peSrc k len = ok peSrc' ∧
      toPoly peSrc' = Spec.nttLayer (toPoly peSrc) k.val len.val 0 hLenPos ∧
      wfArray peSrc' := by
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
      ∃ peSrc1, ntt peSrc = ok peSrc1 ∧
      wfArray peSrc1
      := by
      unfold ntt
      progress; fsimp [Nat.log2]
      progress
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      progress; fsimp [Nat.log2]
      assumption

    set_option maxHeartbeats 800000
    theorem ntt_spec' (peSrc : Std.Array U16 256#usize)
      (hWf : wfArray peSrc) :
      ∃ peSrc1, ntt peSrc = ok peSrc1 ∧
      wfArray peSrc1
      := by
      unfold ntt
      progress by fsimp [Nat.log2]
      progress
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      progress by fsimp [Nat.log2]
      assumption

  end Ntt

end Test

end Progress

end Aeneas
