import Lean
import Base.Arith
import Base.Progress.Base
import Base.Primitives -- TODO: remove?

namespace Progress

open Lean Elab Term Meta Tactic
open Utils

-- TODO: the scalar types annoyingly often get reduced when we use the progress
-- tactic. We should find a way of controling reduction. For now we use rewriting
-- lemmas to make sure the goal remains clean, but this complexifies proof terms.
-- It seems there used to be a `fold` tactic.
theorem scalar_isize_eq : Primitives.Scalar .Isize = Primitives.Isize := by rfl
theorem scalar_i8_eq    : Primitives.Scalar .I8 = Primitives.I8 := by rfl
theorem scalar_i16_eq   : Primitives.Scalar .I16 = Primitives.I16 := by rfl
theorem scalar_i32_eq   : Primitives.Scalar .I32 = Primitives.I32 := by rfl
theorem scalar_i64_eq   : Primitives.Scalar .I64 = Primitives.I64 := by rfl
theorem scalar_i128_eq  : Primitives.Scalar .I128 = Primitives.I128 := by rfl
theorem scalar_usize_eq : Primitives.Scalar .Usize = Primitives.Usize := by rfl
theorem scalar_u8_eq    : Primitives.Scalar .U8 = Primitives.U8 := by rfl
theorem scalar_u16_eq   : Primitives.Scalar .U16 = Primitives.U16 := by rfl
theorem scalar_u32_eq   : Primitives.Scalar .U32 = Primitives.U32 := by rfl
theorem scalar_u64_eq   : Primitives.Scalar .U64 = Primitives.U64 := by rfl
theorem scalar_u128_eq  : Primitives.Scalar .U128 = Primitives.U128 := by rfl
def scalar_eqs := [
  ``scalar_isize_eq, ``scalar_i8_eq, ``scalar_i16_eq, ``scalar_i32_eq, ``scalar_i64_eq, ``scalar_i128_eq,
  ``scalar_usize_eq, ``scalar_u8_eq, ``scalar_u16_eq, ``scalar_u32_eq, ``scalar_u64_eq, ``scalar_u128_eq
]

inductive TheoremOrLocal where
| Theorem (thName : Name)
| Local (asm : LocalDecl)

structure Stats where
  usedTheorem : Syntax

instance : ToMessageData TheoremOrLocal where
  toMessageData := λ x => match x with | .Theorem thName => m!"{thName}" | .Local asm => m!"{asm.userName}"

instance : Coe TheoremOrLocal Name where
  coe := λ x => match x with | .Theorem thName => thName | .Local asm => asm.userName

/- Type to propagate the errors of `progressWith`.
   We need this because we use the exceptions to backtrack, when trying to
   use the assumptions for instance. When there is actually an error we want
   to propagate to the user, we return it. -/
inductive ProgressError
| Ok
| Error (msg : MessageData)
deriving Inhabited

def progressWith (fExpr : Expr) (thExpr : Expr)
  (keep : Option Name) (ids : Array (Option Name)) (splitPost : Bool)
  (asmTac : TacticM Unit) : TacticM ProgressError := do
  /- Apply the theorem
     We try to match the theorem with the goal
     In order to do so, we introduce meta-variables for all the parameters
     (i.e., quantified variables and assumpions), and unify those with the goal.
     Remark: we do not introduce meta-variables for the quantified variables
     which don't appear in the function arguments (we want to let them
     quantified).
     We also make sure that all the meta variables which appear in the
     function arguments have been instantiated
   -/
  let thTy ← inferType thExpr
  trace[Progress] "Looked up theorem/assumption type: {thTy}"
  -- TODO: the tactic fails if we uncomment withNewMCtxDepth
  -- withNewMCtxDepth do
  let (mvars, binders, thExBody) ← forallMetaTelescope thTy
  trace[Progress] "After stripping foralls: {thExBody}"
  -- Introduce the existentially quantified variables and the post-condition
  -- in the context
  let thBody ←
    existsTelescope thExBody.consumeMData fun _evars thBody => do
    trace[Progress] "After stripping existentials: {thBody}"
    let (thBody, _) ← optSplitConj thBody
    trace[Progress] "After splitting the conjunction: {thBody}"
    let (thBody, _) ← destEq thBody
    trace[Progress] "After splitting equality: {thBody}"
    -- There shouldn't be any existential variables in thBody
    pure thBody.consumeMData
  -- Match the body with the target
  trace[Progress] "Matching:\n- body:\n{thBody}\n- target:\n{fExpr}"
  let ok ← isDefEq thBody fExpr
  if ¬ ok then throwError "Could not unify the theorem with the target:\n- theorem: {thBody}\n- target: {fExpr}"
  let mgoal ← Tactic.getMainGoal
  postprocessAppMVars `progress mgoal mvars binders true true
  Term.synthesizeSyntheticMVarsNoPostponing
  let thBody ← instantiateMVars thBody
  trace[Progress] "thBody (after instantiation): {thBody}"
  -- Add the instantiated theorem to the assumptions (we apply it on the metavariables).
  let th ← mkAppOptM' thExpr (mvars.map some)
  trace[Progress] "Instantiated theorem reusing the metavariables: {th}"
  let asmName ← do match keep with | none => mkFreshAnonPropUserName | some n => do pure n
  let thAsm ← Utils.addDeclTac asmName th (← inferType th) (asLet := false)
  withMainContext do -- The context changed - TODO: remove once addDeclTac is updated
  let ngoal ← getMainGoal
  trace[Progress] "current goal: {ngoal}"
  trace[Progress] "current goal is assigned: {← ngoal.isAssigned}"
  -- The assumption should be of the shape:
  -- `∃ x1 ... xn, f args = ... ∧ ...`
  -- We introduce the existentially quantified variables and split the top-most
  -- conjunction if there is one. We use the provided `ids` list to name the
  -- introduced variables.
  let res ← splitAllExistsTac thAsm ids.toList fun h ids => do
    -- Split the conjunctions.
    -- For the conjunctions, we split according once to separate the equality `f ... = .ret ...`
    -- from the postcondition, if there is, then continue to split the postcondition if there
    -- are remaining ids.
    let splitEqAndPost (k : Expr → Option Expr → List (Option Name) → TacticM ProgressError) : TacticM ProgressError := do
      if ← isConj (← inferType h) then do
        let hName := (← h.fvarId!.getDecl).userName
        let (optIds, ids) ← do
          match ids with
          | [] => do pure (some (hName, ← mkFreshAnonPropUserName), [])
          | none :: ids => do pure (some (hName, ← mkFreshAnonPropUserName), ids)
          | some id :: ids => do pure (some (hName, id), ids)
        splitConjTac h optIds (fun hEq hPost => k hEq (some hPost) ids)
      else k h none ids
    -- Simplify the target by using the equality and some monad simplifications,
    -- then continue splitting the post-condition
    splitEqAndPost fun hEq hPost ids => do
    trace[Progress] "eq and post:\n{hEq} : {← inferType hEq}\n{hPost}"
    trace[Progress] "current goal: {← getMainGoal}"
    Tactic.focus do
    let _ ←
      tryTac
        (simpAt true {} [] []
               [``Primitives.bind_tc_ok, ``Primitives.bind_tc_fail, ``Primitives.bind_tc_div]
               [hEq.fvarId!] (.targets #[] true))
    -- It may happen that at this point the goal is already solved (though this is rare)
    -- TODO: not sure this is the best way of checking it
    if (← getUnsolvedGoals) == [] then pure .Ok
    else
       trace[Progress] "goal after applying the eq and simplifying the binds: {← getMainGoal}"
       -- TODO: remove this (some types get unfolded too much: we "fold" them back)
       let _ ← tryTac (simpAt true {} [] [] scalar_eqs [] .wildcard_dep)
       trace[Progress] "goal after folding back scalar types: {← getMainGoal}"
       -- Clear the equality, unless the user requests not to do so
       let mgoal ← do
         if keep.isSome then getMainGoal
         else do
           let mgoal ← getMainGoal
           mgoal.tryClearMany #[hEq.fvarId!]
       setGoals (mgoal :: (← getUnsolvedGoals))
       trace[Progress] "Goal after splitting eq and post and simplifying the target: {mgoal}"
       -- Continue splitting following the post following the user's instructions
       match hPost with
       | none =>
         -- Sanity check
         if ¬ ids.isEmpty then
           return (.Error m!"Too many ids provided ({ids}): there is no postcondition to split")
         else return .Ok
       | some hPost => do
         let rec splitPostWithIds (prevId : Name) (hPost : Expr) (ids0 : List (Option Name)) : TacticM ProgressError := do
           match ids0 with
           | [] =>
             /- We used all the user provided ids.
                Split the remaining conjunctions by using fresh ids if the user
                instructed to fully split the post-condition, otherwise stop -/
             if splitPost then
               splitFullConjTac true hPost (λ _ => pure .Ok)
             else pure .Ok
           | nid :: ids => do
             trace[Progress] "Splitting post: {← inferType hPost}"
             -- Split
             let nid ← do
               match nid with
               | none => mkFreshAnonPropUserName
               | some nid => pure nid
             trace[Progress] "\n- prevId: {prevId}\n- nid: {nid}\n- remaining ids: {ids}"
             if ← isConj (← inferType hPost) then
               splitConjTac hPost (some (prevId, nid)) (λ _ nhPost => splitPostWithIds nid nhPost ids)
             else return (.Error m!"Too many ids provided ({ids0}) not enough conjuncts to split in the postcondition")
         let curPostId := (← hPost.fvarId!.getDecl).userName
         splitPostWithIds curPostId hPost ids
  match res with
  | .Error _ => return res -- Can we get there? We're using "return"
  | .Ok =>
    -- Update the set of goals
    let curGoals ← getUnsolvedGoals
    let newGoals := mvars.map Expr.mvarId!
    let newGoals ← newGoals.filterM fun mvar => not <$> mvar.isAssigned
    trace[Progress] "new goals: {newGoals}"
    setGoals newGoals.toList
    allGoals asmTac
    let newGoals ← getUnsolvedGoals
    setGoals (newGoals ++ curGoals)
    trace[Progress] "progress: replaced the goals"
    --
    pure .Ok

-- Small utility: if `args` is not empty, return the name of the app in the first
-- arg, if it is a const.
def getFirstArgAppName (args : Array Expr) : MetaM (Option Name) := do
  if args.size = 0 then pure none
  else
    (args.get! 0).withApp fun f _ => do
    if f.isConst then pure (some f.constName)
    else pure none

def getFirstArg (args : Array Expr) : Option Expr := do
  if args.size = 0 then none
  else some (args.get! 0)

/- Helper: try to lookup a theorem and apply it.
   Return true if it succeeded. -/
def tryLookupApply (keep : Option Name) (ids : Array (Option Name)) (splitPost : Bool)
  (asmTac : TacticM Unit) (fExpr : Expr)
  (kind : String) (th : Option Expr) : TacticM Bool := do
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
          let res ← progressWith fExpr th keep ids splitPost asmTac
          pure (some res)
        catch _ => none
  match res with
  | some .Ok => pure true
  | some (.Error msg) => throwError msg
  | none => pure false

-- The array of ids are identifiers to use when introducing fresh variables
def progressAsmsOrLookupTheorem (keep : Option Name) (withTh : Option Expr)
  (ids : Array (Option Name)) (splitPost : Bool) (asmTac : TacticM Unit) : TacticM Syntax := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  -- There might be uninstantiated meta-variables in the goal that we need
  -- to instantiate (otherwise we will get stuck).
  let goalTy ← instantiateMVars goalTy
  trace[Progress] "goal: {goalTy}"
  -- Dive into the goal to lookup the theorem
  -- Remark: if we don't isolate the call to `withPSpec` to immediately "close"
  -- the terms immediately, we may end up with the error:
  -- "(kernel) declaration has free variables"
  -- I'm not sure I understand why.
  -- TODO: we should also check that no quantified variable appears in fExpr.
  -- If such variables appear, we should just fail because the goal doesn't
  -- have the proper shape.
  let fExpr ← do
    let isGoal := true
    withPSpec isGoal goalTy fun desc => do
    let fExpr := desc.fArgsExpr
    trace[Progress] "Expression to match: {fExpr}"
    pure fExpr
  -- If the user provided a theorem/assumption: use it.
  -- Otherwise, lookup one.
  match withTh with
  | some th => do
    match ← progressWith fExpr th keep ids splitPost asmTac with
    | .Ok => return (← exprToSyntax th)
    | .Error msg => throwError msg
  | none =>
    -- Try all the assumptions one by one and if it fails try to lookup a theorem.
    let ctx ← Lean.MonadLCtx.getLCtx
    let decls ← ctx.getDecls
    for decl in decls.reverse do
      trace[Progress] "Trying assumption: {decl.userName} : {decl.type}"
      let res ← do try progressWith fExpr decl.toExpr keep ids splitPost asmTac catch _ => continue
      match res with
      | .Ok => return (mkIdent decl.userName)
      | .Error msg => throwError msg
    -- It failed: lookup the pspec theorems which match the expression *only
    -- if the function is a constant*
    let fIsConst ← do
      fExpr.consumeMData.withApp fun mf _ => do
      pure mf.isConst
    if ¬ fIsConst then throwError "Progress failed"
    else do
      trace[Progress] "No assumption succeeded: trying to lookup a pspec theorem"
      let pspecs : Array Name ← do
        let thNames ← pspecAttr.find? fExpr
        -- TODO: because of reduction, there may be several valid theorems (for
        -- instance for the scalars). We need to sort them from most specific to
        -- least specific. For now, we assume the most specific theorems are at
        -- the end.
        let thNames := thNames.reverse
        trace[Progress] "Looked up pspec theorems: {thNames}"
        pure thNames
      -- Try the theorems one by one
      for pspec in pspecs do
        -- TODO: convert pspec into an Expr.
        let pspecExpr ← Term.mkConst pspec
        if ← tryLookupApply keep ids splitPost asmTac fExpr "pspec theorem" pspecExpr then return (mkIdent pspec)
        else pure ()
      -- It failed: try to use the recursive assumptions
      trace[Progress] "Failed using a pspec theorem: trying to use a recursive assumption"
      -- We try to apply the assumptions of kind "auxDecl"
      let ctx ← Lean.MonadLCtx.getLCtx
      let decls ← ctx.getAllDecls
      let decls := decls.filter (λ decl => match decl.kind with
        | .default | .implDetail => false | .auxDecl => true)
      for decl in decls.reverse do
        trace[Progress] "Trying recursive assumption: {decl.userName} : {decl.type}"
        let res ← do try progressWith fExpr decl.toExpr keep ids splitPost asmTac catch _ => continue
        match res with
        | .Ok => return (mkIdent decl.userName)
        | .Error msg => throwError msg
      -- Nothing worked: failed
      throwError "Progress failed"

syntax progressArgs := ("keep" (ident <|> "_"))? ("with" term)? ("as" " ⟨ " (ident <|> "_"),* " .."? " ⟩")?

def evalProgress (args : TSyntax `Progress.progressArgs) : TacticM Stats := do
  let args := args.raw
  -- Process the arguments to retrieve the identifiers to use
  trace[Progress] "Progress arguments: {args}"
  let (keepArg, withArg, asArgs) ←
    match args.getArgs.toList with
    | [keepArg, withArg, asArgs] => do pure (keepArg, withArg, asArgs)
    | _ => throwError "Unexpected: invalid arguments"
  let keep : Option Name ← do
    trace[Progress] "Keep arg: {keepArg}"
    let args := keepArg.getArgs
    if args.size > 0 then do
      trace[Progress] "Keep args: {args}"
      let arg := args.get! 1
      trace[Progress] "Keep arg: {arg}"
      if arg.isIdent then pure (some arg.getId)
      else do pure (some (← mkFreshAnonPropUserName))
    else do pure none
  trace[Progress] "Keep: {keep}"
  let withArg ← do
    let withArg := withArg.getArgs
    if withArg.size > 0 then
      let id := withArg.get! 1
      trace[Progress] "With arg: {id}"

      -- Either, it's a local declaration or a theorem, either it's a term
      -- for which we need to find a declaration

      if id.isIdent then
        -- Attempt to lookup a local declaration
        match (← getLCtx).findFromUserName? id.getId with
        | some decl => do
          trace[Progress] "With arg: local decl"
          pure (some decl.toExpr)
        | none => do
          -- Not a local declaration: should be a theorem
          trace[Progress] "With arg: theorem"
          addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
          let some e ← Term.resolveId? id | throwError m!"Could not find theorem: {id}"
          pure (some e)
      else
        trace[Progress] "With arg: not an identifier (a term?)"
        let e ← Tactic.elabTerm id none
        trace[Progress] m!"With arg: elaborated expression {e}"
        pure (some e)
    else pure none
  let ids :=
    let args := asArgs.getArgs
    if args.size > 2 then
      let args := (args.get! 2).getSepArgs
      args.map (λ s => if s.isIdent then some s.getId else none)
    else #[]
  trace[Progress] "User-provided ids: {ids}"
  let splitPost : Bool :=
    let args := asArgs.getArgs
    args.size > 3 ∧ (args.get! 3).getArgs.size > 0
  trace[Progress] "Split post: {splitPost}"
  /- For scalarTac we have a fast track: if the goal is not a linear
     arithmetic goal, we skip (note that otherwise, scalarTac would try
     to prove a contradiction) -/
  let scalarTac : TacticM Unit := do
    if ← Arith.goalIsLinearInt then
      -- Also: we don't try to split the goal if it is a conjunction
      -- (it shouldn't be)
      Arith.scalarTac false
    else
      throwError "Not a linear arithmetic goal"
  let usedTheorem ← progressAsmsOrLookupTheorem keep withArg ids splitPost (
    withMainContext do
    trace[Progress] "trying to solve assumption: {← getMainGoal}"
    firstTac [assumptionTac, scalarTac])
  trace[Progress] "Progress done"
  return {
    usedTheorem
  }

elab (name := progress) "progress" args:progressArgs : tactic =>
  evalProgress args *> return ()

elab tk:"progress?" args:progressArgs : tactic => do
  let stats ← evalProgress args
  let mut stxArgs := args.raw
  if stxArgs[1].isNone then
    let withArg := mkNullNode #[mkAtom "with", stats.usedTheorem]
    stxArgs := stxArgs.setArg 1 withArg
  let tac := mkNode `Progress.progress #[mkAtom "progress", stxArgs]
  -- if stats.usedTheorem.isInaccesisble then
  --  logInfo "{...} is inaccessible, if you want to actually use the suggestion, please use `rename_i ...`"

  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)

namespace Test
  open Primitives Result

  -- Show the traces
  -- set_option trace.Progress true
  -- set_option pp.rawOnError true

  set_option says.verify true

  -- The following commands display the databases of theorems
  -- #eval showStoredPSpec
  open alloc.vec

  example {ty} {x y : Scalar ty}
    (hmin : Scalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ Scalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 .. ⟩
    simp [*, h1]

  example {ty} {x y : Scalar ty}
    (hmin : Scalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ Scalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress? keep _ as ⟨ z, h1 .. ⟩ says progress keep _ with Primitives.Scalar.add_spec as ⟨ z, h1 .. ⟩
    simp [*, h1]

  example {ty} {x y : Scalar ty}
    (hmin : Scalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ Scalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep h with Scalar.add_spec as ⟨ z ⟩
    simp [*, h]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    -- This spec theorem is suboptimal, but it is good to check that it works
    progress with Scalar.add_spec as ⟨ z, h1 .. ⟩
    simp [*, h1]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress with U32.add_spec as ⟨ z, h1 .. ⟩
    simp [*, h1]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 .. ⟩
    simp [*, h1]

  /- Checking that universe instantiation works: the original spec uses
     `α : Type u` where u is quantified, while here we use `α : Type 0` -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv, v.update_usize i x = ok nv ∧
    nv.val = v.val.update i.val x := by
    progress
    simp [*]


  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv, v.update_usize i x = ok nv ∧
    nv.val = v.val.update i.val x := by
    progress? says progress with Primitives.alloc.vec.Vec.update_usize_spec
    simp [*]

  /- Checking that progress can handle nested blocks -/
  example {α : Type} (v: Vec α) (i: Usize) (x : α)
    (hbounds : i.val < v.length) :
    ∃ nv,
      (do
         (do
            let _ ← v.update_usize i x
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
    (f : U32 → Result Unit) (h : ∀ x, f x = .ok ()) :
    f x = ok () := by
    progress


  example {x : U32}
    (f : U32 → Result Unit) (h : ∀ x, f x = .ok ()) :
    f x = ok () := by
    progress? says progress with h

  /- The use of `right` introduces a meta-variable in the goal, that we
     need to instantiate (otherwise `progress` gets stuck) -/
  example {ty} {x y : Scalar ty}
    (hmin : Scalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ Scalar.max ty) :
    False ∨ (∃ z, x + y = ok z ∧ z.val = x.val + y.val) := by
    right
    progress keep _ as ⟨ z, h1 .. ⟩
    simp [*, h1]

  /- Progress using a term -/
  example {x: U32}
    (f : U32 → Result Unit)
    (h : ∀ x, f x = .ok ()):
      f x = ok () := by
      progress with (show ∀ x, f x = .ok () by exact h)

end Test

end Progress
