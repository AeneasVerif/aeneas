import Lean
import Aeneas.ScalarTac
import Aeneas.Progress.Init
import Aeneas.Std
import Aeneas.FSimp

namespace Aeneas

namespace Progress

open Lean Elab Term Meta Tactic
open Utils

/-- A special definition that we use to introduce pretty-printed terms in the context -/
def prettyMonadEq {α : Type u} (x : Std.Result α) (y : α) : Prop := x = .ok y

macro:max "[> " "let" y:term " ← " x:term " <]"   : term => `(prettyMonadEq $x $y)

@[app_unexpander prettyMonadEq]
def unexpPrettyMonadEqofNat : Lean.PrettyPrinter.Unexpander | `($_ $x $y) => `([> let $y ← $x <]) | _ => throw ()

example (x y z : Std.U32) (_ : [> let z ← (x + y) <]) : True := by simp

theorem eq_imp_prettyMonadEq {α : Type u} {x : Std.Result α} {y : α} (h : x = .ok y) : prettyMonadEq x y := by simp [prettyMonadEq, h]


-- TODO: the scalar types annoyingly often get reduced when we use the progress
-- tactic. We should find a way of controling reduction. For now we use rewriting
-- lemmas to make sure the goal remains clean, but this complexifies proof terms.
-- It seems there used to be a `fold` tactic. Update: there is a `refold_let` in Mathlib
theorem uscalar_u8_eq    : Std.UScalar .U8 = Std.U8 := by rfl
theorem uscalar_u16_eq   : Std.UScalar .U16 = Std.U16 := by rfl
theorem uscalar_u32_eq   : Std.UScalar .U32 = Std.U32 := by rfl
theorem uscalar_u64_eq   : Std.UScalar .U64 = Std.U64 := by rfl
theorem uscalar_u128_eq  : Std.UScalar .U128 = Std.U128 := by rfl
theorem uscalar_usize_eq : Std.UScalar .Usize = Std.Usize := by rfl

theorem iscalar_i8_eq    : Std.IScalar .I8 = Std.I8 := by rfl
theorem iscalar_i16_eq   : Std.IScalar .I16 = Std.I16 := by rfl
theorem iscalar_i32_eq   : Std.IScalar .I32 = Std.I32 := by rfl
theorem iscalar_i64_eq   : Std.IScalar .I64 = Std.I64 := by rfl
theorem iscalar_i128_eq  : Std.IScalar .I128 = Std.I128 := by rfl
theorem iscalar_isize_eq : Std.IScalar .Isize = Std.Isize := by rfl
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
| progressThm name => pure <| mkIdent name

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
/- Type to propagate the errors of `progressWith`.
   We need this because we use the exceptions to backtrack, when trying to
   use the assumptions for instance. When there is actually an error we want
   to propagate to the user, we return it. -/
inductive Result (T U : Type) where
| Ok : T → Result T U
| Error : U → Result T U
deriving Inhabited

structure ProgressGoals where
  /-- The preconditions that are left to prove -/
  preconditions : Array MVarId
  /-- the main goal, if it was not proven -/
  mainGoal : Option MVarId
deriving Inhabited

structure Stats extends ProgressGoals where
  usedTheorem : UsedTheorem

structure ProgressWithOutput extends ProgressGoals where
  /- The post-conditions introduced in the context -/
  posts : Array FVarId
deriving Inhabited

attribute [progress_post_simps]
  Std.IScalar.toNat Std.UScalar.ofNat_val_eq Std.IScalar.ofInt_val_eq

open Result in
def progressWith (fExpr : Expr) (th : Expr)
  (keep keepPretty : Option Name) (ids : Array (Option Name)) (splitPost : Bool)
  (asmTac : TacticM Unit) : TacticM (Result ProgressWithOutput MessageData) := do
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
  /- There might be meta-variables in the type if the theorem comes from a local declaration,
     especially if this declaration was introduced by a tactic -/
  let thTy ← instantiateMVars (← inferType th)
  trace[Progress] "Looked up theorem/assumption type: {thTy}"
  -- Normalize to inline the let-bindings
  let thTy ← normalizeLetBindings thTy
  trace[Progress] "After normalizing the let-bindings: {thTy}"
  programTelescope thTy fun xs _zs thBody _ _ => do
  let (mvars, binders) := xs.unzip
  let mvars := mvars.map .mvar
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
  let th := mkAppN th mvars
  trace[Progress] "Instantiated theorem reusing the metavariables: {th}"
  let asmName ← do match keep with | none => mkFreshAnonPropUserName | some n => do pure n
  let thTy ← inferType th
  trace[Progress] "thTy (after application): {thTy}"
  /- Normalize the let-bindings (note that we already inlined the let bindings once above when analizing
     the theorem, now we do it again on the instantiated theorem - there is probably a smarter way to do,
     but it doesn't really matter). -/
  -- TODO: actually we might want to let the user insert them in the context
  let thTy ← normalizeLetBindings thTy
  trace[Progress] "thTy (after normalizing let-bindings): {thTy}"
  let thAsm ← Utils.addDeclTac asmName th thTy (asLet := false)
  withMainContext do -- The context changed - TODO: remove once addDeclTac is updated
  let ngoal ← getMainGoal
  trace[Progress] "current goal: {ngoal}"
  trace[Progress] "current goal is assigned: {← ngoal.isAssigned}"
  /- The assumption should be of the shape:
     `∃ x1 ... xn, f args = ... ∧ ...`
     We introduce the existentially quantified variables and split the top-most
     conjunction if there is one. We use the provided `ids` list to name the
     introduced variables. -/
  let res : Result (Array FVarId) MessageData ← splitAllExistsTac thAsm ids.toList fun h ids => do
    /- Introduce the pretty equality if the user requests it.
       We take care of introducing it *before* splitting the post-conditions, so that those appear
       after it.
     -/
    match keepPretty with
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
        let _ ← Utils.addDeclTac name e (← inferType e) (asLet := false)
        trace[Progress] "Introduced the \"pretty\" let binding: {← getMainGoal}"

    /- Split the conjunctions.
       For the conjunctions, we split according once to separate the equality `f ... = .ret ...`
       from the postcondition, if there is, then continue to split the postcondition if there
       are remaining ids. -/
    let splitEqAndPost (k : Expr → Option Expr → List (Option Name) → TacticM (Result (Array FVarId) MessageData)) :
      TacticM (Result (Array FVarId) MessageData) := do
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
    splitEqAndPost fun hEq hPost ids => do
    trace[Progress] "eq and post:\n{hEq} : {← inferType hEq}\n{hPost}"
    trace[Progress] "current goal: {← getMainGoal}"
    simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← progressSimpExt.getTheorems], hypsToUse := #[hEq.fvarId!]} (.targets #[] true)
    /- It may happen that at this point the goal is already solved (though this is rare)
       TODO: not sure this is the best way of checking it -/
    let goals ← getUnsolvedGoals
    assert! (goals.length ≤ 1) -- We focused on the main goal so there should be at most one goal
    if goals == [] then
      trace[Progress] "The main goal was solved!"
      pure (Ok #[])
    else
      trace[Progress] "goal after applying the eq and simplifying the binds: {← getMainGoal}"
      -- TODO: remove this? (some types get unfolded too much: we "fold" them back)
      let _ ← tryTac (simpAt true {} {addSimpThms := scalar_eqs} .wildcard_dep)
      trace[Progress] "goal after folding back scalar types: {← getMainGoal}"
      -- Clear the equality, unless the user requests not to do so
      if keep.isSome then pure ()
      else do
        let mgoal ← getMainGoal
        let mgoal ← mgoal.tryClearMany #[hEq.fvarId!]
        setGoals [mgoal]
      trace[Progress] "Unsolved goals: {← getUnsolvedGoals}"
      trace[Progress] "Goal after clearing the equality: {← getMainGoal}"
      -- Continue splitting following the post following the user's instructions
      match hPost with
      | none =>
        -- Sanity check
        if ¬ ids.isEmpty then
          logWarning m!"Too many ids provided ({ids}): there is no postcondition to split"
        return (Ok #[])
      | some hPost => do
        let rec splitPostWithIds (prevId : Name) (hPosts : List FVarId) (hPost : Expr) (ids0 : List (Option Name)) :
        TacticM (Result (Array FVarId) MessageData) := do
          match ids0 with
          | [] =>
            /- We used all the user provided ids.
               Split the remaining conjunctions by using fresh ids if the user
               instructed to fully split the post-condition, otherwise stop -/
            if splitPost then
              splitFullConjTac true hPost (λ asms => do
                pure (Ok (hPosts.reverse ++ (asms.map (fun x => x.fvarId!))).toArray))
            else pure (Ok (hPost.fvarId! :: hPosts).reverse.toArray)
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
            pure (Ok (hPost.fvarId! :: hPosts).reverse.toArray)
        let curPostId := (← hPost.fvarId!.getDecl).userName
        splitPostWithIds curPostId [] hPost ids
  match res with
  | Error msg => return (Error msg) -- Can we get there? We're using "return"
  | Ok hPosts =>
    -- Update the set of goals
    let curGoals ← getUnsolvedGoals
    trace[Progress] "current goals: {curGoals}"
    let newGoals := mvars.map Expr.mvarId!
    let newGoals ← newGoals.filterM fun mvar => not <$> mvar.isAssigned
    trace[Progress] "new goals: {newGoals}"
    -- Split between the goals which are propositions and the others
    let (newPropGoals, newNonPropGoals) ←
      newGoals.toList.partitionM fun mvar => do isProp (← mvar.getType)
    trace[Progress] "Prop goals: {newPropGoals}"
    trace[Progress] "Non prop goals: {← newNonPropGoals.mapM fun mvarId => do pure ((← mvarId.getDecl).userName, mvarId)}"
    -- Try to solve the goals which are propositions
    setGoals newPropGoals
    allGoalsNoRecover asmTac
    let newPropGoals ← getUnsolvedGoals
    /- Simplify the post-conditions in the main goal - note that we waited until now because by solving the preconditions
       we may have instantiated meta-variables -/
    setGoals curGoals
    match curGoals with
    | [] => pure ()
    | [ _ ] =>
      let args : SimpArgs :=
        {simpThms := #[← progressPostSimpExt.getTheorems],
         simprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs]}
      simpAt true { maxDischargeDepth := 0, failIfUnchanged := false }
            args (.targets hPosts false)
    | _ => throwError "Unexpected number of goals"
    let curGoals ← getUnsolvedGoals
    trace[Progress] "Main goal after simplifying the post-conditions: {curGoals}"
    /- Update the list of goals -/
    let newNonPropGoals ← newNonPropGoals.filterM fun mvar => not <$> mvar.isAssigned
    let newGoals := newNonPropGoals ++ newPropGoals
    trace[Progress] "Final remaining preconditions: {newGoals}"
    setGoals (newGoals ++ curGoals)
    trace[Progress] "progress: replaced the goals"
    --
    let mainGoal ← do
      match curGoals with
      | [] => pure none
      | [ g ] => pure (some g)
      | _ => throwError "Unexpected number of goals"
    pure (Ok ⟨ ⟨ newGoals.toArray, mainGoal ⟩, hPosts ⟩)

/-- Small utility: if `args` is not empty, return the name of the app in the first
    arg, if it is a const. -/
def getFirstArgAppName (args : Array Expr) : MetaM (Option Name) := do
  if args.size = 0 then pure none
  else
    (args.get! 0).withApp fun f _ => do
    if f.isConst then pure (some f.constName)
    else pure none

def getFirstArg (args : Array Expr) : Option Expr := do
  if args.size = 0 then none
  else some (args.get! 0)

/-- Helper: try to apply a theorem.

    Return the list of post-conditions we introduced if it succeeded. -/
def tryApply (keep keepPretty : Option Name) (ids : Array (Option Name)) (splitPost : Bool)
  (asmTac : TacticM Unit) (fExpr : Expr)
  (kind : String) (th : Option Expr) : TacticM (Option ProgressWithOutput) := do
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
          let res ← progressWith fExpr th keep keepPretty ids splitPost asmTac
          pure (some res)
        catch _ => pure none
  match res with
  | some (.Ok res) => pure (some res)
  | some (.Error msg) => throwError msg
  | none => pure none

-- The array of ids are identifiers to use when introducing fresh variables
def progressAsmsOrLookupTheorem (keep keepPretty : Option Name) (withTh : Option Expr)
  (ids : Array (Option Name)) (splitPost : Bool) (asmTac : TacticM Unit) :
  TacticM (ProgressGoals × UsedTheorem) := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  /- There might be uninstantiated meta-variables in the goal that we need
     to instantiate (otherwise we will get stuck). -/
  let goalTy ← instantiateMVars goalTy
  trace[Progress] "goal: {goalTy}"
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
    withProgressSpec isGoal goalTy fun {fArgsExpr := fExpr, ..} => do
    trace[Progress] "Expression to match: {fExpr}"
    pure fExpr
  -- If the user provided a theorem/assumption: use it.
  -- Otherwise, lookup one.
  match withTh with
  | some th => do
    match ← progressWith fExpr th keep keepPretty ids splitPost asmTac with
    | .Ok res =>
      -- Remark: exprToSyntax doesn't give the expected result
      return  (res.toProgressGoals, .givenExpr th)
    | .Error msg => throwError msg
  | none =>
    -- Try all the assumptions one by one and if it fails try to lookup a theorem.
    let ctx ← Lean.MonadLCtx.getLCtx
    let decls ← ctx.getDecls
    for decl in decls.reverse do
      trace[Progress] "Trying assumption: {decl.userName} : {decl.type}"
      let res ← do try progressWith fExpr decl.toExpr keep keepPretty ids splitPost asmTac catch _ => continue
      match res with
      | .Ok res => return (res.toProgressGoals, .localHyp decl)
      | .Error msg => throwError msg
    /- It failed: lookup the pspec theorems which match the expression *only
       if the function is a constant* -/
    let fIsConst ← do
      fExpr.consumeMData.withApp fun mf _ => do
      pure mf.isConst
    if ¬ fIsConst then throwError "Progress failed"
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
        match ← tryApply keep keepPretty ids splitPost asmTac fExpr "pspec theorem" pspecExpr with
        | some res => return (res.toProgressGoals, .progressThm pspec)
        | none => pure ()
      -- It failed: try to use the recursive assumptions
      trace[Progress] "Failed using a pspec theorem: trying to use a recursive assumption"
      -- We try to apply the assumptions of kind "auxDecl"
      let ctx ← Lean.MonadLCtx.getLCtx
      let decls ← ctx.getAllDecls
      let decls := decls.filter (λ decl => match decl.kind with
        | .default | .implDetail => false | .auxDecl => true)
      for decl in decls.reverse do
        trace[Progress] "Trying recursive assumption: {decl.userName} : {decl.type}"
        let res ← do try progressWith fExpr decl.toExpr keep keepPretty ids splitPost asmTac catch _ => continue
        match res with
        | .Ok res => return (res.toProgressGoals, .localHyp decl)
        | .Error msg => throwError msg
      -- Nothing worked: failed
      throwError "Progress failed: could not find a local assumption or a theorem to apply"

syntax progressArgs := ("keep" binderIdent)? ("with" term)? ("as" " ⟨ " binderIdent,* " ⟩")?

def parseProgressArgs
: TSyntax ``Aeneas.Progress.progressArgs -> TacticM (Option Name × Option Expr × Array (Option Name))
| args@`(progressArgs| $[keep $x]? $[with $pspec:term]? $[as ⟨ $ids,* ⟩]? ) =>  withMainContext do
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
  return (keep?, withTh?, ids)
| _ => throwUnsupportedSyntax

def evalProgress (keep keepPretty : Option Name) (withArg: Option Expr) (ids: Array (Option Name))
: TacticM Stats := do
  /- Simplify the goal -- TODO: this might close it: we need to check that and abort if necessary,
     and properly track that in the `Stats` -/
  simpAt true { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← progressSimpExt.getTheorems]} (.targets #[] true)
  withMainContext do
  let splitPost := true
  /- Preprocessing step for `singleAssumptionTac` -/
  let singleAssumptionTacDtree ← singleAssumptionTacPreprocess
  /- For scalarTac we have a fast track: if the goal is not a linear
     arithmetic goal, we skip (note that otherwise, scalarTac would try
     to prove a contradiction) -/
  let scalarTac : TacticM Unit := do
    trace[Progress] "Attempting to solve with `scalarTac`"
    if ← ScalarTac.goalIsLinearInt then
      /- Also: we don't try to split the goal if it is a conjunction
         (it shouldn't be), but we split the disjunctions. -/
      ScalarTac.scalarTac { split := false, fastSaturate := true }
    else
      throwError "Not a linear arithmetic goal"
  let simpLemmas ← Aeneas.ScalarTac.scalarTacSimpExt.getTheorems
  let localAsms ← (← (← getLCtx).getDecls).filterMapM fun decl => do
    if ← isProp decl.type then
      pure (some decl.fvarId)
    else pure none
  let simpArgs : SimpArgs := {simpThms := #[simpLemmas], hypsToUse := localAsms.toArray}
  let simpTac : TacticM Unit := do
    trace[Progress] "Attempting to solve with `simp [*]`"
    -- Simplify the goal
    Utils.simpAt false { maxDischargeDepth := 1 } simpArgs (.targets #[] true)
    -- Raise an error if the goal is not proved
    allGoalsNoRecover (throwError "Goal not proved")
  /- We use our custom assumption tactic, which instantiates meta-variables only if there is a single
     assumption matching the goal. -/
  let customAssumTac : TacticM Unit := do
    trace[Progress] "Attempting to solve with `singleAssumptionTac`"
    singleAssumptionTacCore singleAssumptionTacDtree
  let (goals, usedTheorem) ← progressAsmsOrLookupTheorem keep keepPretty withArg ids splitPost (
    withMainContext do
    trace[Progress] "trying to solve precondition: {← getMainGoal}"
    firstTac [customAssumTac, simpTac, simpTac, scalarTac]
    trace[Progress] "Precondition solved!")
  trace[Progress] "Progress done"
  return ⟨ goals, usedTheorem ⟩

elab (name := progress) "progress" args:progressArgs : tactic => do
  let (keep?, withArg, ids) ← parseProgressArgs args
  evalProgress keep? none withArg ids *> return ()

elab tk:"progress?" args:progressArgs : tactic => do
  let (keep?, withArg, ids) ← parseProgressArgs args
  let stats ← evalProgress keep? none withArg ids
  let mut stxArgs := args.raw
  if stxArgs[1].isNone then
    let withArg := mkNullNode #[mkAtom "with", ←stats.usedTheorem.toSyntax]
    stxArgs := stxArgs.setArg 1 withArg
  let tac := mkNode `Aeneas.Progress.progress #[mkAtom "progress", stxArgs]
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)

syntax (name := letProgress)"let" noWs "*" " ⟨ " binderIdent,* " ⟩" colGe " ← " colGe term: tactic

def parseLetProgress
: TSyntax ``Aeneas.Progress.letProgress -> TacticM (Expr × Array (Option Name))
| args@`(tactic| let* ⟨ $ids,* ⟩ ← $pspec:term) =>  withMainContext do
  trace[Progress] "Progress arguments: {args.raw}"
  let withThm : Expr ← do
    /- We have to make a case disjunction, because if we treat identifiers like
      terms, then Lean will not succeed in infering their implicit parameters
      (`progress` does that by matching against the goal). -/
    match pspec with
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[Progress] "With arg (local decl): {stx.raw}"
        pure decl.toExpr
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[Progress] "With arg (theorem): {stx.raw}"
        let some e ← Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {pspec}"
        pure e
    | term => do
      trace[Progress] "With arg (term): {term}"
      Tactic.elabTerm term none
  let ids := ids.getElems.map fun
      | `(binderIdent| $name:ident) => some name.getId
      | _ => none
  trace[Progress] "User-provided ids: {ids}"
  return (withThm, ids)
| _ => throwUnsupportedSyntax

elab tk:letProgress : tactic => do
  withMainContext do
  let (withArg, ids) ← parseLetProgress tk
  let _ ← evalProgress none (some (.str .anonymous "_")) withArg ids

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
    simp [*, h1]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 ⟩
    simp [*, h1]

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with Aeneas.Std.UScalar.add_spec as ⟨ z, h1 ⟩
    simp [*, h1]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with Aeneas.Std.IScalar.add_spec as ⟨ z, h1 ⟩
    simp [*, h1]

  example {ty} {x y : UScalar ty}
    (hmax : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep h with UScalar.add_spec as ⟨ z ⟩
    simp [*, h]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep h with IScalar.add_spec as ⟨ z ⟩
    simp [*, h]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    -- This spec theorem is suboptimal, but it is good to check that it works
    progress with UScalar.add_spec as ⟨ z, h1 ⟩
    simp [*, h1]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress with U32.add_spec as ⟨ z, h1 ⟩
    simp [*, h1]

  example {x y : U32}
    (hmax : x.val + y.val ≤ U32.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
    progress keep _ as ⟨ z, h1 ⟩
    simp [*, h1]

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
    progress? says progress with Aeneas.Std.alloc.vec.Vec.update_spec
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
    simp [*, h1]

  example {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ x.val + y.val)
    (hmax : x.val + y.val ≤ IScalar.max ty) :
    False ∨ (∃ z, x + y = ok z ∧ z.val = x.val + y.val) := by
    right
    progress? keep _ as ⟨ z, h1 ⟩ says progress keep _ with Aeneas.Std.IScalar.add_spec as ⟨ z, h1 ⟩
    simp [*, h1]

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
      progress? as ⟨ z1, h ⟩ says progress with Aeneas.Progress.Test.add_spec' as ⟨ z1, h ⟩
      progress? as ⟨ z2, h ⟩ says progress with Aeneas.Progress.Test.add_spec' as ⟨ z2, h ⟩
  end

  /- Checking that `add_spec'` went out of scope -/
  example (x y : U32) (h : 2 * x.val + 2 * y.val ≤ U32.max) :
    ∃ z, add1 x y = ok z := by
    rw [add1]
    progress? as ⟨ z1, h ⟩ says progress with Aeneas.Std.U32.add_spec as ⟨ z1, h ⟩
    progress? as ⟨ z2, h ⟩ says progress with Aeneas.Std.U32.add_spec as ⟨ z2, h ⟩

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
    progress as ⟨ c', hc' ⟩ -- we have: `hc' : c'.bv = c.bv >>> 16`
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
      progress; fsimp [Nat.log2]
      assumption

  end Ntt

end Test

end Progress

end Aeneas
