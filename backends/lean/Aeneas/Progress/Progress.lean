import Lean
import Aeneas.ScalarTac
import Aeneas.Progress.Core
import Aeneas.Std -- TODO: remove?
import Aeneas.FSimp

namespace Aeneas

namespace Progress

open Lean Elab Term Meta Tactic
open Utils

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
def scalar_eqs := [
  ``uscalar_usize_eq, ``uscalar_u8_eq, ``uscalar_u16_eq, ``uscalar_u32_eq, ``uscalar_u64_eq, ``uscalar_u128_eq,
  ``iscalar_isize_eq, ``iscalar_i8_eq, ``iscalar_i16_eq, ``iscalar_i32_eq, ``iscalar_i64_eq, ``iscalar_i128_eq
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

def progressWith (fExpr : Expr) (th : Expr)
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
  /- There might be meta-variables in the type if the theorem comes from a local declaration,
     especially if this declaration was introduced by a tactic -/
  let thTy ← instantiateMVars (← inferType th)
  trace[Progress] "Looked up theorem/assumption type: {thTy}"
  -- Normalize to inline the let-bindings
  let thTy ← normalizeLetBindings thTy
  trace[Progress] "After normalizing the let-bindings: {thTy}"
  -- TODO: the tactic fails if we uncomment withNewMCtxDepth
  -- withNewMCtxDepth do
  let (mvars, binders, thExBody) ← forallMetaTelescope thTy.consumeMData
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
  let th ← mkAppOptM' th (mvars.map some)
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
        (simpAt true {} [] [] []
               [``Std.bind_tc_ok, ``Std.bind_tc_fail, ``Std.bind_tc_div,
                -- Those ones are quite useful to simplify the goal further by eliminating
                -- existential quantifiers, for instance.
                ``and_assoc, ``Std.Result.ok.injEq,
                ``exists_eq_left, ``exists_eq_left', ``exists_eq_right, ``exists_eq_right',
                ``exists_eq, ``exists_eq', ``true_and, ``and_true,
                ``Prod.mk.injEq]
               [hEq.fvarId!] (.targets #[] true))
    -- It may happen that at this point the goal is already solved (though this is rare)
    -- TODO: not sure this is the best way of checking it
    if (← getUnsolvedGoals) == [] then pure .Ok
    else
       trace[Progress] "goal after applying the eq and simplifying the binds: {← getMainGoal}"
       -- TODO: remove this (some types get unfolded too much: we "fold" them back)
       let _ ← tryTac (simpAt true {} [] [] [] scalar_eqs [] .wildcard_dep)
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
          logWarning m!"Too many ids provided ({ids}): there is no postcondition to split"
         return .Ok
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
             else
              logWarning m!"Too many ids provided ({ids0}) not enough conjuncts to split in the postcondition"
              pure .Ok
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
    -- Split between the goals which are propositions and the others
    let (newPropGoals, newNonPropGoals) ←
      newGoals.toList.partitionM fun mvar => do isProp (← mvar.getType)
    trace[Progress] "Prop goals: {newPropGoals}"
    trace[Progress] "Non prop goals: {← newNonPropGoals.mapM fun mvarId => do pure ((← mvarId.getDecl).userName, mvarId)}"
    -- Try to solve the goals which are propositions
    setGoals newPropGoals
    allGoalsNoRecover asmTac
    --
    let newPropGoals ← getUnsolvedGoals
    let newNonPropGoals ← newNonPropGoals.filterM fun mvar => not <$> mvar.isAssigned
    let newGoals := newNonPropGoals ++ newPropGoals
    trace[Progress] "Final remaining preconditions: {newGoals}"
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

/-- Helper: try to apply a theorem.

    Return true if it succeeded. -/
def tryApply (keep : Option Name) (ids : Array (Option Name)) (splitPost : Bool)
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
        catch _ => pure none
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
    | .Ok =>
      -- Remark: exprToSyntax doesn't give the expected result
      return ← Lean.Meta.Tactic.TryThis.delabToRefinableSyntax th
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
        let pspecExpr ← Term.mkConst pspec
        if ← tryApply keep ids splitPost asmTac fExpr "pspec theorem" pspecExpr
        then return (mkIdent pspec)
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

syntax optIdent := ident <|> "_"
syntax progressArgs := ("keep" optIdent)? ("with" term)? ("as" " ⟨ " optIdent,* " ⟩")?

def parseProgressArgs /- {{{ -/
: TSyntax ``Aeneas.Progress.progressArgs -> TacticM (Option Name × Option Expr × Array (Option Name))
| args@`(progressArgs| $[keep $x]? $[with $pspec:term]? $[as ⟨ $ids,* ⟩]? ) =>  withMainContext do
  trace[Progress] "Progress arguments: {args.raw}"
  let keep?: Option Name <- Option.sequence <| x.map fun
    | `(optIdent| _) => mkFreshAnonPropUserName
    | `(optIdent| $name:ident) => pure name.getId
    | _ => throwUnsupportedSyntax
  trace[Progress] "Keep: {keep?}"
  let withTh?: Option Expr <- Option.sequence <| pspec.map fun
    /- We have to make a case disjunction, because if we treat identifiers like
       terms, then Lean will not succeed in infering their implicit parameters
       (`progress` does that by matching against the goal). -/
    | `($stx:ident) => do
      match (<- getLCtx).findFromUserName? stx.getId with
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
  if let .some pspec := withTh? then trace[Progress] "With arg: elborated expression {pspec}"
  let ids := ids.getD ∅
    |>.getElems.map fun
      | `(optIdent| $name:ident) => some name.getId
      | _ => none
  trace[Progress] "User-provided ids: {ids}"
  return (keep?, withTh?, ids)
| _ => throwUnsupportedSyntax/- }}} -/

def evalProgress (keep: Option Name)(withArg: Option Expr)(ids: Array (Option Name))
: TacticM Stats := do
  withMainContext do
  let splitPost := true
  /- For scalarTac we have a fast track: if the goal is not a linear
     arithmetic goal, we skip (note that otherwise, scalarTac would try
     to prove a contradiction) -/
  let scalarTac : TacticM Unit := do
    if ← ScalarTac.goalIsLinearInt then
      -- Also: we don't try to split the goal if it is a conjunction
      -- (it shouldn't be), but we split the disjunctions.
      ScalarTac.scalarTac { split := false, fastSaturate := true }
    else
      throwError "Not a linear arithmetic goal"
  let simpLemmas ← Aeneas.ScalarTac.scalarTacSimpExt.getTheorems
  let simpTac : TacticM Unit := do
      -- Simplify the goal
      Utils.simpAt false {} [] [simpLemmas] [] [] [] (.targets #[] true)
      -- Raise an error if the goal is not proved
      allGoalsNoRecover (throwError "Goal not proved")
  -- We use our custom assumption tactic, which instantiates meta-variables only if there is a single
  -- assumption matching the goal.
  let customAssumTac : TacticM Unit := singleAssumptionTac
  let usedTheorem ← progressAsmsOrLookupTheorem keep withArg ids splitPost (
    withMainContext do
    trace[Progress] "trying to solve precondition: {← getMainGoal}"
    firstTac [customAssumTac, simpTac, scalarTac]
    trace[Progress] "Precondition solved!")
  trace[Progress] "Progress done"
  return {
    usedTheorem
  }
elab (name := progress) "progress" args:progressArgs : tactic => do
  let (keep?, withArg, ids) ← parseProgressArgs args
  evalProgress keep? withArg ids *> return ()

elab tk:"progress?" args:progressArgs : tactic => do
  let (keep?, withArg, ids) <- parseProgressArgs args
  let stats ← evalProgress keep? withArg ids
  let mut stxArgs := args.raw
  if stxArgs[1].isNone then
    let withArg := mkNullNode #[mkAtom "with", stats.usedTheorem]
    stxArgs := stxArgs.setArg 1 withArg
  let tac := mkNode `Aeneas.Progress.progress #[mkAtom "progress", stxArgs]
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)

namespace Test
  open Std Result

  -- Show the traces:
  -- set_option trace.Progress true
  -- set_option pp.rawOnError true

  set_option says.verify true

  -- The following command displays the database of theorems:
  -- #eval showStoredPSpec
  open alloc.vec

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
    (f : U32 → Result Unit) (h : ∀ x, f x = .ok ()) :
    f x = ok () := by
    progress


  example {x : U32}
    (f : U32 → Result Unit) (h : ∀ x, f x = .ok ()) :
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
    def Tree.size (t : Tree) : Result Int :=
      match t with
      | .mk trees => trees.size

    def Trees.size (t : Trees) : Result Int :=
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
  def add (x y : U32) : Result U32 := x + y

  section
    /- Testing progress on theorems containing local let-bindings as well as
       the `local` attribute kind -/
    @[local progress] theorem add_spec' (x y : U32) (h : x.val + y.val ≤ U32.max) :
      let tot := x.val + y.val
      ∃ z, x + y = ok z ∧ z.val = tot := by
      simp
      progress with U32.add_spec
      scalar_tac

    def add1 (x y : U32) : Result U32 := do
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
  variable (f : List α → Result Bool)
  variable (f_spec : ∀ l i, P i l → ∃ b, f l = ok b)

  example (l : List α) (h : P i l) :
    ∃ b, f l = ok b := by
    progress? as ⟨ b ⟩ says progress with f_spec as ⟨ b ⟩

  /- Progress using a term -/
  example {x: U32}
    (f : U32 → Result Unit)
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

  namespace Ntt
    def wfArray (_ : Array U16 256#usize) : Prop := True

    def nttLayer (a : Array U16 256#usize) (_k : Usize) (_len : Usize) : Result (Array U16 256#usize) := ok a

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

    def ntt (x : Array U16 256#usize) : Result (Array U16 256#usize) := do
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

    /-
    simp took 24.6ms
    simp took 18.3ms
    tactic execution of Aeneas.Progress.progress took 43.1ms
    simp took 13.8ms
    simp took 21.1ms
    simp took 17ms
    tactic execution of Aeneas.Progress.progress took 115ms
    simp took 18.2ms
    simp took 20.7ms
    simp took 17.4ms
    tactic execution of Aeneas.Progress.progress took 189ms
    simp took 22.8ms
    simp took 21.8ms
    simp took 17.1ms
    tactic execution of Aeneas.Progress.progress took 259ms
    simp took 28.9ms
    simp took 21.4ms
    simp took 17.7ms
    tactic execution of Aeneas.Progress.progress took 324ms
    simp took 33.9ms
    simp took 21.7ms
    simp took 17.7ms
    tactic execution of Aeneas.Progress.progress took 407ms
    simp took 39.1ms
    simp took 21.5ms
    simp took 17.8ms
    tactic execution of Aeneas.Progress.progress took 483ms
    simp took 44ms
    simp took 21ms
    simp took 17.7ms
    tactic execution of Aeneas.Progress.progress took 563ms
    simp took 44.6ms
    simp took 21.7ms
    simp took 17.7ms
    tactic execution of Aeneas.Progress.progress took 631ms
    simp took 45.1ms
    simp took 21.7ms
    simp took 17.5ms
    tactic execution of Aeneas.Progress.progress took 706ms
    simp took 44.6ms
    simp took 21.9ms
    simp took 18.2ms
    tactic execution of Aeneas.Progress.progress took 789ms
    simp took 45.5ms
    simp took 21.1ms
    simp took 18.7ms
    tactic execution of Aeneas.Progress.progress took 864ms
    simp took 45.4ms
    simp took 22.6ms
    dsimp took 11.3ms
    simp took 18.5ms
    tactic execution of Aeneas.Progress.progress took 951ms
    simp took 46.5ms
    tactic execution of Lean.Parser.Tactic.tacticSeq1Indented took 19ms
    type checking took 81.3ms

    After using `saturateFast` in `scalar_tac`:
    simp took 26.2ms
    simp took 20.6ms
    simp took 10ms
    tactic execution of Aeneas.Progress.progress took 20.9ms
    simp took 21.9ms
    simp took 18.5ms
    tactic execution of Aeneas.Progress.progress took 23.1ms
    simp took 18.1ms
    simp took 21.6ms
    simp took 18ms
    tactic execution of Aeneas.Progress.progress took 38.8ms
    simp took 18ms
    simp took 23.1ms
    simp took 17.6ms
    simp took 10.3ms
    tactic execution of Aeneas.Progress.progress took 31.8ms
    simp took 19.8ms
    simp took 22.1ms
    simp took 18ms
    tactic execution of Aeneas.Progress.progress took 34.9ms
    simp took 22.9ms
    simp took 22.8ms
    simp took 17.8ms
    tactic execution of Aeneas.Progress.progress took 40.9ms
    simp took 26.5ms
    simp took 23.1ms
    simp took 20.1ms
    simp took 19.4ms
    simp took 10.1ms
    tactic execution of Aeneas.Progress.progress took 48.2ms
    simp took 29ms
    simp took 22.9ms
    simp took 18.6ms
    tactic execution of Aeneas.Progress.progress took 51.1ms
    simp took 29.1ms
    simp took 22.5ms
    simp took 19.2ms
    tactic execution of Aeneas.Progress.progress took 56.1ms
    simp took 29.2ms
    simp took 22.5ms
    simp took 19.5ms
    simp took 10.3ms
    tactic execution of Aeneas.Progress.progress took 60ms
    simp took 29.7ms
    simp took 23.4ms
    simp took 19.6ms
    simp took 10.5ms
    tactic execution of Aeneas.Progress.progress took 67.4ms
    simp took 29.1ms
    simp took 23.6ms
    simp took 18.6ms
    simp took 10.7ms
    tactic execution of Aeneas.Progress.progress took 70.1ms
    simp took 30ms
    simp took 24ms
    simp took 20.1ms
    simp took 10.5ms
    tactic execution of Aeneas.Progress.progress took 76.5ms
    simp took 28.7ms
    tactic execution of Lean.Parser.Tactic.tacticSeq1Indented took 17.4ms
    type checking took 86.5ms
    -/
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
