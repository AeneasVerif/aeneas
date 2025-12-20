import AeneasMeta.Utils
import AeneasMeta.Simp

namespace Aeneas.Split

open Lean Meta Elab Tactic

def mkExists (var body : Expr) : MetaM Expr := do
  mkAppM ``Exists #[← mkLambdaFVars #[var] body]

def mkExistsSeq (vars : List Expr) (body : Expr) : MetaM Expr := do
  match vars with
  | [] => pure body
  | v :: vars =>
    let body ← mkExistsSeq vars body
    mkExists v body

def mkOrSeq (disjs : List Expr) : MetaM Expr := do
  match disjs with
  | [] => pure (mkConst ``False)
  | [x] => pure x
  | x :: y => pure (mkOr x (← mkOrSeq y))

/- This example show how to use a `casesOn` lemma to generate case disjunctions. -/
example (l : List α) : l = [] ∨ ∃ hd tl, l = hd :: tl :=
  @List.casesOn α (fun (l : List α) => (l = []) ∨ (∃ (hd : α) (tl : List α), l = hd :: tl)) l
    (by simp)
    (by simp)

theorem imp_or {A B C : Prop} : (A → C) → (B → C) → (A ∨ B) → C := by grind

/-- Split over a `casesOn` theorem or a `matcher` and introduce an **e**quality.

This function does not attempt to substitute the expression we split on, but rather
introduces an equality in the context, hence the name "esplit" (equality split).

Ex.: given goal `α : Type, l : List α ⊢ P` and theorem:
```
List.casesOn : {α : Type u} →
  {motive : List α → Sort u_1} →
    (t : List α) →
    motive [] →
    ((head : α) → (tail : List α) → motive (head :: tail)) →
    motive t
```
`esplit l "h" [[], ["hd", "tl"]]` will introduce the following goals:
```
α : Type, l : List α, h : l = [] ⊢ P
α : Type, l : List α, hd : α, tl : List α, h : l = hd :: tl ⊢ P
```

We return the fvars introduced for the variables appearing af
-/
def esplitCasesOn (isMatcher : Bool) (e : Expr) (casesOnName : Name) (h : Name) (vars : List (List (Option Name))) :
  TacticM (List (Array FVarId × FVarId × MVarId)) :=
  withTraceNode `Utils (fun _ => do pure m!"esplitCasesOn") do
  Tactic.focus do
  -- Check that the expression is an inductive
  let ety ← inferType e
  ety.consumeMData.withApp fun ty tyParams => do
  let .const tyName _ := ty
    | throwError "Could not decompose the type"
  -- Lookup the `casesOn` theorem
  let env ← getEnv
  let some th := env.findAsync? casesOnName
    | throwError "Could not find theorem: {casesOnName}"
  -- Decompose the theorem
  -- the first level is for the output of `motive` (we choose `0` for `Prop`)
  let th ← Term.mkConst casesOnName
  let thTy ← inferType th
  let (args, binderInfo, thTy) ← forallMetaTelescope thTy
  trace[Utils] "args: {Array.map (fun (arg, binder) => if binder == BinderInfo.default then m!"{arg}" else m!"#{arg}") (Array.zip args binderInfo)}, thTy: {thTy}"
  /- Find the first non implicit parameter:
     - if the theorem is an inductive casesOn theorem, then this is the scrutinee,
        and the parameter just before is the motive
     - if the theorem is a matcher, then this is the motive -/
  let mut i := 0
  while i < args.size do
    if binderInfo[i]! == .default then break
    i := i + 1
  let (params, motive, scrutinee, cases) ← do
    if not isMatcher then
      if i ≥ args.size - 1 || i = 0 then throwError "Could not analyze the `casesOn` theorem"
      let params := args.take (i - 1)
      let motive := args[i - 1]!
      let scrutinee := args[i]!
      let cases := args.drop (i + 1)
      pure (params, motive, scrutinee, cases)
    else
      if i + 1 ≥ args.size - 1 then throwError "Could not analyze the `casesOn` theorem"
      let params := args.take i
      let motive := args[i]!
      let scrutinee := args[i + 1]!
      let cases := args.drop (i + 2)
      pure (params, motive, scrutinee, cases)
  trace[Utils] "params: {params}, motive: {motive}, scrutinee: {scrutinee}, cases: {cases}"
  let _ ← isDefEq scrutinee e
  /- Create the motive.

  Taking `List` as example, we want to create an expression of the shape:
  `fun l => l = [] ∨ ∃ hd tl, l = hd :: tl`

  Note that the cases are of the shape (taking `List` for example):
  ```
  ?nil: ?motive []
  ?cons: (head : ?α) → (tail : List ?α) → ?motive (head :: tail)
  ```
  so we simply need to analyze them to create the various cases.
  -/
  -- First, introduce a free variable for the input of the motive
  withLocalDecl `x .default ety fun x => do
  -- Create the various cases
  let disjs ← cases.mapM fun case => do
    forallTelescope (← inferType case) fun vars body => do
    body.consumeMData.withApp fun _ args => do
    -- Create the equality (ex.: `l = hd :: tl`)
    let (eq, eq') ←
      if h: args.size ≠ 1 then throwError "Unexpected: args.size: {args.size}"
      else
        trace[Utils] "About to create the equality: {x} = {args[0]}"
        pure (← mkAppM ``Eq #[x, args[0]], ← mkAppM ``Eq #[e, args[0]])
    -- Add the existentials (ex.: `∃ hd tl, l = hd :: tl)`
    pure (← mkExistsSeq vars.toList eq, ← mkExistsSeq vars.toList eq')
  trace[Utils] "disjs: {disjs}"
  let (disjs, thTyDisjs) := disjs.unzip
  -- Create the disjunction and add the lambda
  let disj ← mkOrSeq disjs.toList
  let thTy ← mkOrSeq thTyDisjs.toList
  let motiveExpr ← mkLambdaFVars #[x] disj
  let _ ← isDefEq motive motiveExpr
  trace[Utils] "motive: {motive}"
  -- Prove the cases - TODO: for now we call `simp`. We should make this more precise.
  let (simpCtx, simprocs) ← Aeneas.Simp.mkSimpCtx false {} .simp {}
  for case in cases do
    trace[Utils] "Proving: {case}"
    let (out, _) ← simpTarget case.mvarId! simpCtx simprocs
    if out.isSome then throwError "Could not prove: {case}"
  -- Put everything together
  let th ← mkAppOptM casesOnName (args.map some)
  trace[Utils] "th: {← inferType th}"
  -- Introduce the theorem
  Utils.addDeclTac h th thTy (asLet := false) fun th => do
  trace[Utils] "th: {th}: {← inferType th}"
  let goal ← getMainGoal
  let target ← goal.getType
  trace[Utils] "Main goal: {goal}"
  let (_, goal) ← goal.revert #[th.fvarId!]
  trace[Utils] "Goal after revert: {goal}"
  goal.withContext do
  -- Repeatedly apply `imp_or`
  let rec applyImpOr (goal : MVarId) (hTy : Expr) (cases : List Expr) : TacticM (List MVarId) := do
    match cases with
    | [] => throwError "Unexpected"
    | [_] => pure [goal]
    | _ :: cases =>
      trace[Utils] "hTy: {hTy}"
      hTy.consumeMData.withApp fun or? args => do
      trace[Utils] "or?: {or?}, args: {args}"
      if args.size ≠ 2 then throwError "Unexpected"
      let disj0 := args[0]!
      let disj1 := args[1]!
      let goal0 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow disj0 target)
      let goal1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow disj1 target)
      goal.assign (← mkAppOptM ``imp_or #[disj0, disj1, target, goal0, goal1])
      let goals ← applyImpOr goal1.mvarId! disj1 cases
      pure (goal0.mvarId! :: goals)
  let goals ← applyImpOr goal thTy cases.toList
  /- We need to intro the equality and destruct the existentials -- first we need to resize
    the list of names (just in case) -/
  let varsEnd := List.map (fun _ => []) (List.range' 0 (goals.length - vars.length))
  let vars : List (List (Option Name)) := (vars.take goals.length) ++ varsEnd
  let goals ← (goals.zip vars).mapM fun (goal, vars) => do
    let (h, goal) ← goal.intro h
    setGoals [goal]
    goal.withContext do
    Utils.splitAllExistsTac (.fvar h) vars fun fvars h _ => do
    /- When the theorem is actually a matcher, it can happen that it introduces useless unit variables:
       we try to get rid of those -/
    if hSize : fvars.size = 1 then
      let fvar := fvars[0]
      if (← inferType fvar).isConstOf ``Unit then
        let ngoal ← (← getMainGoal).tryClear fvar.fvarId!
        pure (#[], h.fvarId!, ngoal)
      else
        pure (fvars.map Expr.fvarId!, h.fvarId!, ← getMainGoal)
    else
      pure (fvars.map Expr.fvarId!, h.fvarId!, ← getMainGoal)
  --
  let ngoals := goals.map fun (_, _, g) => g
  setGoals ngoals
  trace[Utils] "Done: {ngoals}"
  pure goals

local elab "esplitCasesOn" th:ident x:term : tactic => do
  let some th ← Term.resolveId? th (withInfo := true)
    | throwError m!"Could not find theorem: {th}"
  th.withApp fun th _ => do
  let .const thName _ := th
    | throwError "Unexpected"
  let x ← Term.elabTerm x none
  let _ ← esplitCasesOn true x thName `h []

def Test.test {α} (x : Option α) : Nat := match x with | none => 0 | some _ => 1

example α (x : Option α) : x = none ∨ ∃ v, x = some v :=
  @Test.test.match_1 α (fun x => x = none ∨ ∃ v, x = some v) x (by simp) (by simp)

/--
error: unsolved goals
α : Type u_1
x : Option α
h : x = none
⊢ True

α : Type u_1
x : Option α
x✝ : α
h : x = some x✝
⊢ True
-/
#guard_msgs in
example {α} (x : Option α) : True := by
  esplitCasesOn Test.test.match_1 x

/-- Split over an inductive type and introduce an **e**quality.

Ex.: given goal `α : Type, l : List α ⊢ P`, `esplit l "h" [[], ["hd", "tl"]]` will introduce the following goals:
```
α : Type, l : List α, h : l = [] ⊢ P
α : Type, l : List α, hd : α, tl : List α, h : l = hd :: tl ⊢ P
```

We return the fvars introduced for:
- the variables introduced when decomposing the inductive
- the equality introduced in the context
-/
def esplit (e : Expr) (h : Name) (vars : List (List (Option Name))) :
  TacticM (List (Array FVarId × FVarId × MVarId)) :=
  Tactic.focus do
  withTraceNode `Utils (fun _ => do pure m!"esplit") do
  -- Check that the expression is an inductive
  let ety ← inferType e
  ety.consumeMData.withApp fun ty _ => do
  let .const tyName _ := ty
    | throwError "Could not decompose the type"
  -- Lookup the type declaration
  let env ← getEnv
  let some decl := env.findAsync? tyName
    | throwError "Could not find declaration for: {tyName}"
  let .inductInfo _ := decl.constInfo.get
    | throwError "Not an inductive"
  trace[Utils] "Inductive"
  -- Lookup the `casesOn` theorem
  let casesOnName := tyName ++ `casesOn
  esplitCasesOn false e casesOnName h vars

local elab "esplit" x:term : tactic => do
  let x ← Term.elabTerm x none
  let _ ← esplit x `h []

theorem bool_disj_imp (b : Bool) (P : Prop) : (b = true → P) → (b = false → P) → P := by
  grind

/-- Split a boolean and introduce an equality.

Example: given goal `b : Bool ⊢ P`, `esplitBool b h` generates the following goals:
```
b : Bool, h : b = true ⊢ P
b : Bool, h : b = false ⊢ P
```
-/
def esplitBool (b : Expr) (h : Name) : TacticM (List (FVarId × MVarId)) := do
  focus do withMainContext do
  -- Apply the theorem
  let tgt ← getMainTarget
  let thm ← mkAppM ``bool_disj_imp #[b, tgt]
  let thmTy ← inferType thm
  let (goals, _, _) ← forallMetaTelescope thmTy
  let thm := mkAppN thm goals
  let goal ← getMainGoal
  goal.assign thm
  let goals := goals.toList.map Expr.mvarId!
  -- Introduce the equality
  let goals ← goals.mapM fun goal => goal.intro h
  --
  setGoals (goals.map Prod.snd)
  pure goals

/--
error: unsolved goals
α : Type u_1
l : List α
h : l = []
⊢ True

α : Type u_1
l : List α
x✝¹ : α
x✝ : List α
h : l = x✝¹ :: x✝
⊢ True
-/
#guard_msgs in
example {α} (l : List α) : True := by
  esplit l

end Aeneas.Split
