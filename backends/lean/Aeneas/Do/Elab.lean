import Lean
import Aeneas.Std
import Aeneas.Do.Init

open Lean Elab Parser Term Meta

namespace Aeneas

/-- Continuation monad transformer -/
def ContT (r : Type u) (m : Type u → Type v) (a : Type u) : Type (max u v) :=
  (a → m r) → m r

namespace ContT

instance : Monad (ContT r m) where
  pure a k := k a
  bind x f k := x (fun a => f a k)

instance [Monad m] : MonadLift m (ContT r m) where
  monadLift x k := x >>= k

instance [MonadExceptOf ε m] [Monad m] : MonadExceptOf ε (ContT r m) where
  throw e := fun _ => throw e
  tryCatch x h := fun k => tryCatch (x k) (fun e => h e k)

instance [MonadRef m] [Monad m] : MonadRef (ContT r m) where
  getRef := fun k => do let ref ← MonadRef.getRef; k ref
  withRef ref x := fun k => MonadRef.withRef ref (x k)

instance [AddErrorMessageContext m] [Monad m] : AddErrorMessageContext (ContT r m) where
  add stx msg := fun k => do let r ← AddErrorMessageContext.add stx msg; k r

instance [Monad m] [MonadQuotation m] : MonadQuotation (ContT r m) where
  getCurrMacroScope := fun k => do let s ← getCurrMacroScope; k s
  getContext := fun k => do let ctx ← MonadQuotation.getContext; k ctx
  withFreshMacroScope x := fun k => withFreshMacroScope (x k)
  

@[inline] def run (x : ContT r m a) (k : a → m r) : m r := x k

@[inline] def runPure [Monad m] (x : ContT r m r) : m r := x pure

end ContT

namespace Do

/-- Cached information about the monad extracted from the expected type of the `do` block.-/
structure Context where
  m : Expr
  /-- Cached `Bind m` instance -/
  bindInst : Expr
  /-- Cached `Pure m` instance -/
  pureInst : Expr
  /-- The expected element type `α` from the do-block's expected type `m α` -/
  expectedAlpha : Expr

abbrev ElabM := ReaderT Context $ ContT Expr TermElabM

/-- Extract the monad `m` from an expected type `m α` and synthesizes and caches the 
    `Bind` and `Pure` instances for `m`. -/
def mkContext (expectedType : Expr) : TermElabM Context := do
  let expectedType ← whnf expectedType
  let (m, α) ← match expectedType with
    | Expr.app m α => pure (m, α)
    | _ => throwError "expected a monadic type `m α`, got {indentExpr expectedType}"
  let bindInst ← synthInstance (← mkAppM ``Bind #[m])
  let pureInst ← synthInstance (← mkAppM ``Pure #[m])
  return { m, bindInst, pureInst, expectedAlpha := α }

-- TODO: clean this up
-- TODO: clean this up
def ElabM.mkBind (e k : Expr) : ElabM Expr := do
  let ctx ← read
  let eType ← instantiateMVars =<< inferType e
  let .some (α : Expr) := eType.getAppArgs[0]? | throwError "expected monadic type, got{indentExpr eType}"
  let kBody ← inferType (Expr.app k (← mkFreshExprMVar α)) >>= instantiateMVars
  let β ← match kBody with
    | Expr.app _ b => pure b
    | _ => throwError "mkBind: expected monadic return type, got{indentExpr kBody}"
  let mType ← instantiateMVars =<< inferType ctx.m
  let (u, v) ← match mType with
    | Expr.forallE _ (Expr.sort (.succ u)) (Expr.sort (.succ v)) _ => pure (u, v)
    | _ => throwError "mkBind: unexpected monad type{indentExpr mType}"
  return mkApp6 (mkConst ``Bind.bind [u, v]) ctx.m ctx.bindInst α β e k

/-- Build the expected monadic type `m α` for a sub-expression. -/
def ElabM.mkMonadicType (α : Expr) : ElabM Expr := read >>= fun ctx => pure (mkApp ctx.m α)

/-- Run a `Do.ElabM` computation, given an expected type for the whole `do` block. -/
def ElabM.execute (x : ElabM Expr) (expectedType : Expr) : TermElabM Expr := do
  let ctx ← mkContext expectedType
  (x.run ctx).runPure

/-- Run `body fvar` under a fresh local declaration `name : type` -/
def ElabM.withLocalDeclD (name : Name) (type : Expr) (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLocalDeclD name type fun fvar =>
      (body fvar).run ctx |>.run k

/-- Run `body fvar` under a fresh let declaration `let name : type := value` -/
def ElabM.withLetDecl (name : Name) (type : Expr) (value : Expr)
    (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLetDecl name type value fun fvar =>
      (body fvar).run ctx |>.run k

abbrev DoElem := TSyntax `doElem

def getDoElems (doSeq : TSyntax ``doSeq) : ElabM (List DoElem) := do
  match doSeq with
  | `(doSeq| $[$elems $[;]?]*) => return elems.toList
  | _ => throwError "unexpected `doSeq` syntax {indentD doSeq}"

partial def buildCurriedLambda (names : List Name) (types : List Expr)
    (body : ElabM Expr) : ElabM Expr :=
  match names, types with
  | [], _ | _, [] => body
  | [n], [t] =>
    ElabM.withLocalDeclD n t fun fvar => do
      let bodyExpr ← body
      mkLambdaFVars #[fvar] bodyExpr
  | n :: ns, t :: ts =>
    ElabM.withLocalDeclD n t fun fvar => do
      let inner ← buildCurriedLambda ns ts body
      mkLambdaFVars #[fvar] inner

partial def extractPatNames (pat : Syntax) : List Name :=
  if pat.getKind == ``Term.tuple then
    let items := pat[1]  -- null node: first_elem, comma, null(rest...)
    let first := extractPatNames items[0]
    let rest := extractRestNames items[2].getArgs.toList
    first ++ rest
  else if pat.getKind == ``Term.anonymousCtor then
    -- ⟨a, b, ...⟩ — items at [1], same comma-separated layout
    extractRestNames pat[1].getArgs.toList
  else if pat.isIdent then
    [pat.getId]
  else
    [`_]
where
  extractRestNames : List Syntax → List Name
    | [] => []
    | [x] => extractPatNames x
    | x :: _comma :: rest => extractPatNames x ++ extractRestNames rest

/-- For a single-constructor inductive (not Prod), return its constructor name
    and the field types instantiated with the type's parameters.
    Returns `none` if the type is `Prod` or not a single-constructor inductive. -/
def getCtorFieldTypes (ty : Expr) : MetaM (Option (Name × List Expr)) := do
  let ty ← whnf ty
  -- Don't handle Prod — that uses the existing decompose/uncurry path
  if ty.isAppOf ``Prod then return none
  let some indName := ty.getAppFn.constName? | return none
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? indName | return none
  let [ctorName] := indVal.ctors | return none
  -- Get the constructor type with proper universe levels
  let tyArgs := ty.getAppArgs
  let lvls := ty.getAppFn.constLevels!
  let ctorType ← inferType (mkConst ctorName lvls)
  -- Skip the inductive parameters (they're already applied in `ty`)
  let mut remaining := ctorType
  for i in [:indVal.numParams] do
    let .forallE _ _ body _ := remaining
      | return none
    remaining := body.instantiate1 tyArgs[i]!
  -- Collect field types
  let mut fieldTypes : List Expr := []
  let mut rem := remaining
  while true do
    match rem with
    | .forallE _ fieldTy body _ =>
      fieldTypes := fieldTypes ++ [fieldTy]
      -- Use a fresh metavar for potential dependent types
      rem := body.instantiate1 (← mkFreshExprMVar fieldTy)
    | _ => break
  return some (ctorName, fieldTypes)

/-- Build a `T.casesOn discr (fun field₁ ... fieldₙ => body)` application. -/
def mkCasesOn (ty : Expr) (indName : Name) (discr : Expr)
    (minor : Expr) (resultType : Expr) : MetaM Expr := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? indName | throwError "not an inductive: {indName}"
  let casesOnName := mkCasesOnName indName
  let lvls := ty.getAppFn.constLevels!
  -- casesOn universe levels: result universe first, then inductive's levels
  let resultSort ← inferType resultType >>= whnf
  let resultLevel := resultSort.sortLevel!
  let casesOnLvls := resultLevel :: lvls
  let casesOn := Lean.mkConst casesOnName casesOnLvls
  -- Apply: @T.casesOn.{u, ...} params (motive := fun _ => resultType) discr minor
  let tyArgs := ty.getAppArgs
  let mut result := casesOn
  -- Apply inductive parameters
  for i in [:indVal.numParams] do
    result := mkApp result tyArgs[i]!
  -- Apply motive (non-dependent: fun _ => resultType)
  let motive ← mkLambdaFVars #[] (← Meta.withLocalDeclD `_ ty fun _ => pure resultType)
  let motive := Expr.lam `_ ty resultType .default
  result := mkApp result motive
  -- Apply discriminant
  result := mkApp result discr
  -- Apply minor premise (the curried lambda)
  result := mkApp result minor
  return result

partial def decomposeProductType (ty : Expr) (n : Nat) : MetaM (List Expr) := do
  if n ≤ 1 then return [ty]
  let ty ← whnf ty
  match ty.app2? ``Prod with
  | some (α, β) => return α :: (← decomposeProductType β (n - 1))
  | none => throwError "expected a product type, got{indentExpr ty}"

def mkUncurries (innerLam : Expr) (types : List Expr) : MetaM Expr := do
  match types with
  | [] | [_] => return innerLam
  | [_, _] => mkAppM ``Function.uncurry #[innerLam]
  | _ :: rest =>
    match innerLam with
    | Expr.lam name ty body bi =>
      let wrappedBody ← mkUncurries body rest
      let newLam := Expr.lam name ty wrappedBody bi
      mkAppM ``Function.uncurry #[newLam]
    | _ => throwError "mkUncurries: expected lambda, got{indentExpr innerLam}"

/-! ## Individual `doElem` handlers-/
mutual

/-- Dispatch a single `doElem` to the appropriate handler -/
partial def elabDoElem (elem : TSyntax `doElem) (rest : List DoElem) : ElabM Expr := do
  match elem with
  | `(doElem| let $x:ident $[: $ty?]? ← $rhs) => elabDoLetArrowId x ty? rhs rest
  | `(doElem| let $pat:term ← $rhs)  => elabDoLetArrowPat pat rhs rest
  | `(doElem| let $x:ident $[: $ty?]? := $rhs) => elabDoLetId x ty? rhs rest
  | `(doElem| let $pat:term := $rhs)  => elabDoLetPat pat rhs rest
  | `(doElem| if $cond then $thenSeq else $elseSeq) => elabDoIf cond ⟨thenSeq⟩ ⟨elseSeq⟩ rest
  | `(doElem| $expr:term)            => elabDoExpr expr rest
  | `(doElem| match $[(generalizing := $_gen?)]? $(_motive?)? $_discrs,* with $_alts:matchAlt*) =>
    elabDoMatch elem.raw rest
  | _ =>
    -- Handle doNested: unwrap and elaborate the inner doSeq with rest appended
    if elem.raw.isOfKind ``Term.doNested then
      let innerElems ← getDoElems ⟨elem.raw[1]⟩
      elabDoSeqCore (innerElems ++ rest)
    -- Handle doIf with else-if chains: recursively decompose into nested if/then/else
    else if elem.raw.isOfKind ``Term.doIf then
      elabDoIfNode elem.raw rest
    else
      throwError "unsupported `do` element (kind: {elem.raw.getKind}){indentD elem}"

/-- Elaborate a `Term.doIf` node, handling `else if` chains by extracting
    the condition and branches and delegating to `elabDoIf`.
    doIf structure: [0]="if" [1]=doIfCond [2]="then" [3]=doSeq
                    [4]=many(elseIf groups) [5]=optional("else" doSeq) -/
partial def elabDoIfNode (stx : Syntax) (rest : List DoElem) : ElabM Expr := do
  -- Extract the condition from doIfCond (doIfProp: optional(ident ":") term)
  let doIfCond := stx[1]
  -- doIfCond is either doIfProp or doIfLet; for now handle doIfProp
  -- doIfProp: [0]=optional(ident ":") [1]=term
  let cond := if doIfCond.isOfKind ``Term.doIfProp then doIfCond[1]
              else doIfCond  -- fallback
  let thenSeq : TSyntax ``doSeq := ⟨stx[3]⟩
  let elseIfAlts := stx[4]  -- many node: array of else-if groups
  let elseOpt := stx[5]     -- optional node: "else" doSeq
  if elseIfAlts.getNumArgs > 0 then
    -- There are else-if chains. Build a nested doIf for the remaining chain
    -- and elaborate it as the else branch.
    -- Each else-if group: [0]="else if" [1]=doIfCond [2]="then" [3]=doSeq
    let firstElseIf := elseIfAlts[0]!
    let remainingElseIfs := elseIfAlts.getArgs[1:]
    -- Build a new doIf node for the rest of the chain
    let innerDoIf := Syntax.node .none ``Term.doIf #[
      mkAtom "if",             -- [0]
      firstElseIf[1]!,         -- [1] doIfCond
      mkAtom "then",           -- [2]
      firstElseIf[3]!,         -- [3] doSeq
      Syntax.node .none nullKind remainingElseIfs, -- [4] remaining else-ifs
      elseOpt                  -- [5] final else
    ]
    -- Elaborate: if cond then thenBranch++rest else (elabDoIfNode innerDoIf rest)
    -- We reuse elabDoIf's approach: build syntax for both branches
    let mkDoSeqSyntax (elems : List DoElem) : Syntax :=
      let doSeqItems := elems.map fun elem =>
        Syntax.node .none ``Term.doSeqItem #[elem.raw, mkNullNode #[]]
      let doSeq := Syntax.node .none ``Term.doSeqIndent #[mkNullNode doSeqItems.toArray]
      Syntax.node .none ``Term.do #[mkAtom "do", doSeq]
    let thenTerm := mkDoSeqSyntax ((← getDoElems thenSeq) ++ rest)
    -- For the else branch: wrap the inner doIf + rest in a do block
    let innerDoIfElem : TSyntax `doElem := ⟨innerDoIf⟩
    let elseTerm := mkDoSeqSyntax (innerDoIfElem :: rest)
    let condTerm : Term := ⟨cond⟩
    let ifStx ← `(if $condTerm then $(⟨thenTerm⟩) else $(⟨elseTerm⟩))
    let ctx ← read
    let expectedType ← ElabM.mkMonadicType ctx.expectedAlpha
    elabTermEnsuringType ifStx expectedType
  else if elseOpt.getNumArgs > 0 then
    -- Simple if/else (no else-if chains)
    let elseSeq : TSyntax ``doSeq := ⟨elseOpt[1]!⟩
    elabDoIf cond thenSeq elseSeq rest
  else
    throwError "doIf without else clause is not supported in this do-elaborator"

/- Elaborate a term in a `doSeq` position -/
partial def elabDoExpr (term : Syntax) (rest : List DoElem) : ElabM Expr := do
  match rest with
  | [] => do
    -- Terminal: elaborate as the monadic return value using the expected type
    let ctx ← read
    let expectedType ← ElabM.mkMonadicType ctx.expectedAlpha
    elabTermEnsuringType term expectedType
  | _ =>
    -- Non-terminal: elaborate as `m PUnit`, then `Bind.bind e (fun _ => rest)`
    let unitType ← mkConstWithFreshMVarLevels ``Unit
    let expectedType ← ElabM.mkMonadicType unitType
    let e ← elabTermEnsuringType term expectedType
    ElabM.withLocalDeclD `_ unitType fun fvar => do
      let restExpr ← elabDoSeqCore rest
      let body ← mkLambdaFVars #[fvar] restExpr
      ElabM.mkBind e body

/-- Elaborate a let-arrow with a simple identifier (`let x ← e`) -/
partial def elabDoLetArrowId (x : Ident) (ty? : Option Term) (rhs : DoElem)
    (rest : List DoElem) : ElabM Expr := do
  let name := x.getId
  let ty ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType ty
  let e ← withReader (fun ctx => { ctx with expectedAlpha := ty }) do
    match rhs with
    | `(doElem| do $seq:doSeq) =>
      let elems ← getDoElems seq
      elabDoSeqCore elems
    | `(doElem| $expr:term) =>
      elabTermEnsuringType expr expectedType
    | _ => do
      -- The RHS is a do-element like doIf or doMatch — elaborate it as a singleton seq.
      let e ← elabDoElem rhs []
      let eType ← instantiateMVars (← inferType e)
      if let some α := eType.getAppArgs[0]? then
        discard <| isDefEq ty α
      pure e
  let ty ← instantiateMVars ty
  ElabM.withLocalDeclD name ty fun fvar => do
    let restExpr ← elabDoSeqCore rest
    let body ← mkLambdaFVars #[fvar] restExpr
    ElabM.mkBind e body

/-- Elaborate a monadic let-arrow with a pattern (`let (a, b) ← e`) -/
partial def elabDoLetArrowPat (pat : Syntax) (rhs : Syntax) (rest : List DoElem) : ElabM Expr := do
  let names := extractPatNames pat
  let α ← mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType α
  let e ← withReader (fun ctx => { ctx with expectedAlpha := α }) do
    match rhs.getKind with
    | ``Parser.Term.doNested =>
      let elems ← getDoElems ⟨rhs[1]⟩
      elabDoSeqCore elems
    | ``Parser.Term.doExpr =>
      elabTermEnsuringType rhs[0] expectedType
    | _ => do
      let e ← elabDoElem ⟨rhs⟩ []
      let eType ← instantiateMVars (← inferType e)
      if let some a := eType.getAppArgs[0]? then
        discard <| isDefEq α a
      pure e
  let α ← instantiateMVars α
  -- Check if this is an anonymous constructor pattern on a non-Prod inductive
  let useCtorPath ← if pat.getKind == ``Term.anonymousCtor then
    match ← getCtorFieldTypes α with
    | some _ => pure true
    | none => pure false
  else pure false
  if useCtorPath then
    let some (_, fieldTypes) ← getCtorFieldTypes α | unreachable!
    -- Non-Prod single-constructor inductive: use casesOn inside a lambda for mkBind
    let curried ← buildCurriedLambda names fieldTypes (elabDoSeqCore rest)
    synthesizeSyntheticMVarsNoPostponing
    let restType ← do
      let mut ty ← inferType curried
      for ft in fieldTypes do
        match ty with
        | .forallE _ _ body _ => ty := body.instantiate1 (← mkFreshExprMVar ft)
        | _ => break
      pure ty
    let indName := α.getAppFn.constName!
    -- Build k = fun (x : α) => T.casesOn x (fun fields... => rest)
    ElabM.withLocalDeclD `_x α fun xFvar => do
      let body ← mkCasesOn α indName xFvar curried restType
      let k ← mkLambdaFVars #[xFvar] body
      ElabM.mkBind e k
  else
    -- Default Prod path
    let compTypes ← decomposeProductType α names.length
    let curried ← buildCurriedLambda names compTypes (elabDoSeqCore rest)
    synthesizeSyntheticMVarsNoPostponing
    let k ← mkUncurries curried compTypes
    ElabM.mkBind e k

/-- Elaborate a pure let binding (`let x := e`) -/
partial def elabDoLetId (x : TSyntax `ident) (ty? : Option Syntax) (rhs : Syntax)
    (rest : List (TSyntax `doElem)) : ElabM Expr := do
  let name := x.getId
  let α ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  ElabM.withLetDecl name α val fun fvar => do
    let restExpr ← elabDoSeqCore rest
    mkLetFVars #[fvar] restExpr

/-- Elaborate a pure let binding with a pattern (`let (a, b) := e`) -/
partial def elabDoLetPat (pat : Syntax) (rhs : Syntax)
    (rest : List (TSyntax `doElem)) : ElabM Expr := do
  let names := extractPatNames pat
  let α ← mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  -- Check if this is an anonymous constructor pattern on a non-Prod inductive
  if pat.getKind == ``Term.anonymousCtor then
    if let some (_, fieldTypes) ← getCtorFieldTypes α then
      -- Non-Prod single-constructor inductive: use casesOn
      let curried ← buildCurriedLambda names fieldTypes (elabDoSeqCore rest)
      synthesizeSyntheticMVarsNoPostponing
      let resultType ← inferType (← ElabM.mkMonadicType (← mkFreshTypeMVar))
      let indName := α.getAppFn.constName!
      let result ← mkCasesOn α indName val curried (← inferType curried >>= fun t => do
        -- Get the actual result type by applying the curried lambda to dummy args
        let mut ty := t
        for ft in fieldTypes do
          match ty with
          | .forallE _ _ body _ => ty := body.instantiate1 (← mkFreshExprMVar ft)
          | _ => break
        return ty)
      return result
  -- Default Prod path
  let compTypes ← decomposeProductType α names.length
  let curried ← buildCurriedLambda names compTypes (elabDoSeqCore rest)
  synthesizeSyntheticMVarsNoPostponing
  let k ← mkUncurries curried compTypes
  return Expr.app k val

/-- Elaborate an if-then-else.
    Appends `rest` to both branches, wraps them in `do` blocks, and constructs a
    term-level `if/then/else` syntax that is delegated to `elabTerm`. This lets Lean's
    standard `if` elaborator handle Bool vs Prop dispatch and Decidable synthesis. -/
partial def elabDoIf (cond : Syntax) (thenSeq elseSeq : TSyntax ``doSeq)
    (rest : List (TSyntax `doElem)) : ElabM Expr := do
  let mkDoSeqSyntax (elems : List DoElem) : Syntax :=
    let doSeqItems := elems.map fun elem =>
      Syntax.node .none ``Term.doSeqItem #[elem.raw, mkNullNode #[]]
    let doSeq := Syntax.node .none ``Term.doSeqIndent #[mkNullNode doSeqItems.toArray]
    Syntax.node .none ``Term.do #[mkAtom "do", doSeq]
  -- Append rest to both branches and wrap in `do`
  let thenTerm := mkDoSeqSyntax ((← getDoElems thenSeq) ++ rest)
  let elseTerm := mkDoSeqSyntax ((← getDoElems elseSeq) ++ rest)
  -- Build `if cond then do ... else do ...` and let elabTerm handle it
  let cond : Term := ⟨cond⟩
  let ifStx ← `(if $cond then $(⟨thenTerm⟩) else $(⟨elseTerm⟩))
  let ctx ← read
  let expectedType ← ElabM.mkMonadicType ctx.expectedAlpha
  elabTermEnsuringType ifStx expectedType

/-- Elaborate a pattern match (`doMatch`) -/
partial def elabDoMatch (stx : Syntax) (rest : List (TSyntax `doElem)) : ElabM Expr := do
  -- doMatch: [0]="match", [1]=opt name, [2]=opt gen, [3]=discrs, [4]="with", [5]=matchAlts
  let alts := stx[5][0]  
  let mut newAlts := #[]
  for i in [:alts.getNumArgs] do
    let alt := alts[i]
    let armDoSeq : TSyntax ``Term.doSeq := ⟨alt[3]⟩
    let armElems ← getDoElems armDoSeq
    let allElems := armElems ++ rest
    -- Build doSeqItems from the elements
    let doSeqItems := allElems.map fun elem =>
      Syntax.node .none ``Term.doSeqItem #[elem.raw, mkNullNode #[]]
    let newDoSeq := Syntax.node .none ``Term.doSeqIndent #[mkNullNode doSeqItems.toArray]
    let doTerm := Syntax.node .none ``Term.do #[mkAtom "do", newDoSeq]
    -- Replace the arm body with the `do` term
    let newAlt := alt.setArg 3 doTerm
    newAlts := newAlts.push newAlt
  -- Rebuild the match as a term-level match
  let newAltsNode := Syntax.node .none ``Term.matchAlts #[mkNullNode newAlts]
  let termMatch := Syntax.node .none ``Term.match
    #[stx[0], stx[1], stx[2], stx[3], stx[4], newAltsNode]
  -- Elaborate as a term
  let ctx ← read
  let expectedType ← ElabM.mkMonadicType ctx.expectedAlpha
  elabTermEnsuringType termMatch expectedType

partial def elabDoSeqCore : List (TSyntax `doElem) → ElabM Expr
  | [] => throwError "unexpected empty `do` block"
  | elem :: rest => elabDoElem elem rest

end

def elabDoSeq (doSeq : TSyntax ``doSeq) : ElabM Expr :=
  getDoElems doSeq >>= fun elems => elabDoSeqCore elems


/--
TODO: Add doc
-/
@[term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  let useNewElab ← do
    let some expectedType := expectedType? | pure false
    let expectedType ← instantiateMVars =<< whnf expectedType
    match_expr expectedType with
    | Aeneas.Std.Result _ => pure (Aeneas.newDoElab.get (← getOptions))
    | _ => pure false
  if useNewElab then
    -- logInfo  m!"Using new do elaborator"
    let `(do $doSeq) := stx | throwUnsupportedSyntax
    Do.ElabM.execute (Do.elabDoSeq doSeq) expectedType?.get!
  else
    -- logWarning m!"Using old do elaborator"
    Term.elabDo stx expectedType?

end Do
end Aeneas

section tests

open Aeneas Std Result ControlFlow Error

set_option pp.notation false

def test1 : Result Nat := do
  ok 42
/--
info: def test1 : Result Nat :=
ok 42
-/
#guard_msgs in
#print test1

def test2 : Result Nat := do
  let x ← ok 1
  ok x
/--
info: def test2 : Result Nat :=
Bind.bind (ok 1) fun x => ok x
-/
#guard_msgs in
#print test2

def test3 : Result Nat := do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)
/--
info: def test3 : Result Nat :=
Bind.bind (ok 1) fun x => Bind.bind (ok 2) fun y => ok (HAdd.hAdd x y)
-/
#guard_msgs in
#print test3

def test4 : Result Nat := do
  let x : Nat ← ok 1
  ok (x + 1)
/--
info: def test4 : Result Nat :=
Bind.bind (ok 1) fun x => ok (HAdd.hAdd x 1)
-/
#guard_msgs in
#print test4

def test5 : Result Nat := do
  let x := 1
  ok (x + 2)
/--
info: def test5 : Result Nat :=
have x := 1;
ok (HAdd.hAdd x 2)
-/
#guard_msgs in
#print test5

def test6 : Result Nat := do
  let x : Nat := 1
  let y ← ok 2
  ok (x + y)
/--
info: def test6 : Result Nat :=
have x := 1;
Bind.bind (ok 2) fun y => ok (HAdd.hAdd x y)
-/
#guard_msgs in
#print test6

def test7 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok x else ok 0
/--
info: def test7 : Result Nat :=
Bind.bind (ok 1) fun x => ite (GT.gt x 0) (ok x) (ok 0)
-/
#guard_msgs in
#print test7

def test8 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20
/--
info: def test8 : Result Nat :=
Bind.bind (ok 1) fun x => ite (GT.gt x 0) (ok 10) (ok 20)
-/
#guard_msgs in
#print test8

def test9 : Result Nat := do
  let x ← ok 2
  let y ← do
    if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test9 : Result Nat :=
Bind.bind (ok 2) fun x => Bind.bind (ite (GT.gt x 1) (ok 1) (ok 0)) fun y => ok y
-/
#guard_msgs in
#print test9

def test10 : Result Nat := do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test10 : Result Nat :=
Bind.bind (ok 2) fun x => Bind.bind (ite (GT.gt x 1) (ok 1) (ok 0)) fun y => ok y
-/
#guard_msgs in
#print test10

def test11_body (max i : Nat) : Result (ControlFlow Nat Nat) :=
  if i < max then ok (ControlFlow.cont (i + 1))
  else ok (ControlFlow.done i)

def test11 : Result Nat := do
  let max ← ok 10
  loop (test11_body max) 0
/--
info: def test11 : Result Nat :=
Bind.bind (ok 10) fun max => loop (test11_body max) 0
-/
#guard_msgs in
#print test11

def test12 : Result Nat := do
  let (a, b) ← ok (1, 2)
  ok (a + b)
/--
info: def test12 : Result Nat :=
Bind.bind (ok (Prod.mk 1 2)) (Function.uncurry fun a b => ok (HAdd.hAdd a b))
-/
#guard_msgs in
#print test12

def test13 : Result Nat := do
  let (_, b) ← ok (1, 2)
  ok b
/--
info: def test13 : Result Nat :=
Bind.bind (ok (Prod.mk 1 2)) (Function.uncurry fun _ b => ok b)
-/
#guard_msgs in
#print test13

def test14 : Result Nat := do
  let (a, b) := (1, 2)
  ok (a + b)
/--
info: def test14 : Result Nat :=
Function.uncurry (fun a b => ok (HAdd.hAdd a b)) (Prod.mk 1 2)
-/
#guard_msgs in
#print test14

def test15 : Result Nat := do
  let x ← ok 1
  match x with
  | 0 => ok 10
  | _ => ok 20
/--
info: def test15 : Result Nat :=
Bind.bind (ok 1) fun x => test15.match_1 (fun x => Result Nat) x (fun _ => ok 10) fun x => ok 20
-/
#guard_msgs in
#print test15

def test16 : Result Nat := do
  let x ← ok 1
  let y ← match x with
    | 0 => ok 10
    | _ => ok 20
  ok (y + 1)
/--
info: def test16 : Result Nat :=
Bind.bind (ok 1) fun x =>
  Bind.bind (test15.match_1 (fun x => Result Nat) x (fun _ => ok 10) fun x => ok 20) fun y => ok (HAdd.hAdd y 1)
-/
#guard_msgs in
#print test16

def massert_test : Result Unit := do
  let s ←
    lift (Array.to_slice
      (Array.make 5#usize [ 0#u32, 1#u32, 2#u32, 3#u32, 4#u32 ]))
  let i ← core.slice.Slice.iter s
  let it ← core.slice.iter.IteratorSliceIter.step_by i 1#usize
  let (o, it1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) it
  let i1 ← core.option.Option.unwrap o
  massert (i1 = 0#u32)
  let (o1, it2) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) it1
  let i2 ← core.option.Option.unwrap o1
  massert (i2 = 1#u32)
/--
info: def massert_test : Result Unit :=
Bind.bind
  (lift
    (Array.make (Usize.ofNat 5 massert_test._proof_1)
        (List.cons (U32.ofNat 0 massert_test._proof_2)
          (List.cons (U32.ofNat 1 massert_test._proof_3)
            (List.cons (U32.ofNat 2 massert_test._proof_4)
              (List.cons (U32.ofNat 3 massert_test._proof_5)
                (List.cons (U32.ofNat 4 massert_test._proof_6) List.nil)))))
        massert_test._proof_7).to_slice)
  fun s =>
  Bind.bind (core.slice.Slice.iter s) fun i =>
    Bind.bind (core.slice.iter.IteratorSliceIter.step_by i (Usize.ofNat 1 massert_test._proof_8)) fun it =>
      Bind.bind (core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it)
        (Function.uncurry fun o it1 =>
          Bind.bind (core.option.Option.unwrap o) fun i1 =>
            Bind.bind (massert (Eq i1 (U32.ofNat 0 massert_test._proof_2))) fun _ =>
              Bind.bind
                (core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it1)
                (Function.uncurry fun o1 it2 =>
                  Bind.bind (core.option.Option.unwrap o1) fun i2 =>
                    massert (Eq i2 (U32.ofNat 1 massert_test._proof_3))))
-/
#guard_msgs in
#print massert_test

def bool_test (x : Bool) : Result Bool := do
  let b ← ok x
  if b
  then ok true
  else ok false
/--
info: def bool_test : Bool → Result Bool :=
fun x => Bind.bind (ok x) fun b => ite (Eq b true) (ok true) (ok false)
-/
#guard_msgs in
#print bool_test

opaque core.mem.drop {T : Type} : T → Result Unit

def do_nested_test (b1 : Bool) : Result Unit := do
  let _ ←
    if b1
    then ok (true, 2#u32)
    else ok (false, 0#u32)
  ok ()
/--
info: def do_nested_test : Bool → Result Unit :=
fun b1 =>
  Bind.bind
    (ite (Eq b1 true) (ok (Prod.mk true (U32.ofNat 2 massert_test._proof_4)))
      (ok (Prod.mk false (U32.ofNat 0 massert_test._proof_2))))
    fun _ => ok Unit.unit
-/
#guard_msgs in
#print do_nested_test

def if_then_add_test (b : Bool) (x : Std.U32) : Result Std.U32 := do
  let y ← if b then ok 1#u32 else ok 0#u32
  x + y
/--
info: def if_then_add_test : Bool → U32 → Result U32 :=
fun b x =>
  Bind.bind (ite (Eq b true) (ok (U32.ofNat 1 massert_test._proof_3)) (ok (U32.ofNat 0 massert_test._proof_2))) fun y =>
    HAdd.hAdd x y
-/
#guard_msgs in
#print if_then_add_test

def match_add_test (a : Std.U32) (x : Std.U32) : Result Std.U32 := do
  let y ←
    match a with
    | 0#uscalar => ok 0#u32
    | 1#uscalar => ok 1#u32
    | _ => ok 2#u32
  x + y
/--
info: def match_add_test : U32 → U32 → Result U32 :=
fun a x =>
  Bind.bind
    (match_add_test.match_1 (fun a => Result (UScalar UScalarTy.U32)) a
      (fun _ => ok (U32.ofNat 0 massert_test._proof_2)) (fun _ => ok (U32.ofNat 1 massert_test._proof_3)) fun x =>
      ok (U32.ofNat 2 massert_test._proof_4))
    fun y => HAdd.hAdd x y
-/
#guard_msgs in
#print match_add_test

structure Wrapper (T : Type) where
  x : T

def make_wrapper {T : Type} (x : T) :
  Result ((Wrapper T) × (Wrapper T → Wrapper T)) := do
  ok ({ x }, fun w => w)

def universe_test {T : Type} (w : Wrapper T) :
  Result ((Wrapper T) × (Wrapper T → Wrapper T)) := do
  let (inner, back) ← make_wrapper w.x
  let back2 := fun w1 => back { w with x := w1.x }
  ok (inner, back2)
/--
info: def universe_test : {T : Type} → Wrapper T → Result (Prod (Wrapper T) (Wrapper T → Wrapper T)) :=
fun {T} w =>
  Bind.bind (make_wrapper w.x)
    (Function.uncurry fun inner back =>
      have back2 := fun w1 => back { x := w1.x };
      ok (Prod.mk inner back2))
-/
#guard_msgs in
#print universe_test

def make_pair {T : Type} (x y : T) :
  Result (T × T × (T → List T) × (T → List T)) := do
  ok (x, y, fun t => [t], fun t => [t])

def universe_tuple_test {T : Type} (x y : T) :
  Result ((T × T) × ((T × T) → (List T × List T))) := do
  let (a, b, back, back1) ← make_pair x y
  let back2 :=
    fun p =>
      let (t1, t2) := p
      (back t1, back1 t2)
  ok ((a, b), back2)
/--
info: def universe_tuple_test : {T : Type} → T → T → Result (Prod (Prod T T) (Prod T T → Prod (List T) (List T))) :=
fun {T} x y =>
  Bind.bind (make_pair x y)
    (Function.uncurry fun a =>
      Function.uncurry fun b =>
        Function.uncurry fun back back1 =>
          have back2 := fun p =>
            universe_tuple_test.match_1 (fun p => Prod (List T) (List T)) p fun t1 t2 => Prod.mk (back t1) (back1 t2);
          ok (Prod.mk (Prod.mk a b) back2))
-/
#guard_msgs in
#print universe_tuple_test

def get_and_update (xs : alloc.vec.Vec U32) (i : Usize) :
  Result (U32 × (U32 → alloc.vec.Vec U32)) := do
  let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) xs i
  ok (x, fun _v => xs)

def mono_loop_test (xs : alloc.vec.Vec U32) (i : Usize) :
  Result (alloc.vec.Vec U32) := do
  let i1 := alloc.vec.Vec.len xs
  if i < i1
  then
    let (_, update_back) ← get_and_update xs i
    let i2 ← i + 1#usize
    let xs1 := update_back 0#u32
    mono_loop_test xs1 i2
  else ok xs
partial_fixpoint
/--
info: @[irreducible] def mono_loop_test : alloc.vec.Vec U32 → Usize → Result (alloc.vec.Vec U32) :=
Order.fix
  (fun f xs i =>
    let i1 := xs.len;
    ite (LT.lt i i1)
      (Bind.bind (get_and_update xs i)
        (Function.uncurry fun _ update_back =>
          Bind.bind (HAdd.hAdd i (Usize.ofNat 1 massert_test._proof_8)) fun i2 =>
            let xs1 := update_back (U32.ofNat 0 massert_test._proof_2);
            f xs1 i2))
      (ok xs))
  mono_loop_test._proof_1
-/
#guard_msgs in
#print mono_loop_test

def doIf_pat_test (b : Bool) : Result (Nat × Nat) := do
  let (x, y) ←
    if b then ok (1, 2) else ok (3, 4)
  ok (x, y)
/--
info: def doIf_pat_test : Bool → Result (Prod Nat Nat) :=
fun b =>
  Bind.bind (ite (Eq b true) (ok (Prod.mk 1 2)) (ok (Prod.mk 3 4))) (Function.uncurry fun x y => ok (Prod.mk x y))
-/
#guard_msgs in
#print doIf_pat_test

def match_pat_test (n : Nat) : Result (Nat × Nat) := do
  let (x, y) ←
    match n with
    | 0 => ok (1, 2)
    | _ => ok (3, 4)
  ok (x, y)
/--
info: def match_pat_test : Nat → Result (Prod Nat Nat) :=
fun n =>
  Bind.bind (test15.match_1 (fun n => Result (Prod Nat Nat)) n (fun _ => ok (Prod.mk 1 2)) fun x => ok (Prod.mk 3 4))
    (Function.uncurry fun x y => ok (Prod.mk x y))
-/
#guard_msgs in
#print match_pat_test

def else_if_test (x y : Nat) : Result Ordering := do
  if x < y
  then ok Ordering.lt
  else if x = y
  then ok Ordering.eq
  else ok Ordering.gt
/--
info: def else_if_test : Nat → Nat → Result Ordering :=
fun x y => ite (LT.lt x y) (ok Ordering.lt) (ite (Eq x y) (ok Ordering.eq) (ok Ordering.gt))
-/
#guard_msgs in
#print else_if_test

inductive Wrap where
  | mk : Nat → Wrap

def anon_ctor_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ := w
  ok (n + 1)
/--
info: def anon_ctor_test : Wrap → Result Nat :=
fun w => Wrap.casesOn w fun n => ok (HAdd.hAdd n 1)
-/
#guard_msgs in
#print anon_ctor_test

def anon_ctor_monadic_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ ← ok w
  ok (n + 1)
/--
info: def anon_ctor_monadic_test : Wrap → Result Nat :=
fun w => Bind.bind (ok w) fun _x => Wrap.casesOn _x fun n => ok (HAdd.hAdd n 1)
-/
#guard_msgs in
#print anon_ctor_monadic_test

structure ExBox (Inst : Type → Type) where
  ty : Type
  inst : Inst ty
  val : ty

structure Into2 (Self : Type) (T : Type) where
  into : Self → Result T

def exbox_lambda_test {V T W : Type}
    (inst1 : Into2 T V) (inst2 : Into2 W V)
    (b : Bool) (x : T) (y : W) :
    Result (ExBox (fun _dyn => Into2 _dyn V)) := do
  if b
  then ok (ExBox.mk _ inst1 x)
  else ok (ExBox.mk _ inst2 y)
/--
info: def exbox_lambda_test : {V T W : Type} →
  Into2 T V → Into2 W V → Bool → T → W → Result (ExBox fun _dyn => Into2 _dyn V) :=
fun {V T W} inst1 inst2 b x y =>
  ite (Eq b true) (ok { ty := T, inst := inst1, val := x }) (ok { ty := W, inst := inst2, val := y })
-/
#guard_msgs in
#print exbox_lambda_test

end tests
