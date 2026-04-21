import Lean
import Mathlib.Control.Monad.Cont
import Aeneas.Std
import Aeneas.Do.Init

open Lean Elab Parser Term Meta

instance [MonadExceptOf ε m] [Monad m] : MonadExceptOf ε (ContT r m) where
  throw e := fun _ => throw e
  tryCatch x h := fun k => tryCatch (x k) (fun e => h e k)
--
instance [MonadRef m] [Monad m] : MonadRef (ContT r m) where
  getRef := fun k => do let ref ← MonadRef.getRef; k ref
  withRef ref x := fun k => MonadRef.withRef ref (x k)
--
instance [AddErrorMessageContext m] [Monad m] : AddErrorMessageContext (ContT r m) where
  add stx msg := fun k => do let r ← AddErrorMessageContext.add stx msg; k r
--
instance [Monad m] [MonadQuotation m] : MonadQuotation (ContT r m) where
  getCurrMacroScope := fun k => do let s ← getCurrMacroScope; k s
  getContext := fun k => do let ctx ← MonadQuotation.getContext; k ctx
  withFreshMacroScope x := fun k => withFreshMacroScope (x k)

namespace Aeneas
namespace Do

/-- Monad info cached from the `do` block's expected type `m α`. -/
structure Context where
  m : Expr
  /-- The element type `α`. -/
  expectedAlpha : Expr
  bindInst : Expr
  pureInst : Expr

abbrev ElabM := ReaderT Context $ ContT Expr TermElabM

/-- Split `m α` and synthesize the `Bind m` and `Pure m` instances. -/
def mkContext (expectedType : Expr) : TermElabM Context := do
  let expectedType ← whnf expectedType
  let (m, α) ← match expectedType with
    | Expr.app m α => pure (m, α)
    | _ => throwError "expected a monadic type `m α`, got {indentExpr expectedType}"
  let bindInst ← synthInstance (← mkAppM ``Bind #[m])
  let pureInst ← synthInstance (← mkAppM ``Pure #[m])
  return { m, expectedAlpha := α, bindInst, pureInst }

def ElabM.mkBind (e k : Expr) : ElabM Expr := do
  let ctx ← read
  mkAppOptM ``Bind.bind #[some ctx.m, some ctx.bindInst, none, none, some e, some k]

/-- Build `m α`. -/
def ElabM.mkMonadicType (α : Expr) : ElabM Expr := read >>= fun ctx => pure (mkApp ctx.m α)

/-- Run an `ElabM` against the given `do` block expected type. -/
def ElabM.execute (x : ElabM Expr) (expectedType : Expr) : TermElabM Expr := do
  let ctx ← mkContext expectedType
  (x.run ctx).run pure

/-- `Meta.withLocalDeclD` lifted to `ElabM`. -/
def ElabM.withLocalDeclD (name : Name) (type : Expr) (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLocalDeclD name type fun fvar =>
      (body fvar).run ctx |>.run k

/-- `Meta.withLetDecl` lifted to `ElabM`. -/
def ElabM.withLetDecl (name : Name) (type : Expr) (value : Expr)
    (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLetDecl name type value fun fvar =>
      (body fvar).run ctx |>.run k

/-- Fill a match arm's `?m` by elaborating `body` under the arm's pattern binders
    and assigning the abstracted result to the mvar. -/
def ElabM.assignArmMVar (arm : Expr) (body : ElabM Expr) : ElabM Unit := do
  let ctx ← read
  fun _ k =>
    Meta.lambdaTelescope arm fun fvars ebody => do
      let .mvar mvarId := ebody.getAppFn
        | throwError "elabDoMatch: expected metavariable arm body, got{indentExpr ebody}"
      let armExpr ← (body.run ctx).run pure
      let value ←
        if ebody.isMVar then
          let usedFVars := fvars.filter (armExpr.occurs ·)
          if usedFVars.isEmpty then pure armExpr
          else mkLambdaFVars usedFVars armExpr
        else
          mkLambdaFVars fvars armExpr
      mvarId.assign value
      k ()


/-- For a single-constructor inductive (other than `Prod`), return the constructor
    name and field types instantiated at the type's parameters. `none` otherwise. -/
def getCtorFieldTypes (ty : Expr) : MetaM (Option (Name × List Expr)) := do
  let ty ← whnf ty
  -- Prod has its own decompose/uncurry path
  if ty.isAppOf ``Prod then return none
  let some indName := ty.getAppFn.constName? | return none
  let indVal ← getConstInfoInduct indName
  let [ctorName] := indVal.ctors | return none
  let lvls := ty.getAppFn.constLevels!
  let params := ty.getAppArgs.extract 0 indVal.numParams
  let ctorType ← inferType (mkAppN (mkConst ctorName lvls) params)
  forallTelescopeReducing ctorType fun fields _ => do
    let fieldTypes ← fields.toList.mapM (·.fvarId!.getType)
    return some (ctorName, fieldTypes)

/-- Build `T.casesOn discr minor` with a non-dependent motive `fun _ : ty => resultType`. -/
def mkCasesOn (ty : Expr) (indName : Name) (discr : Expr)
    (minor : Expr) (resultType : Expr) : MetaM Expr := do
  let indVal ← getConstInfoInduct indName
  -- `casesOn`'s first universe is the motive's; the rest are the inductive's.
  let casesOnLvls := (← getLevel resultType) :: ty.getAppFn.constLevels!
  let casesOn := Lean.mkConst (mkCasesOnName indName) casesOnLvls
  let params := ty.getAppArgs.extract 0 indVal.numParams
  let motive ← withLocalDeclD `_ ty fun x => mkLambdaFVars #[x] resultType
  return mkAppN casesOn (params ++ #[motive, discr, minor])

partial def decomposeProductType (ty : Expr) (n : Nat) : MetaM (List Expr) := do
  if n ≤ 1 then return [ty]
  let ty ← whnf ty
  match_expr ty with
  | Prod α β => return α :: (← decomposeProductType β (n - 1))
  | _ => throwError "expected a product type, got{indentExpr ty}"

partial def mkUncurries (innerLam : Expr) (types : List Expr) : MetaM Expr := do
  match types with
  | [] | [_] => return innerLam
  | [_, _] => mkAppM ``Function.uncurry #[innerLam]
  | _ :: rest =>
    lambdaBoundedTelescope innerLam 1 fun fvars body => do
      let wrappedBody ← mkUncurries body rest
      let newLam ← mkLambdaFVars fvars wrappedBody
      mkAppM ``Function.uncurry #[newLam]

/-! ## Pattern analysis and continuation building -/

inductive PatShape where
  | leaf (name : Name)
  | prod (subs : Array PatShape)
  | ctor (indName : Name) (subs : Array PatShape)
  deriving Inhabited

/-- Walk `pat` alongside its expected `ty`, producing a `PatShape`. -/
partial def analyzePat (pat : Term) (ty : Expr) : ElabM PatShape := do
  let analyzeSubs (subPats : Array Term) (subTypes : List Expr) : ElabM (Array PatShape) :=
    subPats.toList.zip subTypes |>.toArray.mapM fun (p, t) => analyzePat p t
  match pat with
  | `(_) => return .leaf `_
  | `($id:ident) => return .leaf id.getId
  | `(($x, $xs,*)) =>
    let subPats : Array Term := #[x] ++ xs.getElems
    let subTypes ← decomposeProductType ty subPats.size
    return .prod (← analyzeSubs subPats subTypes)
  | `(⟨$xs,*⟩) =>
    let subPats : Array Term := xs.getElems
    let ty ← whnf ty
    if ty.isAppOf ``Prod then
      let subTypes ← decomposeProductType ty subPats.size
      return .prod (← analyzeSubs subPats subTypes)
    else
      match ← getCtorFieldTypes ty with
      | some (_, fieldTypes) =>
        let some indName := ty.getAppFn.constName?
          | throwError "analyzePat: cannot determine inductive name for{indentExpr ty}"
        return .ctor indName (← analyzeSubs subPats fieldTypes)
      | none => throwError "analyzePat: unsupported anonymous-ctor pattern on type{indentExpr ty}"
  | _ =>
    throwError "analyzePat: unsupported pattern kind `{pat.raw.getKind}`{indentD pat}"

/-- Result type of a `casesOn` whose minor is `curried : f₁ → … → fₙ → ρ`. -/
def computeCasesOnResultType (curried : Expr) (fieldTypes : List Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType curried) fieldTypes.length fun _ body => return body

mutual

/-- Build a curried lambda `fun x₁ … xₙ => body [x₁, …, xₙ]`, one fvar per sub-pattern. -/
partial def mkCurriedLambda (subs : List PatShape) (types : List Expr)
    (body : Array Expr → ElabM Expr) (idx : Nat := 0) : ElabM Expr := do
  match subs, types with
  | [], _ | _, [] => body #[]
  | sub :: restSubs, ty :: restTypes =>
    let n := match sub with
      | .leaf n => n
      | _ => Name.mkSimple s!"_x{idx}"
    ElabM.withLocalDeclD n ty fun fv => do
      let innerBody ← mkCurriedLambda restSubs restTypes
        (fun fs => body (#[fv] ++ fs)) (idx + 1)
      mkLambdaFVars #[fv] innerBody

/-- Recursively unpack each `fv` per its `sub`, calling `body` with the collected leaves. -/
partial def unpackAll (subs : List PatShape) (fvs : List Expr) (types : List Expr)
    (body : Array Expr → ElabM Expr) : ElabM Expr := do
  match subs, fvs, types with
  | [], _, _ | _, [], _ | _, _, [] => body #[]
  | sub :: restSubs, fv :: restFvs, ty :: restTypes =>
    unpackFvar sub fv ty fun extra =>
      unpackAll restSubs restFvs restTypes fun more => body (extra ++ more)

/-- Unpack `fv : ty` per `sub`, calling `body` with the leaves. Emits
    `Function.uncurry` for `.prod` and `T.casesOn` for `.ctor`. -/
partial def unpackFvar (sub : PatShape) (fv : Expr) (ty : Expr)
    (body : Array Expr → ElabM Expr) : ElabM Expr := do
  match sub with
  | .leaf _ => body #[fv]
  | .prod subs =>
    let subTypes ← decomposeProductType ty subs.size
    let minor ← mkCurriedLambda subs.toList subTypes fun outerFvs =>
      unpackAll subs.toList outerFvs.toList subTypes body
    let uncurried ← mkUncurries minor subTypes
    return mkApp uncurried fv
  | .ctor indName subs =>
    let some (_, fieldTypes) ← getCtorFieldTypes ty
      | throwError "unpackFvar: expected single-ctor inductive, got{indentExpr ty}"
    let minor ← mkCurriedLambda subs.toList fieldTypes fun outerFvs =>
      unpackAll subs.toList outerFvs.toList fieldTypes body
    let resultType ← computeCasesOnResultType minor fieldTypes
    mkCasesOn ty indName fv minor resultType

end

/-- Build a continuation `k : ty → ρ` that destructures its argument per `shape`
    and calls `body` with the leaf fvars. -/
partial def mkPatContinuation (shape : PatShape) (ty : Expr)
    (body : Array Expr → ElabM Expr) : ElabM Expr := do
  match shape with
  | .leaf n =>
    ElabM.withLocalDeclD n ty fun fv => do
      mkLambdaFVars #[fv] (← body #[fv])
  | .prod subs =>
    let subTypes ← decomposeProductType ty subs.size
    let minor ← mkCurriedLambda subs.toList subTypes fun outerFvs =>
      unpackAll subs.toList outerFvs.toList subTypes body
    mkUncurries minor subTypes
  | .ctor indName subs =>
    ElabM.withLocalDeclD `_x ty fun xFv => do
      let some (_, fieldTypes) ← getCtorFieldTypes ty
        | throwError "mkPatContinuation: expected single-ctor inductive, got{indentExpr ty}"
      let minor ← mkCurriedLambda subs.toList fieldTypes fun outerFvs =>
        unpackAll subs.toList outerFvs.toList fieldTypes body
      let resultType ← computeCasesOnResultType minor fieldTypes
      let casesExpr ← mkCasesOn ty indName xFv minor resultType
      mkLambdaFVars #[xFv] casesExpr

/-! ## If-then-else construction helpers -/

/-- Elaborate `cond`, returning a `Prop`. `Bool` is coerced to `cond = true`.
    Synthetic mvars are forced so `Decidable` can be inferred downstream. -/
def elabIfCondition (cond : Term) : ElabM Expr := do
  let condExpr ← Lean.Elab.Term.elabTerm cond none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let condExpr ← instantiateMVars condExpr
  let condType ← whnf (← instantiateMVars (← inferType condExpr))
  if condType.isConstOf ``Bool then
    mkEq condExpr (mkConst ``Bool.true)
  else
    pure condExpr

/-- Build `ite propExpr thn els`, synthesizing the `Decidable` instance. -/
def mkIteExpr (propExpr thn els : Expr) : MetaM Expr := do
  mkAppOptM ``ite #[none, some propExpr, none, some thn, some els]

/-! ## Individual `doElem` handlers-/

abbrev DoElem := TSyntax `doElem

def getDoElems (doSeq : TSyntax ``doSeq) : ElabM (List DoElem) := do
  match doSeq with
  | `(doSeq| $[$elems $[;]?]*) => return elems.toList
  | _ => throwError "unexpected `doSeq` syntax {indentD doSeq}"

mutual

/-- Dispatch a `doElem` to its handler. -/
partial def elabDoElem (elem : TSyntax `doElem) (rest : List DoElem) : ElabM Expr := do
  match elem with
  | `(doElem| let $x:ident $[: $ty?]? ← $rhs) => elabDoLetArrowId x ty? rhs rest
  | `(doElem| let $pat:term ← $rhs)  => elabDoLetArrowPat pat rhs rest
  | `(doElem| let $x:ident $[: $ty?]? := $rhs) => elabDoLetId x ty? rhs rest
  | `(doElem| let $pat:term := $rhs)  => elabDoLetPat pat rhs rest
  | `(doElem| if $cond:term then $thenSeq:doSeq
              $[else if $econds:term then $eseqs:doSeq]*
              else $elseSeq:doSeq) =>
    let branches : Array (Term × TSyntax ``doSeq) :=
      #[(cond, thenSeq)] ++ econds.zip eseqs
    elabDoIfChain branches elseSeq rest
  | `(doElem| $expr:term)            => elabDoExpr expr rest
  | `(doElem| match $[(generalizing := $gen?)]? $[$motive?:motive]? $discrs,* with $alts:matchAlt*) =>
    elabDoMatch gen? motive? discrs alts rest
  | `(doElem| do $seq:doSeq) =>
    let innerElems ← getDoElems seq
    elabDoSeqCore (innerElems ++ rest)
  | _ =>
    throwError "unsupported `do` element (kind: {elem.raw.getKind}){indentD elem}"

/-- Elaborate a monadic sub-term. If `rest` is empty, use the block's expected
    type `m α`; otherwise elaborate at `m Unit` and bind `rest` onto it. -/
partial def elabMonadicAsDoElem
    (elabAtType : Expr → ElabM Expr) (rest : List DoElem) : ElabM Expr := do
  match rest with
  | [] =>
    let ctx ← read
    let expectedType ← ElabM.mkMonadicType ctx.expectedAlpha
    elabAtType expectedType
  | _ =>
    let unitType ← mkConstWithFreshMVarLevels ``Unit
    ElabM.withLocalDeclD `_ unitType fun fvar => do
      let restExpr ← elabDoSeqCore rest
      let body ← mkLambdaFVars #[fvar] restExpr
      let expectedType ← ElabM.mkMonadicType unitType
      let e ← elabAtType expectedType
      ElabM.mkBind e body

/-- Elaborate a term in a `doSeq` position. -/
partial def elabDoExpr (term : Term) (rest : List DoElem) : ElabM Expr :=
  elabMonadicAsDoElem (fun ty => elabTermEnsuringType term ty) rest

/-- Elaborate `let x ← e`. -/
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
      -- RHS is a do-element (e.g. `if`, `match`): elaborate as a singleton seq.
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

/-- Elaborate `let pat ← e`. -/
partial def elabDoLetArrowPat (pat : Term) (rhs : DoElem) (rest : List DoElem) : ElabM Expr := do
  let α ← mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType α
  let e ← withReader (fun ctx => { ctx with expectedAlpha := α }) do
    match rhs with
    | `(doElem| do $seq:doSeq) =>
      let elems ← getDoElems seq
      elabDoSeqCore elems
    | `(doElem| $expr:term) =>
      elabTermEnsuringType expr expectedType
    | _ => do
      let e ← elabDoElem rhs []
      let eType ← instantiateMVars (← inferType e)
      if let some a := eType.getAppArgs[0]? then
        discard <| isDefEq α a
      pure e
  let α ← instantiateMVars α
  let shape ← analyzePat pat α
  let k ← mkPatContinuation shape α fun _ => elabDoSeqCore rest
  synthesizeSyntheticMVarsNoPostponing
  ElabM.mkBind e k

/-- Elaborate `let x := e`. -/
partial def elabDoLetId (x : Ident) (ty? : Option Term) (rhs : Term)
    (rest : List DoElem) : ElabM Expr := do
  let name := x.getId
  let α ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  ElabM.withLetDecl name α val fun fvar => do
    let restExpr ← elabDoSeqCore rest
    mkLetFVars #[fvar] restExpr

/-- Elaborate `let pat := e`. -/
partial def elabDoLetPat (pat : Term) (rhs : Term)
    (rest : List DoElem) : ElabM Expr := do
  let α ← mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  let shape ← analyzePat pat α
  let k ← mkPatContinuation shape α fun _ => elabDoSeqCore rest
  synthesizeSyntheticMVarsNoPostponing
  -- For `.ctor`, `k` is `fun _x => T.casesOn _x …`; head-beta gives `T.casesOn val …`.
  -- For `.prod` the head is `Function.uncurry`, so `headBeta` is a no-op.
  return (mkApp k val).headBeta

/-- Elaborate an `if/else-if/…/else` chain as nested `ite`s. `rest` is bound
    once outside the chain. -/
partial def elabDoIfChain (branches : Array (Term × TSyntax ``doSeq))
    (elseSeq : TSyntax ``doSeq) (rest : List (TSyntax `doElem)) : ElabM Expr := do
  let elabAtType (ty : Expr) : ElabM Expr := do
    let some α := ty.getAppArgs[0]?
      | throwError "elabDoIfChain: expected monadic type, got{indentExpr ty}"
    withReader (fun ctx => { ctx with expectedAlpha := α }) do
      let mut result ← elabDoSeqCore (← getDoElems elseSeq)
      for (c, s) in branches.toList.reverse do
        let thenExpr ← elabDoSeqCore (← getDoElems s)
        let propExpr ← elabIfCondition c
        result ← mkIteExpr propExpr thenExpr result
      return result
  elabMonadicAsDoElem elabAtType rest

/-- Elaborate a `match`. Drives Lean's match elaborator with `_` in each arm
    body, then fills the resulting per-arm mvars by elaborating the original
    `doSeq`s directly in the mvar's local context — avoiding re-entry through a
    fresh syntax tree. `rest` is bound once outside the match. -/
partial def elabDoMatch
    (gen? : Option (TSyntax [`Lean.Parser.Term.trueVal, `Lean.Parser.Term.falseVal]))
    (motive? : Option (TSyntax ``Term.motive))
    (discrs : Array (TSyntax ``Term.matchDiscr))
    (alts : Array (TSyntax ``Term.matchAlt)) (rest : List DoElem) : ElabM Expr := do
  let mut armSeqs : Array (TSyntax ``doSeq) := #[]
  let mut holedAlts : Array (TSyntax ``Term.matchAlt) := #[]
  for alt in alts do
    match alt with
    | `(matchAltExpr| | $pats,* => $body) =>
      armSeqs := armSeqs.push ⟨body.raw⟩
      holedAlts := holedAlts.push (← `(matchAltExpr| | $pats,* => _))
    | _ => throwError "elabDoMatch: unexpected match arm syntax{indentD alt}"
  let termMatch ← `(match $[(generalizing := $gen?)]? $[$motive?]? $[$discrs],* with $holedAlts:matchAlt*)
  let elabAtType (ty : Expr) : ElabM Expr := do
    let some α := ty.getAppArgs[0]?
      | throwError "elabDoMatch: expected monadic type, got{indentExpr ty}"
    let matchExpr ← elabTermEnsuringType termMatch ty
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let matchExpr ← instantiateMVars matchExpr
    let some fnName := matchExpr.getAppFn.constName?
      | throwError "elabDoMatch: expected matcher application, got{indentExpr matchExpr}"
    let some info ← getMatcherInfo? fnName
      | throwError "elabDoMatch: `{fnName}` is not a matcher"
    let args := matchExpr.getAppArgs
    let firstAltIdx := info.getFirstAltPos
    unless armSeqs.size == info.numAlts do
      throwError "elabDoMatch: arm count mismatch (expected {info.numAlts}, got {armSeqs.size})"
    withReader (fun ctx => { ctx with expectedAlpha := α }) do
      for i in [:info.numAlts] do
        let elems ← getDoElems armSeqs[i]!
        ElabM.assignArmMVar args[firstAltIdx + i]! (elabDoSeqCore elems)
    instantiateMVars matchExpr
  elabMonadicAsDoElem elabAtType rest

partial def elabDoSeqCore : List (TSyntax `doElem) → ElabM Expr
  | [] => throwError "unexpected empty `do` block"
  | elem :: rest => elabDoElem elem rest

end

def elabDoSeq (doSeq : TSyntax ``doSeq) : ElabM Expr :=
  getDoElems doSeq >>= fun elems => elabDoSeqCore elems


/-- `do`-notation elaborator. Dispatches to the new `ElabM`-based elaborator for
    `Aeneas.Std.Result _` blocks when `Aeneas.newDoElab` is set; otherwise falls
    back to Lean's default. -/
@[term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  let useNewElab ← do
    let some expectedType := expectedType? | pure false
    let expectedType ← instantiateMVars =<< whnf expectedType
    match_expr expectedType with
    | Aeneas.Std.Result _ => pure (Aeneas.newDoElab.get (← getOptions))
    | _ => pure false
  if useNewElab then
    let `(do $doSeq) := stx | throwUnsupportedSyntax
    Do.ElabM.execute (Do.elabDoSeq doSeq) expectedType?.get!
  else
    Term.elabDo stx expectedType?

/-! ## Delaborators

The elaborator emits `Function.uncurry`-wrapped continuations for pattern
bindings. These delaborators turn them back into the expected `do let pat ← e`
and `let pat := val` forms. -/

open Lean PrettyPrinter Lean.PrettyPrinter.Delaborator SubExpr

/-- `Function.uncurry (fun a b => body) val` → `let (a, b) := val; body`. -/
@[delab app.Function.uncurry]
def delabUncurryLet : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let f := e.getArg! 3
  let .lam aName _ (.lam bName _ _ _) _ := f | failure
  let valStx ← withAppArg delab
  let bodyStx ← withAppFn (withAppArg (withBindingBody aName (withBindingBody bName delab)))
  `(let ($(mkIdent aName), $(mkIdent bName)) := $valStx
    $bodyStx)

/-- Partially applied `Function.uncurry (fun a b => body)` → `fun (a, b) => body`. -/
@[app_unexpander Function.uncurry]
def unexpUncurry : Unexpander
  | `($_ fun $a:ident $b:ident => $body) => `(fun ($a, $b) => $body)
  | _ => throw ()

/-- Extract binder names from a chain of `fun n₁ … nₖ => body`. -/
private def extractLamBinders : Expr → List Name
  | .lam n _ b _ => n :: extractLamBinders b
  | _ => []

/-- `T.casesOn val (fun f₁ … fₙ => body)` → `let ⟨f₁, …, fₙ⟩ := val; body`
    for any single-constructor inductive `T` (other than `Prod`). -/
@[delab app]
def delabSingleCtorCasesOn : Delab := do
  let e ← getExpr
  let .const fnName _ := e.getAppFn | failure
  let .str typeName "casesOn" := fnName | failure
  guard (typeName != ``Prod)
  let some (.inductInfo indInfo) := (← getEnv).find? typeName | failure
  guard (indInfo.ctors.length == 1)
  let args := e.getAppArgs
  let numParams := indInfo.numParams
  guard (args.size == numParams + 3)
  let names := extractLamBinders args[numParams + 2]!
  guard (!names.isEmpty)
  let discrStx ← withNaryArg (numParams + 1) delab
  let bodyStx ← withNaryArg (numParams + 2) <|
    names.foldr (fun n d => withBindingBody n d) delab
  let binders := names.toArray.map Lean.mkIdent
  `(let ⟨$binders,*⟩ := $discrStx
    $bodyStx)

/-- Walk a `Bind.bind` chain collecting `doElem`s. Extends Lean's builtin
    `delabDoElems` with two continuation shapes emitted by our elaborator:
    `Function.uncurry (fun a b => body)` → `let (a, b) ← e`, and
    `fun _x => T.casesOn _x (fun f₁ … fₙ => body)` → `let ⟨f₁, …, fₙ⟩ ← e`.
    Without this, Lean's `delabDoElems` bails on the non-lambda continuation,
    collapsing the whole chain back to `>>=` notation. -/
partial def aeneasDelabDoElems : DelabM (List (TSyntax `doElem)) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let α := e.getAppArgs[2]!
    let ma ← withAppFn <| withAppArg delab
    let arg := e.appArg!
    -- Tuple pattern: Function.uncurry (fun a b => body)
    if arg.isAppOfArity ``Function.uncurry 4 then
      if let .lam aName _ (.lam bName _ _ _) _ := arg.appArg! then
        let rest ← withAppArg <| withAppArg <|
          withBindingBody aName <| withBindingBody bName aeneasDelabDoElems
        let elem ← `(doElem| let ($(mkIdent aName), $(mkIdent bName)) ← $ma:term)
        return elem :: rest
    -- Ctor pattern: fun _x => T.casesOn _x (fun f₁ … fₙ => body)
    if let .lam xName _ xBody _ := arg then
      if let .const fnName _ := xBody.getAppFn then
        if let .str typeName "casesOn" := fnName then
          if typeName != ``Prod then
            if let some (.inductInfo indInfo) := (← getEnv).find? typeName then
              if indInfo.ctors.length == 1 then
                let xArgs := xBody.getAppArgs
                let numParams := indInfo.numParams
                if xArgs.size == numParams + 3 ∧ xArgs[numParams + 1]! == .bvar 0 then
                  let names := extractLamBinders xArgs[numParams + 2]!
                  if !names.isEmpty then
                    let rest ← withAppArg <| withBindingBody xName <|
                      withNaryArg (numParams + 2) <|
                        names.foldr (fun n d => withBindingBody n d) aeneasDelabDoElems
                    let binders := names.toArray.map Lean.mkIdent
                    let elem ← `(doElem| let ⟨$binders,*⟩ ← $ma:term)
                    return elem :: rest
    -- Regular bind: fun n => body (mirrors Lean's delabDoElems)
    withAppArg do
      match (← getExpr) with
      | .lam _ _ body _ =>
        withBindingBodyUnusedName fun n => do
          let nStx : TSyntax `term := ⟨n⟩
          let rest ← aeneasDelabDoElems
          if body.hasLooseBVars then
            return (← `(doElem| let $nStx:term ← $ma:term)) :: rest
          else if α.isConstOf ``Unit ∨ α.isConstOf ``PUnit then
            return (← `(doElem| $ma:term)) :: rest
          else
            return (← `(doElem| let _ ← $ma:term)) :: rest
      | _ => failure
  else if e.isLet then
    let .letE n t v b nondep ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    Meta.withLetDecl n t v (nondep := nondep) fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 do
        let rest ← aeneasDelabDoElems
        if nondep then
          return (← `(doElem| have $(mkIdent n) : $stxT := $stxV)) :: rest
        else
          return (← `(doElem| let $(mkIdent n) : $stxT := $stxV)) :: rest
  else
    let stx ← delab
    return [← `(doElem| $stx:term)]

/-- Top-level `do`-block delab. Walks a `Bind.bind` chain with
    `aeneasDelabDoElems`, which understands tuple/ctor pattern continuations
    and so doesn't bail on them the way Lean's builtin `delabDo` does. -/
@[delab app.Bind.bind]
def aeneasDelabDo : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Bind.bind 6
  let elems ← aeneasDelabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

end Do
end Aeneas

section tests

open Aeneas Std Result ControlFlow Error

def test1 : Result Nat := do
  ok 42
/--
info: def test1 : Result ℕ :=
ok 42
-/
#guard_msgs in
#print test1

def test2 : Result Nat := do
  let x ← ok 1
  ok x
/--
info: def test2 : Result ℕ :=
do
  let x ← ok 1
  ok x
-/
#guard_msgs in
#print test2

def test3 : Result Nat := do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)
/--
info: def test3 : Result ℕ :=
do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)
-/
#guard_msgs in
#print test3

def test4 : Result Nat := do
  let x : Nat ← ok 1
  ok (x + 1)
/--
info: def test4 : Result ℕ :=
do
  let x ← ok 1
  ok (x + 1)
-/
#guard_msgs in
#print test4

def test5 : Result Nat := do
  let x := 1
  ok (x + 2)
/--
info: def test5 : Result ℕ :=
have x := 1;
ok (x + 2)
-/
#guard_msgs in
#print test5

def test6 : Result Nat := do
  let x : Nat := 1
  let y ← ok 2
  ok (x + y)
/--
info: def test6 : Result ℕ :=
have x := 1;
do
let y ← ok 2
ok (x + y)
-/
#guard_msgs in
#print test6

def test7 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok x else ok 0
/--
info: def test7 : Result ℕ :=
do
  let x ← ok 1
  if x > 0 then ok x else ok 0
-/
#guard_msgs in
#print test7

def test8 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20
/--
info: def test8 : Result ℕ :=
do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20
-/
#guard_msgs in
#print test8

def test9 : Result Nat := do
  let x ← ok 2
  let y ← do
    if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test9 : Result ℕ :=
do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
-/
#guard_msgs in
#print test9

def test10 : Result Nat := do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test10 : Result ℕ :=
do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
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
info: def test11 : Result ℕ :=
do
  let max ← ok 10
  loop (test11_body max) 0
-/
#guard_msgs in
#print test11

def test12 : Result Nat := do
  let (a, b) ← ok (1, 2)
  ok (a + b)
/--
info: def test12 : Result ℕ :=
do
  let (a, b) ← ok (1, 2)
  ok (a + b)
-/
#guard_msgs in
#print test12

def test13 : Result Nat := do
  let (_, b) ← ok (1, 2)
  ok b
/--
info: def test13 : Result ℕ :=
do
  let (_, b) ← ok (1, 2)
  ok b
-/
#guard_msgs in
#print test13

def test14 : Result Nat := do
  let (a, b) := (1, 2)
  ok (a + b)
/--
info: def test14 : Result ℕ :=
let (a, b) := (1, 2)
ok (a + b)
-/
#guard_msgs in
#print test14

def test15 : Result Nat := do
  let x ← ok 1
  match x with
  | 0 => ok 10
  | _ => ok 20
/--
info: def test15 : Result ℕ :=
do
  let x ← ok 1
  match x with
    | 0 => ok 10
    | x => ok 20
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
info: def test16 : Result ℕ :=
do
  let x ← ok 1
  let y ←
    match x with
      | 0 => ok 10
      | x => ok 20
  ok (y + 1)
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
do
  let s ← lift (Array.make 5#usize [0#u32, 1#u32, 2#u32, 3#u32, 4#u32] massert_test._proof_7).to_slice
  let i ← core.slice.Slice.iter s
  let it ← core.slice.iter.IteratorSliceIter.step_by i 1#usize
  let (o, it1) ← core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it
  let i1 ← core.option.Option.unwrap o
  massert (i1 = 0#u32)
  let (o1, it2) ← core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it1
  let i2 ← core.option.Option.unwrap o1
  massert (i2 = 1#u32)
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
fun x => do
  let b ← ok x
  if b = true then ok true else ok false
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
fun b1 => do
  let _ ← if b1 = true then ok (true, 2#u32) else ok (false, 0#u32)
  ok ()
-/
#guard_msgs in
#print do_nested_test

def if_then_add_test (b : Bool) (x : Std.U32) : Result Std.U32 := do
  let y ← if b then ok 1#u32 else ok 0#u32
  x + y
/--
info: def if_then_add_test : Bool → U32 → Result U32 :=
fun b x => do
  let y ← if b = true then ok 1#u32 else ok 0#u32
  x + y
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
fun a x => do
  let y ←
    match a with
      | 0#32#uscalar => ok 0#u32
      | 1#32#uscalar => ok 1#u32
      | x => ok 2#u32
  x + y
-/
#guard_msgs in
#print match_add_test

def make2nats (x y : Nat) : Result (Nat × Nat) := do
  ok (x, y)

def make3nats (x y z : Nat) : Result ((Nat × Nat) × Nat) := do
  ok ((x, y), z)

def make4nats (x y z w : Nat) : Result ((Nat × Nat) × (Nat × Nat)) := do
  ok ((x, y), z, w)

def nested_pat_test : Result Nat := do
  let (a, b) ← make2nats 1 2
  let ((c, d), e) ← make3nats 3 4 5
  let ((f, g), (h, i)) ← make4nats 6 7 8 9
  ok (a + b + c + d + e + f + g + h + i)
/--
info: def nested_pat_test : Result ℕ :=
do
  let (a, b) ← make2nats 1 2
  let (_x0, e) ← make3nats 3 4 5
  let (c, d) := _x0
    do
    let (_x0, _x1) ← make4nats 6 7 8 9
    let (f, g) := _x0
      let (h, i) := _x1
      ok (a + b + c + d + e + f + g + h + i)
-/
#guard_msgs in
#print nested_pat_test

structure TwoNatsWrapped where
  x : Nat
  y : Nat

structure FourNatsWrapped where
  z : TwoNatsWrapped
  w : TwoNatsWrapped

def make2natswrapped (x y : Nat) : Result TwoNatsWrapped := do
  ok { x, y }

def make4natswrapped (w₁ w₂ : TwoNatsWrapped) : Result FourNatsWrapped := do
  ok ⟨w₁, w₂⟩

def nested_wrapped_pat_test : Result Nat := do
  let w₁ ← make2natswrapped 1 2
  let w₂ ← make2natswrapped 3 4
  let ⟨⟨x, y⟩, ⟨z, w⟩⟩ ← make4natswrapped w₁ w₂
  ok (x + y + z + w)
/--
info: def nested_wrapped_pat_test : Result ℕ :=
do
  let w₁ ← make2natswrapped 1 2
  let w₂ ← make2natswrapped 3 4
  let ⟨_x0, _x1⟩ ← make4natswrapped w₁ w₂
  let ⟨x, y⟩ := _x0
    let ⟨z, w⟩ := _x1
    ok (x + y + z + w)
-/
#guard_msgs in
#print nested_wrapped_pat_test

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
info: def universe_test : {T : Type} → Wrapper T → Result (Wrapper T × (Wrapper T → Wrapper T)) :=
fun {T} w => do
  let (inner, back) ← make_wrapper w.x
  have back2 : Wrapper T → Wrapper T := fun w1 => back { x := w1.x }
  ok (inner, back2)
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
info: def universe_tuple_test : {T : Type} → T → T → Result ((T × T) × (T × T → List T × List T)) :=
fun {T} x y =>
  make_pair x y >>=
    Function.uncurry fun a =>
      Function.uncurry fun b (back, back1) =>
        have back2 := fun p =>
          match p with
          | (t1, t2) => (back t1, back1 t2);
        ok ((a, b), back2)
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
    if i < i1 then do
      let (_, update_back) ← get_and_update xs i
      let i2 ← i + 1#usize
      let xs1 : alloc.vec.Vec U32 := update_back 0#u32
      f xs1 i2
    else ok xs)
  mono_loop_test._proof_1
-/
#guard_msgs in
#print mono_loop_test

def doIf_pat_test (b : Bool) : Result (Nat × Nat) := do
  let (x, y) ←
    if b then ok (1, 2) else ok (3, 4)
  ok (x, y)
/--
info: def doIf_pat_test : Bool → Result (ℕ × ℕ) :=
fun b => do
  let (x, y) ← if b = true then ok (1, 2) else ok (3, 4)
  ok (x, y)
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
info: def match_pat_test : ℕ → Result (ℕ × ℕ) :=
fun n => do
  let (x, y) ←
    match n with
      | 0 => ok (1, 2)
      | x => ok (3, 4)
  ok (x, y)
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
info: def else_if_test : ℕ → ℕ → Result Ordering :=
fun x y => if x < y then ok Ordering.lt else if x = y then ok Ordering.eq else ok Ordering.gt
-/
#guard_msgs in
#print else_if_test

inductive Wrap where
  | mk : Nat → Wrap

def anon_ctor_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ := w
  ok (n + 1)
/--
info: def anon_ctor_test : Wrap → Result ℕ :=
fun w =>
  let ⟨n⟩ := w
  ok (n + 1)
-/
#guard_msgs in
#print anon_ctor_test

def anon_ctor_monadic_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ ← ok w
  ok (n + 1)
/--
info: def anon_ctor_monadic_test : Wrap → Result ℕ :=
fun w => do
  let ⟨n⟩ ← ok w
  ok (n + 1)
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
  if b = true then ok { ty := T, inst := inst1, val := x } else ok { ty := W, inst := inst2, val := y }
-/
#guard_msgs in
#print exbox_lambda_test

def do_if_rest_test : Result Nat := do
  let b ← ok true
  if b then ok () else ok ()
  if b then ok () else ok ()
  if b then ok () else ok ()
  ok 1
/--
info: def do_if_rest_test : Result ℕ :=
do
  let b ← ok true
  if b = true then ok () else ok ()
  if b = true then ok () else ok ()
  if b = true then ok () else ok ()
  ok 1
-/
#guard_msgs in
#print do_if_rest_test

inductive MatchTest | A | B | C

def do_match_rest_test (m : MatchTest) : Result Nat := do
  let n ← ok 3
  match m with
  | .A => ok ()
  | .B => ok ()
  | .C => ok ()
  match m with
  | .A => ok ()
  | .B => ok ()
  | .C => ok ()
  pure n
/--
info: def do_match_rest_test : MatchTest → Result ℕ :=
fun m => do
  let n ← ok 3
  match m with
    | MatchTest.A => ok ()
    | MatchTest.B => ok ()
    | MatchTest.C => ok ()
  match m with
    | MatchTest.A => ok ()
    | MatchTest.B => ok ()
    | MatchTest.C => ok ()
  pure n
-/
#guard_msgs in
#print do_match_rest_test

end tests
