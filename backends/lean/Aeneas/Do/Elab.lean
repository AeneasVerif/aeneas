import Lean
import Mathlib.Control.Monad.Cont
import Aeneas.Std

/-! # New `do` Elaborator

The goal for this elaborator is to construct easier Lean terms to reason about.

The Aeneas extracted `do` syntax is a proper subset of the Lean `do` syntax,
with no early returns, so the new elaborator can avoid the use of jumps. 

We also change the elaboration of pattern matched let bindings to avoid using
the builtin match-based pattern matching.
-/

open Lean Elab Parser Term Meta

/- Some necessary instances for `ContT` -/

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

/-- Elaborate `cond`, returning a `Prop`. `Bool` is coerced to `cond = true`.
    Synthetic mvars are forced so `Decidable` can be inferred downstream. -/
def elabIfCondition (cond : Term) : ElabM Expr := do
  let condExpr ← Lean.Elab.Term.elabTerm cond none
  synthesizeSyntheticMVarsNoPostponing
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
partial def elabDoElem (elem : DoElem) (rest : List DoElem) : ElabM Expr := do
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
  -- For `.ctor`, `k` is `fun _x => T.casesOn _x …`; headBeta gives `T.casesOn val …`.
  -- For `.prod` the head is `Function.uncurry`, so `headBeta` is a no-op.
  return (mkApp k val).headBeta

/-- Elaborate an `if/else-if/…/else` chain as nested `ite`s. `rest` is bound
    once outside the chain. -/
partial def elabDoIfChain (branches : Array (Term × TSyntax ``doSeq))
    (elseSeq : TSyntax ``doSeq) (rest : List DoElem) : ElabM Expr := do
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
    `doSeq`s directly in the mvar's local context -/
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
    synthesizeSyntheticMVarsNoPostponing
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

partial def elabDoSeqCore : List DoElem → ElabM Expr
  | [] => throwError "unexpected empty `do` block"
  | elem :: rest => elabDoElem elem rest

end

def elabDoSeq (doSeq : TSyntax ``doSeq) : ElabM Expr :=
  getDoElems doSeq >>= fun elems => elabDoSeqCore elems

/-- Option to toggle the new Aeneas `do` elaborator -/
register_option Aeneas.newDoElab : Bool := {
    defValue := true
    descr  := "Use the custom Aeneas `do` elaborator"
  }

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

end Do
end Aeneas
