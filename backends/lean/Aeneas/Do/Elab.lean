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

@[inline] def run (x : ContT r m a) (k : a → m r) : m r := x k

@[inline] def runPure [Monad m] (x : ContT r m r) : m r := x pure

@[inline] def callCC (f : (a → ContT r m b) → ContT r m a) : ContT r m a :=
  fun k => f (fun a _ => k a) k

end ContT

namespace Do

/-- Cached information about the monad extracted from the expected type of the `do` block.-/
structure Context where
  m : Expr
  /-- Cached `Bind m` instance -/
  bindInst : Expr
  /-- Cached `Pure m` instance -/
  pureInst : Expr

abbrev ElabM := ReaderT Context $ ContT Expr TermElabM

/-- Extract the monad `m` from an expected type `m α` and synthesizes and caches the 
    `Bind` and `Pure` instances for `m`. -/
def mkContext (expectedType : Expr) : TermElabM Context := do
  let expectedType ← whnf expectedType
  let m ← match expectedType with
    | Expr.app m _ => pure m
    | _ => throwError "expected a monadic type `m α`, got {indentExpr expectedType}"
  let bindInst ← synthInstance (← mkAppM ``Bind #[m])
  let pureInst ← synthInstance (← mkAppM ``Pure #[m])
  return { m, bindInst, pureInst }

-- TODO: clean this up
def ElabM.mkBind (e k : Expr) : ElabM Expr := do
  let ctx ← read
  -- We build `@Bind.bind.{u,v} m inst α β e k` manually.
  -- For Result.{u}, v = u, so we just need the level of α.
  -- α comes from the type of e: `m α`
  let eType ← inferType e >>= instantiateMVars
  let α ← match eType with
    | Expr.app _ a => pure a
    | _ => throwError "mkBind: expected monadic type, got{indentExpr eType}"
  -- β comes from k: it's a lambda `fun (x : α) => body`, body has type `m β`
  let kBody ← match k with
    | Expr.lam _ _ body _ => inferType body >>= instantiateMVars
    | _ => inferType (Expr.app k (← mkFreshExprMVar α)) >>= instantiateMVars
  let β ← match kBody with
    | Expr.app _ b => pure b
    | _ => throwError "mkBind: expected monadic return type, got{indentExpr kBody}"
  -- Extract the universe levels from the monad's type: `m : Sort u → Sort v`
  -- Bind.bind.{u', v'} where α : Sort u' and m α : Sort v'
  -- For m : Type u → Type v, the sorts are Sort (u+1) and Sort (v+1)
  -- so u' = u and v' = v.
  let mType ← inferType ctx.m >>= instantiateMVars
  -- m : Type u → Type v means mType = Sort (u+1) → Sort (v+1)
  -- Bind.bind.{u, v} needs the raw u and v
  let (u, v) ← match mType with
    | Expr.forallE _ (Expr.sort (.succ u)) (Expr.sort (.succ v)) _ => pure (u, v)
    | _ => throwError "mkBind: unexpected monad type{indentExpr mType}"
  return mkApp6 (.const ``Bind.bind [u, v]) ctx.m ctx.bindInst α β e k

def ElabM.mkPure (e : Expr) : ElabM Expr := mkAppM ``Pure.pure #[e]

/-- Build the expected monadic type `m α` for a sub-expression. -/
def ElabM.mkMonadicType (α : Expr) : ElabM Expr := read >>= fun ctx => pure <| mkApp ctx.m α

/-- Run a `Do.ElabM` computation, given an expected type for the whole `do` block. -/
def ElabM.execute (x : ElabM Expr) (expectedType : Expr) : TermElabM Expr := do
  let ctx ← mkContext expectedType
  (x.run ctx).runPure

/-- Run `body fvar` under a fresh local declaration `name : type` -/
def ElabM.withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLocalDecl name bi type fun fvar =>
      (body fvar).run ctx |>.run k

/-- Run `body fvar` under a fresh let declaration `let name : type := value` -/
def ElabM.withLetDecl (name : Name) (type : Expr) (value : Expr)
    (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  fun _ k => Meta.withLetDecl name type value fun fvar =>
      (body fvar).run ctx |>.run k

def getDoElems (doSeq : TSyntax ``doSeq) : ElabM (List $ TSyntax `doElem) := do
  match doSeq with
  | `(doSeq| $[$elems $[;]?]*) => return elems.toList
  | _ => throwError "unexpected `doSeq` syntax {indentD doSeq}"

partial def buildCurriedLambda (names : List Name) (types : List Expr)
    (body : ElabM Expr) : ElabM Expr :=
  match names, types with
  | [], _ | _, [] => body
  | [n], [t] =>
    ElabM.withLocalDecl n .default t fun fvar => do
      let bodyExpr ← body
      mkLambdaFVars #[fvar] bodyExpr
  | n :: ns, t :: ts =>
    ElabM.withLocalDecl n .default t fun fvar => do
      let inner ← buildCurriedLambda ns ts body
      mkLambdaFVars #[fvar] inner

partial def extractPatNames (pat : Syntax) : List Name :=
  if pat.getKind == ``Term.tuple then
    let items := pat[1]  -- null node: first_elem, comma, null(rest...)
    let first := extractPatNames items[0]
    let rest := extractRestNames items[2].getArgs.toList
    first ++ rest
  else if pat.isIdent then
    [pat.getId]
  else
    [`_]
where
  extractRestNames : List Syntax → List Name
    | [] => []
    | [x] => extractPatNames x
    | x :: _comma :: rest => extractPatNames x ++ extractRestNames rest

partial def decomposeProductType (ty : Expr) (n : Nat) : MetaM (List Expr) := do
  if n ≤ 1 then return [ty]
  let ty ← whnf ty
  match ty.app2? ``Prod with
  | some (α, β) => return α :: (← decomposeProductType β (n - 1))
  | none => throwError "expected a product type, got{indentExpr ty}"

partial def mkUncurries (innerLam : Expr) (types : List Expr) : MetaM Expr := do
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
partial def elabDoElem (elem : TSyntax `doElem) (rest : List (TSyntax `doElem)) : ElabM Expr := do
  match elem with
  | `(doElem| let $x:ident $[: $ty?]? ← $rhs) => elabDoLetArrowId x ty? rhs rest
  | `(doElem| let $pat:term ← $rhs)  => elabDoLetArrowPat pat rhs rest
  | `(doElem| let $x:ident $[: $ty?]? := $rhs) => elabDoLetId x ty? rhs rest
  | `(doElem| let $pat:term := $rhs)  => elabDoLetPat pat rhs rest
  | `(doElem| if $cond then $thenSeq else $elseSeq) => elabDoIf cond ⟨thenSeq⟩ ⟨elseSeq⟩ rest
  | `(doElem| $expr:term)            => elabDoExpr expr rest
  | _ =>
    match elem.raw.getKind with
    | ``Term.doMatch => elabDoMatch elem.raw rest
    | k => throwError "unsupported `do` element (kind: {k}){indentD elem}"

/- Elaborate a term in a `doSeq` position -/
partial def elabDoExpr (term : Syntax) (rest : List (TSyntax `doElem)) : ElabM Expr := do
  match rest with
  | [] =>
    -- Terminal: elaborate as the monadic return value
    let expectedType ← ElabM.mkMonadicType (← mkFreshTypeMVar)
    elabTermEnsuringType term expectedType
  | _ =>
    -- Non-terminal: elaborate as `m PUnit`, then `Bind.bind e (fun _ => rest)`
    let expectedType ← ElabM.mkMonadicType (mkConst ``PUnit)
    let e ← elabTermEnsuringType term expectedType
    ElabM.withLocalDecl `_ .default (mkConst ``PUnit) fun fvar => do
      let restExpr ← elabDoSeqCore rest
      let body ← mkLambdaFVars #[fvar] restExpr
      ElabM.mkBind e body

/-- Elaborate a let-arrow with a simple identifier (`let x ← e` ← e`) -/
partial def elabDoLetArrowId (x : TSyntax `ident) (ty? : Option Syntax) (rhs : Syntax)
    (rest : List (TSyntax `doElem)) : ElabM Expr := do
  let name := x.getId
  let α ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType α
  let e ← match rhs.getKind with
    | ``Parser.Term.doNested =>
      let elems ← getDoElems ⟨rhs[1]⟩
      elabDoSeqCore elems
    | ``Parser.Term.doExpr =>
      elabTermEnsuringType rhs[0] expectedType
    | _ =>
      -- The RHS is a do-element like doIf or doMatch — elaborate it as a singleton seq
      elabDoElem ⟨rhs⟩ []
  let α ← instantiateMVars α
  ElabM.withLocalDecl name .default α fun fvar => do
    let restExpr ← elabDoSeqCore rest
    let body ← mkLambdaFVars #[fvar] restExpr
    ElabM.mkBind e body

/-- Elaborate a monadic let-arrow with a pattern (`let (a, b) ← e`) -/
partial def elabDoLetArrowPat (pat : Syntax) (rhs : Syntax) (rest : List (TSyntax `doElem)) : 
    ElabM Expr := do
  let names := extractPatNames pat
  let α ← mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType α
  let e ← match rhs.getKind with
    | ``Parser.Term.doNested =>
      let elems ← getDoElems ⟨rhs[1]⟩
      elabDoSeqCore elems
    | ``Parser.Term.doExpr =>
      elabTermEnsuringType rhs[0] expectedType
    | _ => elabDoElem ⟨rhs⟩ []
  let α ← instantiateMVars α
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
  let compTypes ← decomposeProductType α names.length
  let curried ← buildCurriedLambda names compTypes (elabDoSeqCore rest)
  synthesizeSyntheticMVarsNoPostponing
  let k ← mkUncurries curried compTypes
  return Expr.app k val

/-- Elaborate an if-then-else -/
partial def elabDoIf (cond : Syntax) (thenSeq elseSeq : TSyntax ``doSeq)
    (rest : List (TSyntax `doElem)) : ElabM Expr := do
  -- TODO: look at this logic again, not sure if it's right
  -- Append the rest of the do-block to both branches so the continuation
  -- flows through the if/else without needing join points
  let thenElems := (← getDoElems thenSeq) ++ rest
  let elseElems := (← getDoElems elseSeq) ++ rest
  let condExpr ← elabTerm cond none
  let thenExpr ← elabDoSeqCore thenElems
  let thenType ← inferType thenExpr
  let elseExpr ← elabDoSeqCore elseElems
  let elseExpr ← Term.ensureHasType (some thenType) elseExpr
  -- Resolve pending metavariables and build @ite _ cond inst thenExpr elseExpr
  synthesizeSyntheticMVarsNoPostponing
  mkAppM ``ite #[← instantiateMVars condExpr, ← instantiateMVars thenExpr, ← instantiateMVars elseExpr]

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
  let expectedType ← ElabM.mkMonadicType (← mkFreshTypeMVar)
  elabTermEnsuringType termMatch expectedType

partial def elabDoSeqCore : List (TSyntax `doElem) → ElabM Expr
  | [] => throwError "unexpected empty `do` block"
  | [elem] => elabDoElem elem []
  | elem :: rest => elabDoElem elem rest

end

def elabDoSeq (doSeq : TSyntax ``doSeq) : ElabM Expr := do
  let elems ← getDoElems doSeq
  elabDoSeqCore elems


@[term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  let useNewElab ← (do
    if !(← getBoolOption ``newDoElab) then return false
    let some expectedType := expectedType? | return false
    let expectedType ← whnf (← instantiateMVars expectedType)
    match expectedType with
    | Expr.app m _ => return m.isAppOf ``Aeneas.Std.Result
    | _ => return false : TermElabM Bool)
  if useNewElab then
    logWarning "Using new do elaborator"
    let `(do $doSeq) := stx | throwUnsupportedSyntax
    Do.ElabM.execute (Do.elabDoSeq doSeq) expectedType?.get!
  else
    Term.elabDo stx expectedType?

end Do
end Aeneas

open Aeneas.Std Result
set_option Aeneas.newDoElab true

def test1 : Result Nat := do
  ok 42

def test2 : Result Nat := do
  let x ← ok 1
  ok x

def test3 : Result Nat := do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)

def test4 : Result Nat := do
  let x : Nat ← ok 1
  ok (x + 1)

def test5 : Result Nat := do
  let x := 1
  ok (x + 2)

def test6 : Result Nat := do
  let x : Nat := 1
  let y ← ok 2
  ok (x + y)

def test7 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok x else ok 0

def test8 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20

def test9 : Result Nat := do
  let x ← ok 2
  let y ← do
    if x > 1 then ok 1 else ok 0
  ok y

def test10 : Result Nat := do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y

def test11_body (max i : Nat) : Result (ControlFlow Nat Nat) :=
  if i < max then ok (ControlFlow.cont (i + 1))
  else ok (ControlFlow.done i)

def test11 : Result Nat := do
  let max ← ok 10
  loop (test11_body max) 0

def test12 : Result Nat := do
  let (a, b) ← ok (1, 2)
  ok (a + b)

def test13 : Result Nat := do
  let (_, b) ← ok (1, 2)
  ok b

structure Wrapper where
  val : Nat

set_option Aeneas.newDoElab false in
def test14 : Result Nat := do
  let ⟨a⟩ ← ok (Wrapper.mk 42)
  ok a

def test15 : Result Nat := do
  let (a, b) := (1, 2)
  ok (a + b)

def test16 : Result Nat := do
  let x ← ok 1
  match x with
  | 0 => ok 10
  | _ => ok 20

def test17 : Result Nat := do
  let x ← ok 1
  let y ← match x with
    | 0 => ok 10
    | _ => ok 20
  ok (y + 1)

set_option pp.notation false
#print test1
#print test2
#print test3
#print test4
#print test5
#print test6
#print test7
#print test8
#print test9
#print test10
#print test11
#print test12
#print test13
#print test14
#print test15
#print test16
#print test17
