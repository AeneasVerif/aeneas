import Lean
import Aeneas.Std
import Aeneas.Do.Init

open Lean Elab Parser Term Meta

namespace Aeneas

/-- Continuation monad transformer. `ContT r m a` represents a computation that
    produces an `a` but can invoke a continuation `a → m r` to produce the final `m r`. -/
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

/-- Run a `ContT` computation with a final continuation. -/
@[inline] def run (x : ContT r m a) (k : a → m r) : m r := x k

/-- Run a `ContT` computation with `pure` as the final continuation. -/
@[inline] def runPure [Monad m] (x : ContT r m r) : m r := x pure

/-- Access the current continuation. -/
@[inline] def callCC (f : (a → ContT r m b) → ContT r m a) : ContT r m a :=
  fun k => f (fun a _ => k a) k

/-- Reify the current continuation as `k : a → m r`, allowing the caller to invoke it
    (possibly zero or multiple times) to build the final result. This is the `shift`
    operator from delimited continuations. -/
@[inline] def shift (f : (a → m r) → m r) : ContT r m a := f

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

/-- Run `body fvar` under a fresh local declaration `name : type`, threading the
    `ElabM` continuation through `withLocalDecl`. This encapsulates the drop into
    raw `ContT`/`TermElabM` needed because `ContT` can't implement `MonadControlT`. -/
def ElabM.withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → ElabM Expr) : ElabM Expr := do
  let ctx ← read
  (fun _ k => Meta.withLocalDecl name bi type fun fvar =>
      (body fvar).run ctx |>.run k
    : ElabM Expr)

/-! ## Elaboration of `doSeq` and `doElem` -/

def getDoElems (doSeq : TSyntax ``doSeq) : ElabM (Array $ TSyntax `doElem) := do
  match doSeq with
  | `(doSeq| $[$elems $[;]?]*) => return elems
  | _ => throwError "unexpected `doSeq` syntax {indentD doSeq}"

/-! ## Individual `doElem` handlers-/
mutual 

/-- Call the right doElem elaborator -/
partial def elabDoElem (elem : TSyntax `doElem) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
  match elem with
  | `(doElem| let $x:ident $[: $ty?]? ← $rhs) => elabDoLetArrowId x ty? rhs isLast rest
  -- | `(doElem| let $_:term ← $_)  => elabDoLetArrowPat elem isLast rest
  -- | `(doElem| let $_:ident := $_) => elabDoLetId elem isLast rest
  -- | `(doElem| let $_:term := $_)  => elabDoLetPat elem isLast rest
  | `(doElem| $expr:term)            => elabDoExpr expr isLast rest
  | _ =>
    match elem.raw.getKind with
    -- | ``Term.doIf    => elabDoIf elem isLast rest
    -- | ``Term.doMatch => elabDoMatch elem isLast rest
    | k => throwError "unsupported `do` element (kind: {k}){indentD elem}"

partial def elabDoExpr (term : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
  if isLast then
    -- Terminal: elaborate as the monadic return value
    let expectedType ← ElabM.mkMonadicType (← mkFreshTypeMVar)
    elabTermEnsuringType term expectedType
  else
    -- Non-terminal: elaborate as `m PUnit`, then `Bind.bind e (fun _ => rest)`
    let expectedType ← ElabM.mkMonadicType (mkConst ``PUnit)
    let e ← elabTermEnsuringType term expectedType
    ElabM.withLocalDecl `_ .default (mkConst ``PUnit) fun fvar => do
      let restExpr ← rest
      let body ← mkLambdaFVars #[fvar] restExpr
      ElabM.mkBind e body

/-- Elaborate a monadic let-arrow with a simple identifier (`let x ← e` or `let x : ty ← e`).
    Desugars to `Bind.bind e (fun x => rest)`.
    The RHS may be a `doExpr` or a `doNested` (nested `do` block). -/
partial def elabDoLetArrowId (x : TSyntax `ident) (ty? : Option Syntax) (rhs : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
  let name := x.getId
  -- If a type annotation is given, elaborate it; otherwise use a fresh metavar
  let α ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let expectedType ← ElabM.mkMonadicType α
  let e ← if rhs.getKind == ``Parser.Term.doNested then
      let elems ← getDoElems ⟨rhs[1]⟩
      elabDoSeqCore elems 0
    else
      -- doExpr: the inner term is at rhs[0]
      elabTermEnsuringType rhs[0] expectedType
  -- Build `Bind.bind e (fun x => rest)`
  let α ← instantiateMVars α
  ElabM.withLocalDecl name .default α fun fvar => do
    let restExpr ← rest
    let body ← mkLambdaFVars #[fvar] restExpr
    ElabM.mkBind e body

-- /-- Elaborate a monadic let-arrow with a pattern (`let (a, b) ← e`).
--     Desugars to `Bind.bind e (fun _x => match _x with | (a, b) => rest)`. -/
-- partial def elabDoLetArrowPat (stx : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
--   sorry

-- /-- Elaborate a pure let binding with a simple identifier (`let x := e`).
--     Introduces a local definition and continues. -/
-- partial def elabDoLetId (stx : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
--   sorry

-- /-- Elaborate a pure let binding with a pattern (`let (a, b) := e` or `let ⟨f⟩ := e`).
--     Desugars to a `match` or projections. -/
-- partial def elabDoLetPat (stx : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
--   sorry

-- /-- Elaborate an if-then-else (`Lean.Parser.Term.doIf`).
--     Both branches are `doSeq`s that are elaborated independently. -/
-- partial def elabDoIf (stx : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
--   sorry

-- /-- Elaborate a pattern match (`Lean.Parser.Term.doMatch`).
--     Each arm body is a `doSeq` elaborated independently. -/
-- partial def elabDoMatch (stx : Syntax) (isLast : Bool) (rest : ElabM Expr) : ElabM Expr := do
--   sorry

/-- Walk an array of `doElem` nodes starting at index `i`, threading each element's
    result into the next via the explicit `rest` thunk passed to each handler. -/
partial def elabDoSeqCore (elems : Array $ TSyntax `doElem) (i : Nat) : ElabM Expr := do
  if h : i < elems.size then
    let isLast := i + 1 = elems.size
    let rest : ElabM Expr :=
      if isLast then throwError "internal error: requested rest after last element"
      else elabDoSeqCore elems (i + 1)
    elabDoElem elems[i] isLast rest
  else
    throwError "internal error: index out of bounds in `do` block elaboration"

end

/-- Elaborate a `doSeq` (the body of a `do` block): extract the `doElem`s and
    process them left-to-right. Each element handler receives a thunk for
    "elaborate the rest of the block" so it can build `Bind.bind` or `let` around it. -/
def elabDoSeq (doSeq : TSyntax ``doSeq) : ElabM Expr := do
  let elems ← getDoElems doSeq
  if elems.isEmpty then
    throwError "unexpected empty `do` block"
  else
    elabDoSeqCore elems 0


@[term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  if ← getBoolOption ``newDoElab then
    let expectedType ← match expectedType? with
      | some ty => instantiateMVars ty
      | none => do
        let α ← Meta.mkFreshTypeMVar
        -- We'll only ever be using this elaborator on the extracted code, so the monad should
        -- always be `Aeneas.Std.Result`
        return mkApp (.const ``Aeneas.Std.Result [← Meta.getLevel α]) α 
    let `(do $doSeq) := stx | throwUnsupportedSyntax
    -- TODO: delete this
    logWarning "Using the new `doSeq` elaborator!"
    Do.ElabM.execute (Do.elabDoSeq doSeq) expectedType
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

set_option pp.notation false
#print test1
#print test2
#print test3
#print test4
