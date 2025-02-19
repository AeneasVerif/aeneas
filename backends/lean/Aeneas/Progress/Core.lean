import Lean
import Aeneas.Utils
import Aeneas.Std.Core
import Aeneas.Extensions
import Aeneas.Progress.Trace

namespace Aeneas

namespace Progress

open Lean Elab Term Meta
open Utils Extensions

/- # Progress tactic -/

structure PSpecDesc where
  -- The universally quantified variables
  -- Can be fvars or mvars
  fvars : Array Expr
  -- The existentially quantified variables
  evars : Array Expr
  -- The function applied to its arguments
  fArgsExpr : Expr
  -- ⊤ if the function is a constant (must be if we are registering a theorem,
  -- but is not necessarily the case if we are looking at a goal)
  fIsConst : Bool
  -- The function arguments
  fLevels : List Level
  args : Array Expr
  -- The returned value
  ret : Expr
  -- The postcondition (if there is)
  post : Option Expr

section Methods
  variable [MonadLiftT MetaM m] [MonadControlT MetaM m] [Monad m] [MonadOptions m]
  variable [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  variable [MonadError m]
  variable {a : Type}

  /- Analyze a goal or a pspec theorem to decompose its arguments.

     PSpec theorems should be of the following shape:
     ```
     ∀ x1 ... xn, H1 → ... Hn → ∃ y1 ... ym. f x1 ... xn = .ret ... ∧ Post1 ∧ ... ∧ Postk
     ```

     The continuation `k` receives the following inputs:
     - universally quantified variables
     - assumptions
     - existentially quantified variables
     - function name
     - function arguments
     - return
     - postconditions
  -/
  partial
  def withPSpec [Inhabited (m a)] [Nonempty (m a)]
    (isGoal : Bool) (th : Expr) (k : PSpecDesc → m a) :
    m a := do
    trace[Progress] "Proposition: {th}"
    -- Dive into the quantified variables and the assumptions
    -- Note that if we analyze a pspec theorem to register it in a database (i.e.
    -- a discrimination tree), we need to introduce *meta-variables* for the
    -- quantified variables.
    let telescope (k : Array Expr → Expr → m a) : m a :=
      if isGoal then forallTelescope th.consumeMData (fun fvars th => k fvars th)
      else do
        let (fvars, _, th) ← forallMetaTelescope th.consumeMData
        k fvars th
    telescope fun fvars th => do
    trace[Progress] "Universally quantified arguments and assumptions: {fvars}"
    -- Dive into the existentials
    existsTelescope th.consumeMData fun evars th => do
    trace[Progress] "Existentials: {evars}"
    trace[Progress] "Proposition after stripping the quantifiers: {th}"
    -- Take the first conjunct
    let (th, post) ← optSplitConj th.consumeMData
    trace[Progress] "After splitting the conjunction:\n- eq: {th}\n- post: {post}"
    -- Destruct the equality
    let (mExpr, ret) ← destEq th.consumeMData
    trace[Progress] "After splitting the equality:\n- lhs: {mExpr}\n- rhs: {ret}"
    -- Recursively destruct the monadic application to dive into the binds,
    -- if necessary (this is for when we use `withPSpec` inside of the `progress` tactic),
    -- and destruct the application to get the function name
    let rec strip_monad mExpr := do
      mExpr.consumeMData.withApp fun mf margs => do
      trace[Progress] "After stripping the arguments of the monad expression:\n- mf: {mf}\n- margs: {margs}"
      if mf.isConst ∧ mf.constName = ``Bind.bind then do
        -- Dive into the bind
        let fExpr := (margs.get! 4).consumeMData
        -- Recursve
        strip_monad fExpr
      else
        -- No bind
        pure (mExpr, mf, margs)
    let (fArgsExpr, f, args) ← strip_monad mExpr
    trace[Progress] "After stripping the arguments of the function call:\n- f: {f}\n- args: {args}"
    let fLevels ← do
      -- If we are registering a theorem, then the function must be a constant
      if ¬ f.isConst then
        if isGoal then pure []
        else throwError "{f} should be a constant"
      else pure f.constLevels!
    -- *Sanity check* (activated if we are analyzing a theorem to register it in a DB)
    -- Check if some existentially quantified variables
    let _ := do
      -- Collect all the free variables in the arguments
      let allArgsFVars ← args.foldlM (fun hs arg => getFVarIds arg hs) Std.HashSet.empty
      -- Check if they intersect the fvars we introduced for the existentially quantified variables
      let evarsSet : Std.HashSet FVarId := Std.HashSet.empty.insertMany (evars.map (fun (x : Expr) => x.fvarId!))
      let filtArgsFVars := allArgsFVars.toArray.filter (fun var => evarsSet.contains var)
      if filtArgsFVars.isEmpty then pure ()
      else
        let filtArgsFVars := filtArgsFVars.map (fun fvarId => Expr.fvar fvarId)
        throwError "Some of the function inputs are not universally quantified: {filtArgsFVars}"
    -- Return
    trace[Progress] "Function with arguments: {fArgsExpr}";
    let thDesc := {
      fvars := fvars
      evars := evars
      fArgsExpr
      fIsConst := f.isConst
      fLevels
      args := args
      ret := ret
      post := post
    }
    k thDesc
end Methods

def getPSpecFunArgsExpr (isGoal : Bool) (th : Expr) : MetaM Expr :=
  withPSpec isGoal th (fun d => do pure d.fArgsExpr)

/-- The progress attribute -/
structure PSpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name
  deriving Inhabited

private def saveProgressSpecFromThm (ext : DiscrTreeExtension Name) (attrKind : AttributeKind) (thName : Name) :
  AttrM Unit := do
  -- TODO: use the attribute kind
  unless attrKind == AttributeKind.global do
    throwError "invalid attribute 'progress', must be global"
  -- Lookup the theorem
  let env ← getEnv
  -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
  attrIgnoreAuxDef thName (pure ()) do
    trace[Progress] "Registering `progress` theorem for {thName}"
    let thDecl := env.constants.find! thName
    let fKey ← MetaM.run' (do
      trace[Progress] "Theorem: {thDecl.type}"
      -- Normalize to eliminate the let-bindings
      let ty ← normalizeLetBindings thDecl.type
      trace[Progress] "Theorem after normalization (to eliminate the let bindings): {ty}"
      let fExpr ← getPSpecFunArgsExpr false ty
      trace[Progress] "Registering spec theorem for expr: {fExpr}"
      -- Convert the function expression to a discrimination tree key
      DiscrTree.mkPath fExpr)
    let env := ext.addEntry env (fKey, thName)
    setEnv env
    trace[Progress] "Saved the environment"
    pure ()

/- Initiliaze the `progress` attribute. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← mkDiscrTreeExtension `pspecMap
  let attrImpl : AttributeImpl := {
    name := `progress
    descr := "Adds theorems to the `progress` database"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      saveProgressSpecFromThm ext attrKind thName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def PSpecAttr.find? (s : PSpecAttr) (e : Expr) : MetaM (Array Name) := do
  (s.ext.getState (← getEnv)).getMatch e

def PSpecAttr.getState (s : PSpecAttr) : MetaM (DiscrTree Name) := do
  pure (s.ext.getState (← getEnv))

def showStoredPSpec : MetaM Unit := do
  let st ← pspecAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

namespace Test
  /-!
  Making some tests here as models to guide the automation generation of proof terms when lifting theorems in `progress_pure`
  -/
  open Std Result
  def pos_pair : Int × Int := (0, 1)

  theorem pos_pair_is_pos :
    let (x, y) := pos_pair
    x ≥ 0 ∧ y ≥ 0 := by simp [pos_pair]

  theorem lifted_is_pos :
    ∃ x y, toResult pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    Exists.intro x (Exists.intro y (And.intro (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, toResult pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) pos_pair_is_pos

  /- Same as `lifted_is_pos` but making the implicit parameters of the `Exists.intro` explicit:
     this is the important part. -/
  theorem lifted_is_pos' :
    ∃ x y, toResult pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    @Exists.intro Int (fun x_1 => ∃ y_1, ok (x, y) = ok (x_1, y_1) ∧ x_1 ≥ 0 ∧ y_1 ≥ 0)
      x (@Exists.intro Int (fun y_1 => ok (x, y) = ok (x, y_1) ∧ x ≥ 0 ∧ y_1 ≥ 0)
        y (@And.intro (ok (x, y) = ok (x, y)) _ (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, toResult pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) pos_pair_is_pos

  def pos_triple : Int × Int × Int := (0, 1, 2)

  theorem pos_triple_is_pos :
    let (x, y, z) := pos_triple
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 := by simp [pos_triple]

  structure U8 where
    val : Nat

  def overflowing_add (x y : U8) : U8 × Bool := (⟨ x.val + y.val ⟩, x.val + y.val > 255)

  theorem overflowing_add_eq (x y : U8) :
    let z := overflowing_add x y
    if x.val + y.val > 255 then z.snd = true
    else z.snd = false
    :=
    by simp [overflowing_add]

end Test

def reduceProdProjs (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    trace[Utils] "Attempting to reduce: {e}"
    match ← reduceProj? e with
    | none =>
      e.withApp fun fn args =>
      if fn.isConst ∧ (fn.constName! = ``Prod.fst ∨ fn.constName! = ``Prod.snd) ∧ args.size = 3 then
        let pair := args[2]!
        pair.withApp fun fn' args =>
          if fn'.isConst ∧ fn'.constName! = ``Prod.mk ∧ args.size = 4 then
            if fn.constName! = ``Prod.fst then pure (.continue args[2]!)
            else pure (.continue args[3]!)
          else pure (.continue e)
      else pure (.continue e)
    | some e =>
      trace[Utils] "reduced: {e}"
      pure (.continue e)
  transform e (pre := pre)

/-- Given a theorem of type `P x` and a pattern of the shape `∃ y₀ ... yₙ, x = (y₀, ..., yₙ)`,
    introduce a lifted version of the theorem of the shape:
    ```
    ∃ y₀ ... yₙ, toResult x = ok (y₀, ..., yₙ) ∧ P (y₀, ..., yₙ)
    ```

    The output of the function is the name of the new theorem.

    Note that if the pattern is simply `x` (not an existentially quantified equality), this function
    decomposes the type of `x` for as long as it finds a tuple, and introduces one variable per field
    in the tuple.

    For instance, given pattern `some_pair : Int × Int`, the following theorem:
    ```
    P some_pair.fst ∧ Q some_pair.snd
    ```
    gets lifted to:
    ```
    ∃ x y, toResult some_pair = ok (x, y) ∧ P x ∧ Q y
    ```
-/
def liftThm (pat : Syntax) (n : Name) (suffix : String := "progress_spec") : MetaM Name := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let decl := env.constants.find! n
  /- Strip the quantifiers before elaborating the pattern -/
  forallTelescope decl.type.consumeMData fun fvars thm0 => do
  let (pat, _) ← Elab.Term.elabTerm pat none |>.run
  let pat ← instantiateMVars pat
  trace[Progress] "Elaborated pattern: {pat}"
  /- -/
  existsTelescope pat.consumeMData fun _ eqMatch => do
  existsTelescope pat.consumeMData fun _ eqExists => do
  /- Auxiliary helper.

     Given type `α₀ × ... × αₙ`, introduce fresh variables
     `x₀ : α₀, ..., xₙ : αₙ` and call the continuation with those.
  -/
  let withFreshTupleFieldFVars (basename : Name) (ty : Expr) (k : Array Expr → MetaM Name) : MetaM Name := do
    let tys := destProdsType ty
    let tys := List.map (fun (i, ty) => (Name.num basename i, fun _ => pure ty)) (List.enum tys)
    withLocalDeclsD ⟨ tys ⟩ k
  /- Destruct the equality. Note that there may not be a tuple, in which case
     we see the type as a tuple and introduce one variable per field of the tuple
     (and a single variable if it is actually not a tuple). -/
  let tryDestEq basename (eq : Expr) (k : Expr → Expr → MetaM Name) : MetaM Name := do
    match ← destEqOpt eq with
    | some (x, y) => k x y
    | none =>
      withFreshTupleFieldFVars (.str .anonymous basename) (← inferType pat) fun fvars => do
      k pat (← mkProdsVal fvars.toList)
  /- We need to introduce two sets of variables:
     - one for variables which will be introduced by the outer match
     - another for variables which will be bound by the ∃ quantifiers -/
  tryDestEq "x" eqMatch fun pat decompPatMatch => do
  tryDestEq "y" eqExists fun _ decompPatExists => do
  trace[Progress] "Decomposed equality: {pat}, {decompPatMatch}, {decompPatExists}"
  /- The decomposed patterns should be tuple expressions: decompose them further into lists of variables -/
  let fvarsMatch : Array Expr := ⟨ destProdsVal decompPatMatch ⟩
  let fvarsExists : Array Expr := ⟨ destProdsVal decompPatExists ⟩
  trace[Progress] "Fvars: {fvarsMatch}, {fvarsExists}"
  /- Small helper that we use to substitute the pattern in the original theorem -/
  let mkPureThmType (npat : Expr) : MetaM Expr := do
    let thm ← mapVisit (fun _ e => do if e == pat then pure npat else pure e) thm0
    /- Reduce a bit the expression, but in a controlled manner, to make it cleaner -/
    let thm ← normalizeLetBindings thm
    reduceProdProjs thm
  /- Introduce the binder for the pure theorem - it will be bound outside of the ∃ but we need to use it
     right now to generate an expression of type:
     ```
     toResult ... = ok x ∧
     P x -- HERE
     ```
  -/
  let pureThmType ← mkPureThmType decompPatMatch
  let pureThmName ← mkFreshUserName (.str .anonymous "pureThm")
  withLocalDeclD pureThmName pureThmType fun pureThm => do
  /- Introduce the equality -/
  let okDecompPat ← mkAppM ``Std.Result.ok #[decompPatMatch]
  let eqExpr ← mkEqRefl okDecompPat
  let thm ← mkAppM ``And.intro #[eqExpr, pureThm]
  trace[Progress] "Theorem after introducing the lifted equality: {thm}\n  :\n{← inferType thm}"
  /- Auxiliary helper which computes the type of the (intermediate) theorems when adding the existentials.

     Given `toResultArg`, `xl0` and `xl1`, generates:
     ```
     ∃ $xl1,
     toResult $toResultArg = ($xl0 ++ $xl1) ∧
     P ($xl0 ++ $xl1)
     ```
   -/
  let mkThmType (toResultArg : Expr) (xl0 : List Expr) (xl1 : List Expr) : MetaM Expr := do
    trace[Progress] "mkThmType:\n- {toResultArg}\n- {xl0}\n- {xl1}"
    let npatExists ← mkProdsVal (xl0 ++ xl1)
    /- Update the theorem statement to replace the pattern with the decomposed pattern -/
    let thmType ← mkPureThmType npatExists
    trace[Progress] "mkThmType: without lifted equality: {thmType}"
    let toResultPat ← mkAppM ``Std.toResult #[toResultArg]
    let okDecompPat ← mkAppM ``Std.Result.ok #[npatExists]
    let eqType ← mkEq toResultPat okDecompPat
    let thmType := mkAnd eqType thmType
    trace[Progress] "mkThmType: after lifting equality: {thmType}"
    /- Introduce the existentials, only for the suffix of the list of variables -/
    let thmType ← List.foldrM (fun fvar thmType => do
        let p ← mkLambdaFVars #[fvar] thmType
        mkAppM ``Exists #[p]
        ) thmType xl1
    trace[Progress] "mkThmType: after adding the existentials: {thmType}"
    pure thmType
  /- Introduce the existentials -/
  let rec introExists (xl0 xl1 : List (Expr × Expr)) : MetaM Expr := do
    match xl1 with
    | [] => pure thm
    | fvarPair :: xl1 =>
      let thm ← introExists (fvarPair :: xl0) xl1
      let (fvarMatch, fvarExists) := fvarPair
      let α ← inferType fvarMatch
      let thmType ← mkThmType decompPatMatch (fvarExists :: (List.unzip xl0).fst).reverse (List.unzip xl1).snd
      let p ← mkLambdaFVars #[fvarExists] thmType
      let x := fvarMatch
      let h := thm
      trace[Progress] "introExists: about to insert existential:\n- α: {α}\n- p: {p}\n- x: {x}\n- h: {h}"
      let thm ← mkAppOptM ``Exists.intro #[α, p, x, h]
      trace[Progress] "introExists: resulting theorem:\n{thm}\n  :\n{← inferType thm}"
      pure thm
  let thm ← introExists [] (List.zip fvarsMatch.toList fvarsExists.toList)
  trace[Progress] "Theorem after introducing the existentials: {thm} :\n{← inferType thm}"
  /- Introduce the λ which binds the pure theorem -/
  let thm ← mkLambdaFVars #[pureThm] thm
  trace[Progress] "Theorem after introducing the lambda: {thm} :\n{← inferType thm}"
  /- Introduce the matches -/
  let thm ← mkProdsMatch fvarsMatch.toList thm
  trace[Progress] "Theorem after introducing the matches: {thm} :\n{← inferType thm}"
  /- Apply to the scrutinee (which is the pattern provided by the user): `mkProdsMatch` generates
     a lambda expression, where the bound value is the scrutinee we should match over. -/
  let thm := mkApp thm pat
  trace[Progress] "Theorem after introducing the scrutinee: {thm} :\n{← inferType thm}"
  /- Apply to the pure theorem (the expression inside the match is a function which expects to receive this theorem) -/
  let pureThm := mkAppN (.const decl.name (List.map Level.param decl.levelParams)) fvars
  let thm := mkAppN thm #[pureThm]
  trace[Progress] "Theorem after introducing the matches and the app: {thm} :\n{← inferType thm}"
  let thm ← mkLambdaFVars fvars thm
  /- Prepare the theorem type -/
  let thmType ← do
    let thmType ← mkThmType pat [] fvarsExists.toList
    let thmType ← mkForallFVars fvars thmType
    pure thmType
  trace[Progress] "Final theorem: {thm}\n  :\n{thmType}"
  /- Save the auxiliary theorem -/
  let name := Name.str decl.name suffix
  let auxDecl : TheoremVal := {
    name
    levelParams := decl.levelParams
    type := thmType
    value := thm
  }
  addDecl (.thmDecl auxDecl)
  /- -/
  pure name

local elab "#progress_pure_lift_thm" id:ident pat:term : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  let _ ← liftThm pat name)

namespace Test
  #progress_pure_lift_thm pos_pair_is_pos (∃ x y, pos_pair = (x, y))

  #progress_pure_lift_thm pos_triple_is_pos pos_triple

  #progress_pure_lift_thm overflowing_add_eq (overflowing_add x y)
end Test


-- The ident is the name of the saturation set, the term is the pattern.
syntax (name := progress_pure) "progress_pure" term : attr

def elabProgressPureAttribute (stx : Syntax) : AttrM (TSyntax `term) :=
  withRef stx do
    match stx with
    | `(attr| progress_pure $pat) => do
      pure pat
    | _ => throwUnsupportedSyntax

/-- The progress pure attribute -/
structure ProgressPureSpecAttr where
  attr : AttributeImpl
  deriving Inhabited


/- Initiliaze the `progress_pure` attribute, which lifts lemmas about pure functions to
   `progress` lemmas.

   For instance, if we annotate the following theorem with `progress_pure` (note the `let` binding
   which must be at the beginning of the theorem statement):
   ```
   @[progress_pure]
   theorem U32.wrapping_add_eq (x y : U32) :
    let z := wrapping_add x y
    z.bv = x.bv + y.bv
   ```
   `progress_pure` introduces the following intermediate definition:
   ```
   @[progress_pure]
   theorem U32.wrapping_add_eq.progress_spec (x y : U32) :
    ∃ z, ↑(wrapping_add x y) = ok z ∧
    z.bv = x.bv + y.bv
   ```
 -/
initialize pspecPureAttribute : ProgressPureSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `progress_pure
    descr := "Adds lifted version of pure theorems to the `progress_pure` databse"
    add := fun thName stx attrKind => do
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'progress_pure', must be global"
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        trace[Progress] "Registering pure `progress` theorem for {thName}"
        -- Elaborate the pattern
        trace[Saturate.attribute] "Syntax: {stx}"
        let pat ← elabProgressPureAttribute stx
        -- Introduce the lifted theorem
        let liftedThmName ← MetaM.run' (liftThm pat thName)
        -- Save the lifted theorem to the `progress` database
        saveProgressSpecFromThm pspecAttr.ext attrKind liftedThmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

end Progress

end Aeneas
