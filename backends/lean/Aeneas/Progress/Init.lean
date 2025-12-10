import Lean
import AeneasMeta.Utils
import Aeneas.Std.Primitives
import AeneasMeta.Extensions
import Aeneas.Progress.Trace
import Aeneas.Std.WP

namespace Aeneas

namespace Progress

open Lean Elab Term Meta
open Utils Extensions

/-!
# Attribute: `progress_simps`
-/

/-- The `progress_simps` simp attribute. -/
initialize progressSimpExt : SimpExtension ←
  registerSimpAttr `progress_simps "\
    The `progress_simps` attribute registers simp lemmas to be used by `progress`
    to simplify the goal before looking up lemmas. If often happens that some
    monadic function calls, if given some specific parameters (in particuler,
    specific trait instances), can be simplified to far simpler functions: this
    is the main purpose of this attribute."

/-!
# Attribute: `progress_pre_simps`
-/

/-- The `progress_pre_simps` simp attribute. -/
initialize progressPreSimpExt : SimpExtension ←
  registerSimpAttr `progress_pre_simps "\
    The `progress_pre_simps` attribute registers simp lemmas to be used by `progress`
    when solving preconditions by means of the simplifier."

/-!
# Attribute: `progress_post_simps`
-/

/-- The `progress_post_simps` simp attribute. -/
initialize progressPostSimpExt : SimpExtension ←
  registerSimpAttr `progress_post_simps "\
    The `progress_post_simps` attribute registers simp lemmas to be used by `progress`
    to post-process post-conditions after introducing them in the context."

/-! # Attribute: `progress` -/

structure ProgressSpecDesc where
  -- The universally quantified variables and preconditions, as mvars
  preconds : Array MVarId
  -- The existentially quantified variables
  evars : Array FVarId
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
  postcond? : Option Expr

section Methods
  variable {m} [MonadControlT MetaM m] [Monad m]
  variable {a : Type}

  /- Auxiliary helper.

     Given type `α₀ × ... × αₙ`, introduce fresh variables
     `x₀ : α₀, ..., xₙ : αₙ` and call the continuation with those.
  -/
  def withFreshTupleFieldFVars [Inhabited a] (basename : Name) (ty : Expr) (k : Array Expr → m a) : m a := do
    let tys := destProdsType ty
    let tys := List.map (fun (ty, i) => (Name.num basename i, fun _ => pure ty)) (List.zipIdx tys)
    withLocalDeclsD ⟨ tys ⟩ k
end Methods

/- Analyze a goal or a progress theorem to decompose its arguments.

  ProgressSpec theorems should be of the following shape:
  ```
  ∀ x1 ... xn, H1 → ... Hn → spec (f x1 ... xn) P
  ```
-/
def getProgressSpecFunArgsExpr (ty : Expr) :
  MetaM Expr := do
  let ty := ty.consumeMData
  unless ← isProp ty do
    throwError "Expected a proposition, got {←inferType ty}"
  -- ty == ∀ xs, spec (f x1 ... xn) P
  let (xs, xs_bi, ty₂) ← forallMetaTelescope ty
  trace[Progress] "Universally quantified arguments and assumptions: {xs}"
  -- ty₂ == spec (f x1 ... xn) P
  let (spec?, args) := ty₂.consumeMData.withApp (fun f args => (f, args))
  if h: spec?.isConstOf ``Std.WP.spec ∧ args.size = 3
  then pure args[1] -- this is `f x1 ... xn`
  else throwError "Expected to be a `spec (f x1 ... xn) P`, got {ty₂}"

/- Analyze a goal comp

   If comp = bind m k then return true and m
   Else return false and comp
-/
def getFirstBind (comp : Expr) : MetaM (Bool × Expr) := do
  let (bind?, args) := comp.consumeMData.withApp (fun f args => (f, args))
  if h: bind?.isConstOf ``Std.bind ∧ args.size = 4
  then pure (true, args[2])
  else pure (false, comp)

structure Rules where
  rules : DiscrTree Name
  /- We can't remove keys from a discrimination tree, so to support
     local rules we keep a set of deactivated rules (rules which have
     come out of scope) on the side -/
  deactivated : Std.HashSet Name
deriving Inhabited

def Rules.empty : Rules := ⟨ DiscrTree.empty, Std.HashSet.emptyWithCapacity ⟩

def Extension := SimpleScopedEnvExtension (DiscrTreeKey × Name) Rules
deriving Inhabited

def Rules.insert (r : Rules) (kv : Array DiscrTree.Key × Name) : Rules :=
  { rules := r.rules.insertCore kv.fst kv.snd,
    deactivated := r.deactivated.erase kv.snd }

def Rules.erase (r : Rules) (k : Name) : Rules :=
  { r with deactivated := r.deactivated.insert k }

def mkExtension (name : Name := by exact decl_name%) :
  IO Extension :=
  registerSimpleScopedEnvExtension {
    name        := name,
    initial     := Rules.empty,
    addEntry    := Rules.insert,
  }

/-- The progress attribute -/
structure ProgressSpecAttr where
  attr : AttributeImpl
  ext  : Extension
  deriving Inhabited

private def saveProgressSpecFromThm (ext : Extension) (attrKind : AttributeKind) (thName : Name) :
  AttrM Unit := do
  -- Lookup the theorem
  let env ← getEnv
  -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
  attrIgnoreAuxDef thName (pure ()) do
    trace[Progress] "Registering `progress` theorem for {thName}"
    let some thDecl := env.findAsync? thName
      | throwError "Could not find theorem {thName}"
    let type := thDecl.sig.get.type
    let fKey ← MetaM.run' (do
      trace[Progress] "Theorem: {type}"
      -- Normalize to eliminate the let-bindings
      let ty ← normalizeLetBindings type
      trace[Progress] "Theorem after normalization (to eliminate the let bindings): {ty}"
      let fExpr ← getProgressSpecFunArgsExpr ty
      trace[Progress] "Registering spec theorem for expr: {fExpr}"
      -- Convert the function expression to a discrimination tree key
      DiscrTree.mkPath fExpr)
    -- Save the entry
    ScopedEnvExtension.add ext (fKey, thName) attrKind
    trace[Progress] "Saved the entry"
    pure ()

/- Initiliaze the `progress` attribute. -/
initialize progressAttr : ProgressSpecAttr ← do
  let ext ← mkExtension `progressMap
  let attrImpl : AttributeImpl := {
    name := `progress
    descr := "Adds theorems to the `progress` database"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      saveProgressSpecFromThm ext attrKind thName
    erase := fun thName => do
      let s := ext.getState (← getEnv)
      let s := s.erase thName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def ProgressSpecAttr.find? (s : ProgressSpecAttr) (e : Expr) : MetaM (Array Name) := do
  let state := s.ext.getState (← getEnv)
  let rules ← state.rules.getMatch e
  pure (rules.filter (fun th => th ∉ state.deactivated))

def ProgressSpecAttr.getState (s : ProgressSpecAttr) : MetaM Rules := do
  pure (s.ext.getState (← getEnv))

def showStoredProgressThms : MetaM Unit := do
  let st ← progressAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st.rules}, {st.deactivated.toArray}"
  IO.println s

/-! # Attribute: `progress_pure` -/

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

/-
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
def liftThm (stx pat : Syntax) (n : Name) (suffix : String := "progress_spec") : MetaM Name := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let some decl := env.findAsync? n
    | throwError "Could not find theorem {n}"
  let sig := decl.sig.get
  /- Strip the quantifiers before elaborating the pattern -/
  forallTelescope sig.type.consumeMData fun fvars thm0 => do
  let (pat, _) ← Elab.Term.elabTerm pat none |>.run
  trace[Progress] "Elaborated pattern: {pat}"
  /- -/
  existsTelescope pat.consumeMData fun _ eqMatch => do
  existsTelescope pat.consumeMData fun _ eqExists => do
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
  let pureThm := mkAppN (.const decl.name (List.map Level.param sig.levelParams)) fvars
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
    levelParams := sig.levelParams
    type := thmType
    value := thm
  }
  addDecl (.thmDecl auxDecl)
  /- Save the range -/
  addDeclarationRangesFromSyntax name stx
  /- -/
  pure name

/-!
# Command: `#progress_pure_lift_thm`
-/

local elab "#progress_pure_lift_thm" id:ident pat:term : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  let _ ← liftThm id pat name)

namespace Test
  #progress_pure_lift_thm pos_pair_is_pos (∃ x y, pos_pair = (x, y))

  #progress_pure_lift_thm pos_triple_is_pos pos_triple

  def pos_triple_is_pos' := pos_triple_is_pos
  #progress_pure_lift_thm pos_triple_is_pos' (∃ z, pos_triple = z)

  #progress_pure_lift_thm overflowing_add_eq (overflowing_add x y)
end Test
-/

/-!
# Attribute: `#progress_pure`
-/

/- The ident is the name of the saturation set, the term is the pattern. -/
syntax (name := progress_pure) "progress_pure" term : attr

/-partial def parseCommaSeparated (stx : Syntax) : TermElabM (Array Syntax) := do
  let rec go (stx : Syntax) (acc : Array Syntax) : TermElabM (Array Syntax) := do
    match stx with
    | `(term| ($x, $xs)) => go `(term| $xs) (acc.push x)
    | _ => pure (acc.push stx)
  go stx #[]-/

partial def parseCommaSeparated (stx : Syntax) (acc : Array Syntax := #[]) : TermElabM (Array Syntax) := do
  trace[Progress] "parsing comma separated: {stx} with acc: {acc}"
  let args := stx.getArgs
  trace[Progress] "args.size: {args.size}"
  -- TODO: check if ident
  if args.size = 0 then pure acc
  else if h: args.size = 1 then pure (acc.push args[0])
  else if h: args.size = 3 then
    let arg0 := args[0]
    let arg1 := args[1]
    let arg2 := args[2]
    trace[Progress] "parsing comma separated:\n- arg0: {arg0}\n- arg1: {arg1}\n- arg2: {arg2}"
    let isComma ← do
      match arg1 with
      | .atom _ "," => pure true
      | _ => pure false
    if isComma then
      trace[Progress] "arg1 is a comma"
      parseCommaSeparated arg2 (acc.push arg0)
    else
      -- Maybe we have a tuple: we simply return the current syntax
      trace[Progress] "arg1 is not a comma"
      pure (acc.push stx)
  else if h: args.size = 2 then
    let arg0 := args[0]
    let arg1 := args[1]
    trace[Progress] "parsing comma separated:\n- arg0: {arg0}\n- arg1: {arg1}"
    /-let isComma :=
      match arg1 with
      | .atom _ "," => true
      | _ => false
    if isComma then throwError "Unsupported comma separated syntax: {stx}, unexpected trailing ','"
    pure (acc.push arg0)-/
    throwError "TODO"
  else throwError "Unsupported comma separated syntax: {stx}"

/-- Given a pattern which decomposes a tuple or a struct (`(x, y, z)` or `⟨x, z, z⟩`, `((x, y), z, ⟨a, b⟩), etc.)`,
  return the list of identifiers appearing inside the pattern. -/
partial def elabProgressPurePattern (stx : Syntax) : TermElabM (Array Ident) := do
  trace[Progress] "syntax: {stx}"
  -- Check if this is an identifier
  match stx with
  | `(term| $name:ident) => pure #[name]
  |_ =>
  let args := stx.getArgs
  trace[Progress] "args.size: {args.size}"

  -- Check if the syntax is `⟨ ... ⟩` or `( ... )`
  if args.size = 0 then throwError "Unsupported pattern syntax: empty syntax"

  /-if h: args.size = 1 then
    -- Check if this is an identifier
    match args[0] with
    | `(term| $name:ident) => throwError "Unexpected" pure #[name]
    |_ => throwError "Unsupported pattern syntax: expected an identifier: {stx}"-/

  if h: args.size = 3 then
    -- It should be a tuple: decompose it
    let arg0 := args[0]
    let arg1 := args[1]
    let arg2 := args[2]
    let isTuple :=
      match arg0, arg2 with
      | .atom _ "⟨", .atom _ "⟩"
      | .node _ _ #[.atom _ "(", _], .atom _ ")" => true
      | _, _ => false
    if not isTuple then throwError "Unsupported pattern syntax: {stx}"
    let args ← parseCommaSeparated arg1
    trace[Progress] "parsed args: {args}"
    -- Recursively decompose
    let xs ← args.mapM elabProgressPurePattern
    -- Flatten
    pure xs.flatten
    /-match arg1 with
    | `($xs,*) => do
      throwError "TODO"
      /-let xs := xs.getElems.mapM fun
        | `(binderIdent| $name:ident) => pure name
        | _ => throwError "Unexpected syntax in pattern"
      -- Recursive calls:
      let xs ← (#[x0] ++ xs).mapM elabProgressPurePattern
      -- Flatten
      pure xs.flatten-/
    |_ => throwError "Unsupported pattern syntax: {stx}"-/
  else throwError "Unsupported pattern syntax: {stx}"
  /-trace[Progress] "args: {args}"
  match stx with
  | `(term| ⟨$xs,*⟩) => do
    let xs ← xs.getElems.mapM fun
      | `(binderIdent| $name:ident) => pure name
      | _ => throwError "Unexpected syntax in pattern"
    -- Recursive calls:
    let xs ← xs.mapM elabProgressPurePattern
    -- Flatten
    pure xs.flatten
  /-| `(term| ⟨$x0, $xs,*⟩) => do
    let xs ← xs.getElems.mapM fun
      | `(binderIdent| $name:ident) => pure name
      | _ => throwError "Unexpected syntax in pattern"
    -- Recursive calls:
    let xs ← (#[x0] ++ xs).mapM elabProgressPurePattern
    -- Flatten
    pure xs.flatten-/
  --| `(term| ($x0)) => do elabProgressPurePattern x0
  | `(term| ($x0, $xs,*)) => do
    let xs ← xs.getElems.mapM fun
      | `(binderIdent| $name:ident) => pure name
      | _ => throwError "Unexpected syntax in pattern"
    -- Recursive calls:
    let xs ← (#[x0] ++ xs).mapM elabProgressPurePattern
    -- Flatten
    pure xs.flatten
  | `(term| ()) => pure #[]
  | `(term| $name:ident) => pure #[name]
  | _ =>
    throwError "Unsupported pattern syntax"-/

open Lean Elab Command Term in
elab "#elab_pattern" pat:term : command => do
  let ids ← liftTermElabM (elabProgressPurePattern pat)
  trace[Progress] "Identifiers: {ids.toList}"
  pure ()

example (x y : Nat) := (x, y)
example (x : Nat × Nat) := let ⟨ y, z ⟩ := x; y + z

#check Syntax
#check mkFreshUserName
#check matchMatcherApp?
#check isMatcherApp

set_option trace.Progress true
set_option pp.rawOnError true

#elab_pattern ⟨⟩
#elab_pattern ()

#elab_pattern ⟨x⟩
#elab_pattern (x)
#elab_pattern (x, y)
#elab_pattern (x, y, z)
#elab_pattern ((x, w), y, (a, b, c))
--#elab_pattern ⟨x, y⟩

#check MVarId.introN

/-- We desugar patterns of the shape `foo = (x, y, z)` to `∃ x y z, foo = (x, y, z)` in order to bind
    the variables introduced in the right-hand side, allowing us to elaborate the patterns. -/
def elabProgressPureAttribute (stx : Syntax) : AttrM (TSyntax `term × Option (Array Ident)) :=
  withRef stx do
    match stx with
    | `(attr| progress_pure $x = $pat) => do
      let ids ← elabProgressPurePattern pat
      pure (x, some ids)
    | `(attr| progress_pure $pat) => do pure (pat, none)
    | _ => throwUnsupportedSyntax

/-- The progress pure attribute -/
structure ProgressPureSpecAttr where
  attr : AttributeImpl
  deriving Inhabited

/- Initialize the `progress_pure` attribute, which lifts lemmas about pure functions to
   `progress` lemmas.

   For instance, if we annotate the following theorem with `progress_pure`:
   ```lean
   @[progress_pure wrapping x y]
   theorem U32.wrapping_add_eq (x y : U32) :
    (wrapping_add x y).bv = x.bv + y.bv
   ```
   `progress_pure` performs operations which are equivalent to introducing the following lemma:
   ```lean
   @[progress]
   theorem U32.wrapping_add_eq.progress_spec (x y : U32) :
    ↑(wrapping_add x y) ⦃⇓z => z.bv = x.bv + y.bv⦄
   ```

   Note that it is possible to control how the output variable is decomposed in the generated lemma
   by writing an equality in the pattern we want to abstract over.
   For instance if we write:
   ```lean
   @[progress_pure pos_pair = (x, y)]
   theorem pos_pair_is_pos : pos_pair.fst ≥ 0 ∧ pos_pair.snd ≥ 0
   ```
   we get:
   ```lean
   @[progress]
   theorem pos_pair_is_pos.progress_spec :
    ↑pos_pair ⦃ ⇓(x, y) => x ≥ 0 ∧ y ≥ 0 ⦄
   ```

   Similarly if we write:
   ```lean
   @[progress_pure pos_pair = z]
   theorem pos_pair_is_pos : pos_pair.fst ≥ 0 ∧ pos_pair.snd ≥ 0
   ```
   we get:
   ```lean
   @[progress]
   theorem pos_pair_is_pos.progress_spec :
    ↑pos_pair ⦃⇓z => z.fst ≥ 0 ∧ z.fst ≥ 0⦄
   ```

   If we don't put an equality in the pattern, `progress_pure` will introduce one variable
   per field in the type of the pattern, if it is a tuple.
 -/
initialize progressPureAttribute : ProgressPureSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `progress_pure
    descr := "Adds lifted version of pure theorems to the `progress_pure` database"
    add := fun thName stx attrKind => do
      -- Lookup the theorem
      let env ← getEnv
      -- -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      -- attrIgnoreAuxDef thName (pure ()) do
      --   -- Elaborate the pattern
      --   let pat ← elabProgressPureAttribute stx
      --   -- Introduce the lifted theorem
      --   let liftedThmName ← MetaM.run' (liftThm stx pat thName)
      --   -- Save the lifted theorem to the `progress` database
      --   saveProgressSpecFromThm progressAttr.ext attrKind liftedThmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

syntax (name := progressPat) term (" = " term)? : term

/-! # Attribute: `progress_pure_def` -/

/- The ident is the name of the saturation set, the term is the pattern. -/
syntax (name := progress_pure_def) "progress_pure_def" (term)? : attr

def elabProgressPureDefAttribute (stx : Syntax) : AttrM (Option Syntax) := do
  if stx[1].isNone then pure none
  else pure (stx[1])

/-- The progress pure def attribute -/
structure ProgressPureDefSpecAttr where
  attr : AttributeImpl
  deriving Inhabited

def mkProgressPureDefThm (stx : Syntax) (pat : Option Syntax) (n : Name) (suffix : String := "progress_spec") : MetaM Name := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let some decl := env.findAsync? n
    | throwError "Could not find theorem {n}"
  let sig := decl.sig.get
  /- Strip the quantifiers before elaborating the pattern -/
  forallTelescope sig.type.consumeMData fun fvars _ => do
  let declTerm := mkAppN (.const decl.name (List.map Level.param sig.levelParams)) fvars
  /- Elaborate the pattern, if there is -/
  let elabDecomposePat (basename : String) (k : Expr → Array Expr → MetaM Name) : MetaM Name := do
    match pat with
    | none =>
      withFreshTupleFieldFVars (.str .anonymous basename) (← inferType declTerm) fun fvars => do
      let pat ← mkProdsVal fvars.toList
      k pat fvars
    | some pat =>
      /- Elaborate the pattern -/
      let (pat, _) ← Elab.Term.elabTerm pat none |>.run
      trace[Progress] "Elaborated pattern: {pat}"
      /- Introduce the existentials -/
      existsTelescope pat.consumeMData fun fvarsExists eq => do
      /- Destruct the equality -/
      let (lhs, rhs) ← destEq eq
      /- Sanity check: the lhs should be equal to the definition -/
      assert! (lhs == declTerm)
      /- -/
      k rhs fvarsExists
  /- We need to introduce two sets of variables:
     - one for the variables bound at the external case
     - one for the variables bound in the existential quantifiers
   -/
  elabDecomposePat "x" fun decompPatMatch fvarsMatch => do
  elabDecomposePat "y" fun _ fvarsExists => do
  /- Introduce the lifted and pure equalities -/
  let liftedEq ← do
    let okDecompPat ← mkAppM ``Std.Result.ok #[decompPatMatch]
    mkEqRefl okDecompPat
  let pureEq ← mkEqRefl decompPatMatch
  let thm ← mkAppM ``And.intro #[liftedEq, pureEq]
  trace[Progress] "Theorem after introducing the lifted and pure equalities: {thm}\n  :\n{← inferType thm}"
  /- Auxiliary helper which computes the type of the (intermediate) theorems when adding the existentials.

     Given `toResultArg`, `xl0` and `xl1`, generates:
     ```
     ∃ $xl1,
     toResult $toResultArg = ($xl0 ++ $xl1) ∧
     ($xl0 ++ $xl1) = $toResultArg
     ```
   -/
  let mkThmType (toResultArg : Expr) (xl0 : List Expr) (xl1 : List Expr) : MetaM Expr := do
    trace[Progress] "mkThmType:\n- {toResultArg}\n- {xl0}\n- {xl1}"
    let npatExists ← mkProdsVal (xl0 ++ xl1)
    let liftedEqTy ←
      mkAppM ``Eq #[← mkAppM ``Std.toResult #[toResultArg], ← mkAppM ``Std.Result.ok #[npatExists]]
    let pureEqTy ← mkAppM ``Eq #[npatExists, toResultArg]
    let thmType := mkAnd liftedEqTy pureEqTy
    trace[Progress] "mkThmType: conjunction: {thmType}"
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
  /- Introduce the matches -/
  let thm ← mkProdsMatch fvarsMatch.toList thm
  trace[Progress] "Theorem after introducing the matches: {thm} :\n{← inferType thm}"
  /- Apply to the scrutinee (which is the pattern provided by the user): `mkProdsMatch` generates
     a lambda expression, where the bound value is the scrutinee we should match over. -/
  let thm := mkApp thm declTerm
  trace[Progress] "Theorem after introducing the scrutinee: {thm} :\n{← inferType thm}"
  let thm ← mkLambdaFVars fvars thm
  /- Prepare the theorem type -/
  let thmType ← do
    let thmType ← mkThmType declTerm [] fvarsExists.toList
    let thmType ← mkForallFVars fvars thmType
    pure thmType
  trace[Progress] "Final theorem: {thm}\n  :\n{thmType}"
  /- Save the auxiliary theorem -/
  let name := Name.str decl.name suffix
  let auxDecl : TheoremVal := {
    name
    levelParams := sig.levelParams
    type := thmType
    value := thm
  }
  addDecl (.thmDecl auxDecl)
  /- Save the range -/
  addDeclarationRangesFromSyntax name stx
  /- -/
  pure name

local elab "#progress_pure_def" id:ident pat:(term)? : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do pure ()
  -- let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  -- let name := cs.constName!
  -- let _ ← mkProgressPureDefThm id pat name
  )

namespace Test
  def wrapping_add (x y : U8) : U8 := ⟨ x.val + y.val ⟩

  #progress_pure_def overflowing_add (∃ z, overflowing_add x y = z)
  #elab overflowing_add.progress_spec
  #check overflowing_add.progress_spec

  #progress_pure_def wrapping_add

  --#elab wrapping_add.progress_spec
end Test

/- Initialize the `progress_pure_def` attribute, which automatically generates
   progress lemams for pure definitions.

   For instance, if we annotate the following definition with `progress_pure_def`:
   ```
   @[progress_pure_def]
   def wrapping_add (x y : U32) : U32 := ...
   ```
   `progress_pure_def` performs operations which are equivalent to introducing the following lemma:
   ```
   @[progress]
   theorem wrapping_add.progress_spec (x y : U32) :
    ∃ z, ↑(wrapping_add x y) = ok z ∧
    z = wrapping_add x y
   ```

   Note that `progress_pure_def` takes a,n
 -/
initialize progressPureDefAttribute : ProgressPureDefSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `progress_pure_def
    descr := "Automatically generate `progress` theorems for pure definitions"
    add := fun declName stx attrKind => do
      -- Lookup the theorem
      let env ← getEnv
      -- -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      -- attrIgnoreAuxDef declName (pure ()) do
      --   -- Elaborate the pattern
      --   trace[Saturate.attribute] "Syntax: {stx}"
      --   let pat ← elabProgressPureDefAttribute stx
      --   -- Introduce the lifted theorem
      --   let thmName ← MetaM.run' (mkProgressPureDefThm stx pat declName)
      --   -- Save the lifted theorem to the `progress` database
      --   saveProgressSpecFromThm progressAttr.ext attrKind thmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

end Progress

end Aeneas
