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

theorem spec_toResult {α : Type} (x : α) (P : α → Prop) (h : P x) :
  Std.WP.spec (Std.toResult x) P := by
  simp [Std.toResult]
  apply h

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
    ```lean
    spec (toResult x) (fun z => ∃ y₀ ... yₙ, z = (y₀, ..., yₙ) ∧ P (y₀, ..., yₙ))
    ```
    that is, using syntactic sugar:
    ```lean
    (toResult x) ⦃ fun z => ∃ y₀ ... yₙ, z = (y₀, ..., yₙ) ∧ P (y₀, ..., yₙ) ⦄
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
    (toResult some_pair) ⦃ fun z => z = (x, y) ∧ P x ∧ Q y ⦄
    ```
-/
def liftToThm (stx : Syntax) (pat : Option Syntax) (n : Name)
  (mkPat : Array Expr → Expr → MetaM Expr)
  /- Receives:
    - the type of the definition/theorem after stripping the quantifiers
    - the pattern
    - the new pattern (can be `(y₀, ..., yₙ)` for instance)
    - the parameters of the definition

    Should generate the `P (y₀, ..., yₙ)`)
   -/
  (mkPred : Expr → Expr → Expr → Array Expr → MetaM Expr)
  /- Should generate a proof term of type `P x` -/
  (mkPredProofTerm : Expr → Expr → Array Expr → MetaM Expr)
  (suffix : String := "progress_spec") : MetaM Name := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let some decl := env.findAsync? n
    | throwError "Could not find declaration {n}"
  let sig := decl.sig.get
  /- Strip the quantifiers *before* elaborating the pattern -/
  forallTelescope sig.type.consumeMData fun fvars thm0 => do
  let pat ← do
    match pat with
    | none => mkPat fvars thm0
    | some pat => do
      pure ((← Elab.Term.elabTerm pat none |>.run).fst)
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
  trace[Progress] "Decomposed patterns: pat: {pat}, decompPatMatch: {decompPatMatch}"
  trace[Progress] "Decomposed equality: {pat}, {decompPatMatch}, {decompPatExists}"
  /- The decomposed patterns should be tuple expressions: decompose them further into lists of variables -/
  let fvarsMatch : Array Expr := ⟨ destProdsVal decompPatMatch ⟩
  let fvarsExists : Array Expr := ⟨ destProdsVal decompPatExists ⟩
  trace[Progress] "Fvars: {fvarsMatch}, {fvarsExists}"
  /- Small helper that we use to substitute the pattern in the original theorem -/
  let mkPred (npat : Expr) : MetaM Expr := mkPred thm0 pat npat fvars
  /- Introduce the binder for the pure theorem - it will be bound outside of the ∃ but we need to use it
    right now to generate an expression of type:
    ```
    pat = (x₁, ...) ∧
    P (x₁, ...) -- HERE
    ```
  -/
  let pureThmType ← mkPred decompPatMatch
  let pureThmName ← mkFreshUserName (.str .anonymous "pureThm")
  withLocalDeclD pureThmName pureThmType fun pureThm => do
  /- Introduce the equality -/
  let okDecompPat := decompPatMatch -- mkAppM ``Std.Result.ok #[decompPatMatch]
  let eqExpr ← mkEqRefl okDecompPat
  let thm ← mkAppM ``And.intro #[eqExpr, pureThm]
  trace[Progress] "Theorem after introducing the lifted equality: {thm}\n  :\n{← inferType thm}"
  /- Auxiliary helper which computes the type of the (intermediate) theorems when adding the existentials.

    Given `pat`, `xl0` and `xl1`, generates:
    ```
    ∃ $xl1,
    $pat = ($xl0 ++ $xl1) ∧
    P ($xl0 ++ $xl1)
    ```
  -/
  let mkThmType (pat : Expr) (xl0 : List Expr) (xl1 : List Expr) : MetaM Expr := do
    trace[Progress] "mkThmType:\n- {pat}\n- {xl0}\n- {xl1}"
    let npatExists ← mkProdsVal (xl0 ++ xl1)
    /- Update the theorem statement to replace the pattern with the decomposed pattern -/
    let thmType ← mkPred npatExists
    trace[Progress] "mkThmType: without lifted equality: {thmType}"
    let eqType ← mkEq pat npatExists
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
  let thm ←
    withTraceNode `Progress (fun _ => pure m!"introExists") do
    introExists [] (List.zip fvarsMatch.toList fvarsExists.toList)
  trace[Progress] "Theorem after introducing the existentials: {thm} :\n{← inferType thm}"
  /- Introduce the λ which binds the pure theorem -/
  let thm ← mkLambdaFVars #[pureThm] thm
  trace[Progress] "Theorem after introducing the lambda: {thm} :\n{← inferType thm}"
  /- Introduce the matches -/
  let thm ←
    withTraceNode `Progress (fun _ => pure m!"mkProdsMatch") do
    mkProdsMatch fvarsMatch.toList thm
  trace[Progress] "Theorem after introducing the matches: {thm} :\n{← inferType thm}"
  /- Apply to the scrutinee (which is the pattern provided by the user): `mkProdsMatch` generates
    a lambda expression, where the bound value is the scrutinee we should match over. -/
  let thm := mkApp thm pat
  trace[Progress] "Theorem after introducing the scrutinee: {thm} :\n{← inferType thm}"
  /- Apply to the pure theorem (the expression inside the match is a function which expects to receive this theorem). -/
  let pureThm ← mkPredProofTerm thm0 pat fvars
  trace[Progress] "pureThm: {← inferType pureThm}"
  /- Remark: we could use `mkAppN`, but if we do so with incorrect arguments, we detect the type-checking
    error only very late (typically when checking the term in the kernel), which is why we prefer using `mkAppOptM'`. -/
  let thm ← mkAppOptM' thm #[pureThm]
  trace[Progress] "Theorem after introducing the matches and the app: {thm} :\n{← inferType thm}"
  -- Generate the predicate: we simply replace the pattern with a fresh variable
  let patVarName ← mkFreshUserName `z
  let patTy ← inferType pat
  withLocalDeclD patVarName patTy fun patVar => do
  let pred ← mkThmType patVar [] fvarsExists.toList
  let pred ← mkLambdaFVars #[patVar] pred
  trace[Progress] "Predicate: {pred}\n  :\n{← inferType pred}"
  -- Lift to a Hoare triple
  let specThm ← mkAppM ``spec_toResult #[pat, pred, thm]
  trace[Progress] "Spec theorem before binding the parameters: {specThm}:\n{← inferType specThm}"
  -- Bind the parameters
  let thm ← mkLambdaFVars fvars specThm
  let thmType ← inferType thm
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

def liftThm (stx pat : Syntax) (n : Name) (suffix : String := "progress_spec") : MetaM Name := do
  let mkPred (thm0 pat npat : Expr) (_ : Array Expr) : MetaM Expr := do
    let thm ← mapVisit (fun _ e => do if e == pat then pure npat else pure e) thm0
    /- Reduce a bit the expression, but in a controlled manner, to make it cleaner -/
    let thm ← normalizeLetBindings thm
    reduceProdProjs thm
  let mkPredProofTerm (_thm0 _pat : Expr) (fvars : Array Expr) : MetaM Expr := do
    mkAppOptM n (fvars.map some)
    --pure (mkAppN (.const decl.name (List.map Level.param sig.levelParams)) fvars)
  liftToThm stx pat n (fun _ _ => throwError "Unreachable") mkPred mkPredProofTerm suffix

/-!
# Command: `#progress_pure_lift_thm`

We do not really use it - it is mostly for testing purposes.
-/


local elab "#progress_pure_lift_thm" id:ident pat:term : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  let _ ← liftThm id pat name)

namespace Test
  #progress_pure_lift_thm pos_pair_is_pos (∃ x y, pos_pair = (x, y))

  /--
info: Aeneas.Progress.Test.pos_pair_is_pos.progress_spec :
  ↑pos_pair ⦃⇓ z =>
    ∃ x y,
      z = (x, y) ∧
        match (x, y) with
        | (x, y) => x ≥ 0 ∧ y ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_pair_is_pos.progress_spec

  #progress_pure_lift_thm pos_triple_is_pos pos_triple

  /--
info: Aeneas.Progress.Test.pos_triple_is_pos.progress_spec :
  ↑pos_triple ⦃⇓ z =>
    ∃ y.0 y.1 y.2,
      z = (y.0, y.1, y.2) ∧
        match (y.0, y.1, y.2) with
        | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos.progress_spec

  def pos_triple_is_pos' := pos_triple_is_pos
  #progress_pure_lift_thm pos_triple_is_pos' (∃ z, pos_triple = z)

  /--
info: Aeneas.Progress.Test.pos_triple_is_pos'.progress_spec :
  ↑pos_triple ⦃⇓ z =>
    ∃ z_1,
      z = z_1 ∧
        match z_1 with
        | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos'.progress_spec

  #progress_pure_lift_thm overflowing_add_eq (overflowing_add x y)

  /--
info: Aeneas.Progress.Test.overflowing_add_eq.progress_spec (x y : U8) :
  ↑(overflowing_add x y) ⦃⇓ z => ∃ y.0 y.1, z = (y.0, y.1) ∧ if x.val + y.val > 255 then y.1 = true else y.1 = false ⦄
  -/
  #guard_msgs in
  #check overflowing_add_eq.progress_spec
end Test

/-!
# Attribute: `#progress_pure`
-/

syntax (name := progress_pure) "progress_pure" term : attr

section
  variable {m : Type → Type} [Monad m] [MonadOptions m] [MonadTrace m] [AddMessageContext m] [MonadError m]

  partial def parseCommaSeparated (isTuple : Bool) (stx : Syntax) (acc : Array Syntax := #[]) :
    m (Array Syntax) := do
    trace[ProgressElab] "parsing comma separated: {stx} with acc: {acc}"
    -- TODO: check if ident
    match stx with
    | `(ident| $name:ident) =>
      trace[ProgressElab] "is an ident"
      pure (acc.push stx)
    | _ =>
      trace[ProgressElab] "not an ident"
      let args := stx.getArgs
      trace[ProgressElab] "args.size: {args.size}"
      /- Parsing is not the same if we have `(...)` or `⟨ ... ⟩`:
        - in the first case, the syntax looks like this (we have nested lists): `["x", "," ["y", ...]]`
        - in the second case, the syntax looks like this (the list is flattened): `["x", ",", "y", ...]`
        -/
      if args.size = 0 then pure acc
      else if h: args.size = 1 then pure (acc.push args[0])
      else if h: isTuple ∧ args.size = 3 then
        let arg0 := args[0]
        let arg1 := args[1]
        let arg2 := args[2]
        trace[ProgressElab] "parsing comma separated:\n- arg0: {arg0}\n- arg1: {arg1}\n- arg2: {arg2}"
        let isComma ← do
          match arg1 with
          | .atom _ "," => pure true
          | _ => pure false
        if isComma then
          trace[ProgressElab] "arg1 is a comma"
          parseCommaSeparated isTuple arg2 (acc.push arg0)
        else
          -- Maybe we have a tuple: we simply return the current syntax
          trace[ProgressElab] "arg1 is not a comma"
          pure (acc.push stx)
      else if not isTuple then
        -- There should be an odd number of elements: element, comma, element, ...
        if args.size % 2 ≠ 1 then throwError "Expected an odd number of elements in comma separated syntax, got: {stx}"
        -- Check that the odd elements are commas
        let mut acc := acc
        for i in [0:args.size] do
          let arg := args[i]!
          if i % 2 = 0 then
            -- Should be an element
            acc := acc.push arg
          else
            -- Should be a comma
            match arg with
            | .atom _ "," => pure ()
            | _ => throwError "Expected a comma, got: {arg}"
        pure acc
      else throwError "Unsupported comma separated syntax: {stx}"

  /-- Given a pattern which decomposes a tuple or a struct (`(x, y, z)` or `⟨x, z, z⟩`, `((x, y), z, ⟨a, b⟩), etc.)`,
    return the list of identifiers appearing inside the pattern.

  Remark: I tried implementing something simpler based on pattern matching but couldn't get it to work. -/
  partial def getProgressPurePatternIdents (stx : Syntax) : m (Array Ident) := do
    trace[ProgressElab] "syntax: {stx}"
    -- Check if this is an identifier
    match stx with
    | `(term| $name:ident) => pure #[name]
    |_ =>
    let args := stx.getArgs
    trace[ProgressElab] "args.size: {args.size}"

    -- Check if the syntax is `⟨ ... ⟩` or `( ... )`
    if args.size = 0 then throwError "Unsupported pattern syntax: empty syntax"
    if h: args.size = 3 then
      -- It should be a tuple: decompose it
      let arg0 := args[0]
      let arg1 := args[1]
      let arg2 := args[2]
      let (isTupleOrRecord, isTuple) :=
        match arg0, arg2 with
        | .atom _ "⟨", .atom _ "⟩" => (true, false)
        | .node _ _ #[.atom _ "(", _], .atom _ ")" => (true, true)
        | _, _ => (false, false)
      if not isTupleOrRecord then throwError "Unsupported pattern syntax: {stx}"
      let args ← parseCommaSeparated isTuple arg1
      trace[ProgressElab] "parsed args: {args}"
      -- Recursively decompose
      let xs ← args.mapM getProgressPurePatternIdents
      -- Flatten
      pure xs.flatten
    else throwError "Unsupported pattern syntax: {stx}"

  open Lean Elab Command Term in
  /-- Command to check that we correctly parse tuples -/
  local elab "#check_elab_pattern" pat:term " as " ids:ident,* : command => do
    let ids' ← liftTermElabM (getProgressPurePatternIdents pat)
    trace[ProgressElab] "Identifiers: {ids'.toList}"
    let ids ← ids.getElems.mapM fun x => do
      match x with
      | `(ident| $name:ident) => pure name
      | _ => throwError "not an identifier: {x}"
    if ids == ids' then
      trace[ProgressElab] "Success!"
    else
      throwError "Mismatch! Expected: {ids}, got: {ids'}"

  #check_elab_pattern ⟨⟩ as
  #check_elab_pattern () as
  #check_elab_pattern ⟨x⟩ as x
  #check_elab_pattern (x) as x
  #check_elab_pattern (x, y) as x, y
  #check_elab_pattern (x, y, z) as x, y, z
  #check_elab_pattern ((x, w), y, (a, b, c)) as x, w, y, a, b, c
  #check_elab_pattern (⟨x, w⟩, y, ⟨ a, b, c ⟩) as x, w, y, a, b, c
end

open Elab Term Attribute in
/-- We desugar patterns of the shape `foo = (x, y, z)` to `∃ x y z, foo = (x, y, z)` in order to bind
    the variables introduced in the right-hand side, allowing us to elaborate the patterns. -/
def elabProgressPureAttribute (stx : Syntax) : AttrM (TSyntax `term) :=
  withRef stx do
    match stx with
    | `(attr| progress_pure $x = $pat) => do
      let ids ← getProgressPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure term
    | `(attr| progress_pure $pat) => do pure pat
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
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        -- Elaborate the pattern
        let pat ← elabProgressPureAttribute stx
        -- Introduce the lifted theorem
        let liftedThmName ← MetaM.run' (liftThm stx pat thName)
        -- Save the lifted theorem to the `progress` database
        saveProgressSpecFromThm progressAttr.ext attrKind liftedThmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

/-! # Attribute: `progress_pure_def` -/

/-- Automatically generate a `progress` theorem from a pure definition.

Example:
```lean
@[progress_pure_def wrapping_add = (b, x)]
def wrapping_add (x y : U32) : Bool × U32 := ...
```
generates the theorem:
```lean
@[progress]
theorem wrapping_add.progress_spec (x y : U32) :
  (toResult (wrapping_add x y)) ⦃ ⇓z => ∃ b x, z = (b, x) ∧ (b, x) = wrapping_add x y ⦄
```
(note that the `z` appearing in the post-condition is eliminated when calling `progress`,
leaving only `b` and `x` in the environment).
 -/
syntax (name := progress_pure_def) "progress_pure_def" (term)? : attr

/-- We desugar patterns of the shape `foo = (x, y, z)` to `∃ x y z, foo = (x, y, z)` in order to bind
    the variables introduced in the right-hand side, allowing us to elaborate the patterns. -/
def elabProgressPureDefPattern (stx : Syntax) : AttrM (TSyntax `term) :=
  withRef stx do
    match stx with
    | `(term| $x = $pat)
    | `(term| ($x = $pat)) => do
      trace[ProgressElab] "elabProgressPureDefPattern: equality pattern"
      let ids ← getProgressPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure term
    | `(term| $pat) => do
      trace[ProgressElab] "elabProgressPureDefPattern: not an equality"
      pure pat

/-- The progress pure def attribute -/
structure ProgressPureDefSpecAttr where
  attr : AttributeImpl
  deriving Inhabited

theorem specLiftDef {α} (x : α) : Std.WP.spec (Std.toResult x) (fun y => y = x) := by
  simp only [Std.toResult, Std.WP.spec_ok]

def mkProgressPureDefThm (stx : Syntax) (pat : Option Syntax) (n : Name)
  (suffix : String := "progress_spec") : MetaM Name := do
  /- There is a shortcut (leading to simpler theorems) if there is no pattern and the output type is not a tuple:
     we do not introduce existentials; that is instead of generating a theorem of the shape:
     ```lean
     spec (toResult e) (fun x => ∃ y1 ... yn, x = (y1, ..., yn) ∧ (y1, ..., yn) = e)
     ```
     we generate:
     ```lean
     spec (toResult e) (fun x => x = e)
     ```
     -/
  let env ← getEnv
  let some decl := env.findAsync? n
    | throwError "Could not find definition {n}"
  let sig := decl.sig.get
  let noExists ← do
    match pat with
    | some _ => pure false
    | none => do
      /- Strip the quantifiers -/
      forallTelescope sig.type.consumeMData fun _ ty => do
      pure (Option.isNone (← destEqOpt ty))
  if noExists then
    -- We simply use the theorem `specDef`
    forallTelescope sig.type.consumeMData fun fvars _ => do
    let e ← mkAppOptM n (fvars.map some)
    let thm ← mkAppM ``specLiftDef #[e]
    let thm ← mkLambdaFVars fvars thm
    let thmTy ← inferType thm
    /- Save the auxiliary theorem -/
    let name := Name.str decl.name suffix
    let auxDecl : TheoremVal := {
      name
      levelParams := sig.levelParams
      type := thmTy
      value := thm
    }
    addDecl (.thmDecl auxDecl)
    /- Save the range -/
    addDeclarationRangesFromSyntax name stx
    /- -/
    pure name
  else
    -- Regular case
    let mkPat (fvars : Array Expr) (ty : Expr) : MetaM Expr := do
      withLocalDeclD (← mkFreshUserName `x) ty fun v => do
      let x ← mkAppOptM n (fvars.map some)
      let eq ← mkEq x v
      let eq ← mkLambdaFVars #[v] eq
      mkAppM ``Exists #[eq]
    let mkPred (_ _ npat : Expr) (fvars : Array Expr) : MetaM Expr := do
      mkEq npat (← mkAppOptM n (fvars.map some))
    let mkPredProofTerm (_ _ : Expr) (fvars : Array Expr) : MetaM Expr := do
      let e ← mkAppOptM n (fvars.map some)
      mkEqRefl e
    liftToThm stx pat n mkPat mkPred mkPredProofTerm suffix

local elab "#progress_pure_def" id:ident pat:(term)? : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
    let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
    let name := cs.constName!
    trace[ProgressElab] "pat: {pat}"
    let pat ← match pat with
      | some p => do pure (some (← elabProgressPureDefPattern p))
      | none => pure none
    let _ ← mkProgressPureDefThm id pat name
  )

namespace Test
  #progress_pure_def overflowing_add
  #elab overflowing_add.progress_spec

  /--
info: Aeneas.Progress.Test.overflowing_add.progress_spec (x y : U8) :
  ↑(overflowing_add x y) ⦃⇓ y_1 => y_1 = overflowing_add x y ⦄
  -/
  #guard_msgs in
  #check overflowing_add.progress_spec

  def wrapping_add (x y : U8) : U8 × Bool := (⟨ x.val + y.val ⟩, x.val + y.val ≥ 256)
  #progress_pure_def wrapping_add (wrapping_add x y = (b, z))

  /--
info: Aeneas.Progress.Test.wrapping_add.progress_spec (x y : U8) :
  ↑(wrapping_add x y) ⦃⇓ z => ∃ b z_1, z = (b, z_1) ∧ (b, z_1) = wrapping_add x y ⦄
  -/
  #guard_msgs in
  #check wrapping_add.progress_spec
end Test

def elabProgressPureDefAttribute (stx : Syntax) : AttrM (Option (TSyntax `term)) :=
  withRef stx do
    match stx with
    | `(attr| progress_pure_def $x = $pat)
    | `(attr| progress_pure_def ($x = $pat)) => do
      trace[ProgressElab] "elabProgressPureDefAttribute: equality pattern"
      let ids ← getProgressPurePatternIdents pat
      let term ← ids.foldrM (fun id term => do
        `(term| ∃ $id:ident, $term)
        ) (← `(term| $x = $pat))
      pure (some term)
    | `(attr| progress_pure_def $pat) => do
      trace[ProgressElab] "elabProgressPureDefAttribute: not an equality"
      pure (some pat)
    | `(attr| progress_pure_def) => do
      trace[ProgressElab] "elabProgressPureDefAttribute: not an equality"
      pure none
    | _ => throwError "Unsupported syntax"

/- Initialize the `progress_pure_def` attribute, which automatically generates
   progress lemmas for pure definitions. -/
initialize progressPureDefAttribute : ProgressPureDefSpecAttr ← do
  let attrImpl : AttributeImpl := {
    name := `progress_pure_def
    descr := "Automatically generate `progress` theorems for pure definitions"
    add := fun declName stx attrKind => do
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef declName (pure ()) do
      -- Elaborate the pattern
        trace[Saturate.attribute] "Syntax: {stx}"
        let pat ← elabProgressPureDefAttribute stx
        -- Introduce the lifted theorem
        let thmName ← MetaM.run' (mkProgressPureDefThm stx pat declName)
        -- Save the lifted theorem to the `progress` database
        saveProgressSpecFromThm progressAttr.ext attrKind thmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl }

end Progress

end Aeneas
