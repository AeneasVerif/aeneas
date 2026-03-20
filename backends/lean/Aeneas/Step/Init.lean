import Lean
import AeneasMeta.Utils
import Aeneas.Std.Primitives
import AeneasMeta.Extensions
import Aeneas.Progress.Trace
import Aeneas.Std.WP
import AeneasMeta.OptionConfig

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

/-- The `progress_post_simps_proc` simp attribute for the simp rocs. -/
initialize progressPostSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `progress_post_simps_proc "\
    The `progress_post_simps_proc` attribute registers simp procedures to be used by `progress`
    during its preprocessing phase." none

/-!
# Config
-/

structure Config where
  /- **DO NOT** use this: this is experimental and triggers bugs. -/
  async : Bool := false
  /-- Attempt to discharge preconditions by matching them against local assumptions. -/
  assumTac : Bool := true
  /-- Attempt to infer the ghost variables (variables of progress theorems
      that are not bound in the function call). This requires `assumTac` to
      be `true`. -/
  inferGhostVars : Bool := true
  /-- Use `scalar_tac` to discharge preconditions -/
  scalarTac : Bool := false
  /- Use `simp [*]` to discharge preconditions -/
  simpStar : Bool := false
  /-- Use `grind` to discharge preconditions -/
  grind : Bool := true
  /-- Use the ground simp procedures when calling `grind` -/
  withGroundSimprocs : Bool := true
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splits : Nat := 4
  /--`grind` parameter: see `Lean.Grind.Config` -/
  ematch : Nat := 5
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitMatch : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitIte : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  splitIndPred : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  funext : Bool := false
  /--`grind` parameter: see `Lean.Grind.Config` -/
  gen : Nat  := 2
  /--`grind` parameter: see `Lean.Grind.Config` -/
  instances : Nat  := 1000
  /--`grind` parameter: see `Lean.Grind.Config` -/
  canonHeartbeats : Nat := 1000
deriving Repr

def Config.toGrindConfig (cfg : Config) : Grind.Config :=
  let { async := _, assumTac := _, inferGhostVars := _, scalarTac := _, simpStar := _,
        grind := _, withGroundSimprocs := _,
        splits, ematch, splitMatch, splitIte, splitIndPred, funext, gen, instances, canonHeartbeats } := cfg
  { splits, ematch, splitMatch, splitIte, splitIndPred, funext, gen, instances, canonHeartbeats }

declare_option_config_elab Config elabPartialConfig aeneas.progress

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
  { rules := r.rules.insertKeyValue kv.fst kv.snd,
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
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    Exists.intro x (Exists.intro y (And.intro (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) pos_pair_is_pos

  /- Same as `lifted_is_pos` but making the implicit parameters of the `Exists.intro` explicit:
     this is the important part. -/
  theorem lifted_is_pos' :
    ∃ x y, lift pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    @Exists.intro Int (fun x_1 => ∃ y_1, ok (x, y) = ok (x_1, y_1) ∧ x_1 ≥ 0 ∧ y_1 ≥ 0)
      x (@Exists.intro Int (fun y_1 => ok (x, y) = ok (x, y_1) ∧ x ≥ 0 ∧ y_1 ≥ 0)
        y (@And.intro (ok (x, y) = ok (x, y)) _ (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, lift pos_pair = ok (x, y) ∧
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

theorem spec_lift {α : Type} (x : α) (P : α → Prop) (h : P x) :
  Std.WP.spec (Std.lift x) P := by
  simp [Std.lift]
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

open Std.WP

theorem intro_predn (p : α × β → Prop) : p = predn (fun x y => p (x, y)) := by
  unfold predn
  simp only

theorem lift_to_spec x (p0 p1 : α → Prop) (h0 : p0 x) (h1 : p0 = p1) : spec (Std.lift x) p1 := by
  grind [spec, Std.lift]

namespace Test

  /-- Example which shows how to write the proof term explicitly -/
  theorem test_pos_triple (pos_triple : Nat × Nat × Nat) (thm : (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0) pos_triple) :
    Std.lift pos_triple ⦃ x y z => x > 0 ∧ y > 0 ∧ z > 0 ⦄ := by
    --
    have h := fun x => intro_predn (fun y => match (x, y) with | (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
    --
    have h' := intro_predn (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
    replace h := congrArg predn (funext h)
    replace h := Eq.trans h' h
    clear h'
    --
    replace h := lift_to_spec pos_triple (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
      (predn fun x => predn fun x_1 y => match (x, x_1, y) with | (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0)
      thm h
    exact h

  /-- Example which uses tactics -/
  theorem test_pos_triple' (pos_triple : Nat × Nat × Nat) (thm : (fun (x, y, z) => x > 0 ∧ y > 0 ∧ z > 0) pos_triple) :
    Std.lift pos_triple ⦃ x y z => x > 0 ∧ y > 0 ∧ z > 0 ⦄ := by
    simp -failIfUnchanged -iota only [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok, _root_.Aeneas.Std.WP.predn] at thm ⊢
    exact thm

end Test

/-- Given a theorem type `P x` and a pattern of the shape `∃ y₀ ... yₙ, x = (y₀, ..., yₙ)`,
    generate a theorem type of the shape:
    ```lean
    spec (lift x) (fun y₀ ... yₙ => P (y₀, ..., yₙ))
    ```
    that is, using syntactic sugar:
    ```lean
    (lift x) ⦃ fun y₀ ... yₙ => P (y₀, ..., yₙ) ⦄
    ```

    Note that the pattern is optional: if the user doesn't provide it, we completely decompose
-/
def liftThmType (thmTy : Expr) (pat : Option Syntax)
  /- `mkPat` generates the pattern to use to guide the replacement.

  For instance: `∃ x y, foo a = (x, y)`
   -/
  (mkPat : Array Expr → Expr → MetaM Expr)
  /- `mkPred` receives:
    - the type of the definition/theorem after stripping the quantifiers
    - the pattern
    - the new pattern (can be `(y₀, ..., yₙ)` for instance)
    - the parameters of the definition

    and should generate the: `P (y₀, ..., yₙ)`)
   -/
  (mkPred : Expr → Expr → Expr → Array Expr → MetaM Expr) :
  MetaM Expr := do
  withTraceNode `Progress (fun _ => pure m!"liftThmType") do
  /- Strip the quantifiers *before* elaborating the pattern -/
  forallTelescope thmTy.consumeMData fun fvars thmTy => do
  let pat ← do
    match pat with
    | none => mkPat fvars thmTy
    | some pat => do
      pure ((← Elab.Term.elabTerm pat none |>.run).fst)
  trace[Progress] "Elaborated pattern: {pat}"
  existsTelescope pat.consumeMData fun _ patEq => do
  trace[Progress] "patEq: {patEq}"
  /- Destruct the equality. Note that there may not be an equality, in which case
     we see the type as a tuple and introduce one variable per field of the tuple
     (and a single variable if it is actually not a tuple). -/
  let tryDestEq basename (eq : Expr) (k : Expr → Expr → MetaM Expr) : MetaM Expr := do
    match ← destEqOpt eq with
    | some (x, y) => k x y
    | none =>
      withFreshTupleFieldFVars (.str .anonymous basename) (← inferType pat) fun fvars => do
      k pat (← mkProdsVal fvars.toList)
  tryDestEq "x" patEq fun pat fvarsPat => do
  trace[Progress] "Decomposed patterns: pat: {pat}, fvarsPat: {fvarsPat}"
  /- The decomposed pattern should be tuple a expression: decompose it further into a list of variables -/
  let patFVars : Array Expr := ⟨ destProdsVal fvarsPat ⟩
  /- Substitute the pattern -/
  let thmTy ← mkPred thmTy pat fvarsPat fvars
  trace[Progress] "Theorem after substituting the pattern: {thmTy}"
  /- Create the nested `predn` -/
  let rec mkPredn (fvars : List Expr) : MetaM Expr := do
    withTraceNode `Progress (fun _ => pure m!"mkPredn: fvars: {fvars}") do
    match fvars with
    | [] => throwError "Unexpected"
    | [x] =>
      trace[Progres] "Introducing a single lambda: x: {x}, thmTy: {thmTy}"
      mkLambdaFVars #[x] thmTy
    | x :: fvars => do
      trace[Progres] "Introducing `predn`: x: {x}"
      let thm ← mkPredn fvars
      trace[Progres] "thm: {thm}"
      mkAppM ``predn #[← mkLambdaFVars #[x] thm]
  let thmTy ← mkPredn patFVars.toList
  trace[Progress] "result of mkPredn: {thmTy}"
  /- Add the `spec` -/
  let liftExpr ← mkAppM ``Std.lift #[pat]
  trace[Progress] "liftExpr: {liftExpr}"
  let thmTy ← mkAppM ``spec #[liftExpr, thmTy]
  trace[Progress] "thmTy after introducing `spec`: {thmTy}"
  /- Reintroduce the universal quantifiers -/
  let thmTy ← mkForallFVars fvars thmTy
  trace[Progress] "thmTy after introducing the quantifiers: {thmTy}"
  pure thmTy


def liftThmReplaceInTy (thm0 pat npat : Expr) (_ : Array Expr) : MetaM Expr := do
  let thm ← mapVisit (fun _ e => do if e == pat then pure npat else pure e) thm0
  /- Reduce a bit the expression, but in a controlled manner, to make it cleaner -/
  let thm ← normalizeLetBindings thm
  reduceProdProjs thm

def liftThm (stx : Syntax) (name : Name) (pat : Option (TSyntax `term))
  (mkPat : Array Expr → Expr → MetaM Expr := fun _ _ => failure)
  (mkPred := liftThmReplaceInTy)
  (suffix : String := "progress_spec")
  (tacticStx : Option (TSyntax `tactic) := none)
  : MetaM Name := do
  trace[Progress] "Name: {name}"
  let env ← getEnv
  let some decl := env.findAsync? name
    | throwError "Could not find declaration {name}"
  let sig := decl.sig.get
  -- Generate the type of the theorem
  let thmTy ← liftThmType sig.type pat mkPat mkPred
  trace[Progress] "thmTy: {thmTy}"
  -- Prove the theorem - we keep things simple by calling a tactic
  let mvar ← mkFreshExprSyntheticOpaqueMVar thmTy
  let tacticStx ← do
    match tacticStx with
    | none =>
      `(tactic|
        simp -failIfUnchanged -iota only
          [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok, _root_.Aeneas.Std.WP.predn] <;>
        exact $(mkIdent name))
    | some stx => pure stx
  let (goals, _) ← runTactic mvar.mvarId! tacticStx
  if goals.length > 0 then throwError "Could not prove the theorem"
  --
  let name := Name.str name suffix
  let auxDecl : TheoremVal := {
    name
    levelParams := sig.levelParams
    type := thmTy
    value := ← instantiateMVars mvar
  }
  addDecl (.thmDecl auxDecl)
  /- Save the range -/
  addDeclarationRangesFromSyntax name stx
  --
  pure name

/-!
# Command: `#progress_pure_lift_thm`

We do not really use it - it is mostly for testing purposes.
-/

elab stx:"#progress_pure_lift_thm" id:ident pat:term : command => do
  Lean.Elab.Command.runTermElabM fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  let _ ← liftThm stx name pat

namespace Test
  #progress_pure_lift_thm pos_pair_is_pos (∃ x y, pos_pair = (x, y))

  /--
info: Aeneas.Progress.Test.pos_pair_is_pos.progress_spec :
  Std.lift pos_pair ⦃ x y =>
    match (x, y) with
    | (x, y) => x ≥ 0 ∧ y ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_pair_is_pos.progress_spec

  #progress_pure_lift_thm pos_triple_is_pos pos_triple

  /--
info: Aeneas.Progress.Test.pos_triple_is_pos.progress_spec :
  Std.lift pos_triple ⦃ x.0 x.1 x.2 =>
    match (x.0, x.1, x.2) with
    | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos.progress_spec

  def pos_triple_is_pos' := pos_triple_is_pos
  #progress_pure_lift_thm pos_triple_is_pos' (∃ z, pos_triple = z)

  /--
info: Aeneas.Progress.Test.pos_triple_is_pos'.progress_spec :
  Std.lift pos_triple ⦃ z =>
    match z with
    | (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ⦄
  -/
  #guard_msgs in
  #check pos_triple_is_pos'.progress_spec

  #progress_pure_lift_thm overflowing_add_eq (overflowing_add x y)

  /--
info: Aeneas.Progress.Test.overflowing_add_eq.progress_spec (x y : U8) :
  Std.lift (overflowing_add x y) ⦃ x.0 x.1 => if x.val + y.val > 255 then x.1 = true else x.1 = false ⦄
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

/-- The `progress_pure` attribute lifts lemmas about pure functions to `progress` lemmas.

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
    ↑(wrapping_add x y) ⦃ z => z.bv = x.bv + y.bv ⦄
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
    ↑pos_pair ⦃ x y => x ≥ 0 ∧ y ≥ 0 ⦄
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
    ↑pos_pair ⦃ z => z.fst ≥ 0 ∧ z.fst ≥ 0 ⦄
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
        let liftedThmName ← MetaM.run' (liftThm stx thName pat)
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
  (lift (wrapping_add x y)) ⦃ b x => (b, x) = wrapping_add x y ⦄
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

theorem specLiftDef {α} (x : α) : Std.WP.spec (Std.lift x) (fun y => y = x) := by
  simp only [Std.lift, Std.WP.spec_ok]

def mkProgressPureDefThm (stx : Syntax) (pat : Option (TSyntax `term)) (n : Name)
  (suffix : String := "progress_spec") : MetaM Name := do
  -- Regular case
  let mkPat (fvars : Array Expr) (ty : Expr) : MetaM Expr := do
    withTraceNode `Progress (fun _ => pure m!"mkPat") do
    withLocalDeclD (← mkFreshUserName `x) ty fun v => do
    let x ← mkAppOptM n (fvars.map some)
    trace[Progress] "x: {x}"
    let eq ← mkEq x v
    trace[Progress] "eq: {eq}"
    let eq ← mkLambdaFVars #[v] eq
    let eq ← mkAppM ``Exists #[eq]
    trace[Progress] "eq: {eq}"
    pure eq
  let mkPred (_ _ npat : Expr) (fvars : Array Expr) : MetaM Expr := do
    withTraceNode `Progress (fun _ => pure m!"mkPred") do
    mkEq npat (← mkAppOptM n (fvars.map some))
  let tacticStx ←
    `(tactic|
        simp only
          [_root_.Aeneas.Std.lift, _root_.Aeneas.Std.WP.spec_ok, _root_.Aeneas.Std.WP.predn, _root_.implies_true])
  liftThm stx n pat mkPat mkPred suffix (tacticStx := some tacticStx)

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
  Std.lift (overflowing_add x y) ⦃ x✝ => x✝ = overflowing_add x y ⦄
  -/
  #guard_msgs in
  #check overflowing_add.progress_spec

  def wrapping_add (x y : U8) : U8 × Bool := (⟨ x.val + y.val ⟩, x.val + y.val ≥ 256)
  #progress_pure_def wrapping_add (wrapping_add x y = (b, z))

  /--
info: Aeneas.Progress.Test.wrapping_add.progress_spec (x y : U8) :
  Std.lift (wrapping_add x y) ⦃ b z => (b, z) = wrapping_add x y ⦄
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

/- The `progress_pure_def` attribute, which automatically generates
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
