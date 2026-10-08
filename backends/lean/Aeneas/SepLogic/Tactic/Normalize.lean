module
public import Aeneas.SepLogic.Tactic.Init
public meta import Aeneas.SepLogic.Tactic.Init
public import Lean.Meta.Tactic.AC
public meta import Lean
public meta import AeneasMeta.Simp

/-! Normalization of separation-logic assertions, shared by the tactics: exposing connectives,
flattening `sep` trees, reflective reordering proofs, and pulling pure facts and existentials out
of preconditions. -/

@[expose] public section

namespace Aeneas.SepLogic

/-! Reflective reordering: the tactics reify both sides of `A = B` as `SepAC.Tree`s over a shared
list of atoms, and prove it with `Tree.denote_eq`, whose side condition the kernel decides by
evaluating `List.isPerm` on the atom indices. -/
namespace SepAC

inductive Tree where
  | atom (i : Nat)
  | unit
  | node (l r : Tree)

def Tree.denote (env : List IProp) : Tree → IProp
  | .atom i => env.getD i emp
  | .unit => emp
  | .node l r => l.denote env ∗ r.denote env

def Tree.atoms : Tree → List Nat
  | .atom i => [i]
  | .unit => []
  | .node l r => l.atoms ++ r.atoms

theorem foldr_sep_append (l r : List IProp) :
    (l ++ r).foldr sep emp = (l.foldr sep emp ∗ r.foldr sep emp) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sep_assoc_eq]

theorem foldr_sep_perm {l r : List IProp} (h : l.Perm r) :
    l.foldr sep emp = r.foldr sep emp := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b l =>
    simp only [List.foldr]
    rw [← sep_assoc_eq, sep_comm_eq b a, sep_assoc_eq]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Tree.denote_eq_foldr (env : List IProp) (t : Tree) :
    t.denote env = (t.atoms.map (env.getD · emp)).foldr sep emp := by
  induction t with
  | atom i => simp [Tree.denote, Tree.atoms, sep_emp_r_eq]
  | unit => rfl
  | node l r ihl ihr =>
    simp only [Tree.denote, Tree.atoms, ihl, ihr, List.map_append, foldr_sep_append]

theorem Tree.denote_eq (env : List IProp) (l r : Tree) (h : l.atoms.isPerm r.atoms = true) :
    l.denote env = r.denote env := by
  rw [Tree.denote_eq_foldr, Tree.denote_eq_foldr]
  exact foldr_sep_perm ((List.isPerm_iff.mp h).map _)

end SepAC

end Aeneas.SepLogic

end

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

namespace IFrame

private def isConnective (e : Expr) : Bool :=
  let head := e.consumeMData.getAppFn
  head.isConstOf ``sep || head.isConstOf ``iand || head.isConstOf ``ipure ||
    head.isConstOf ``iexists || head.isConstOf `Aeneas.SepLogic.emp ||
    head.isConstOf ``wand || head.isConstOf ``postWand || head.isConstOf ``iforall

def exposeConnective? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if isConnective e then return some e
  match ← unfoldDefinition? e with
  | some e' => if isConnective e' then return some e' else return none
  | none => return none

def exposeConnective (e : Expr) : MetaM Expr :=
  return (← exposeConnective? e).getD e

def reducePostApplication (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Lean.Core.betaReduce e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postSep && args.size = 4 then
    return mkApp2 (mkConst ``sep) (mkApp args[1]! args[3]!) args[2]!
  return e

partial def flatten (e : Expr) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return (← flatten args[0]!) ++ (← flatten args[1]!)
  if fn.isConstOf `Aeneas.SepLogic.emp then
    return #[]
  return #[e]

def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst `Aeneas.SepLogic.emp
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``sep) atom rest

/-- Reify the `sep` structure of `e` as a `SepAC.Tree`, numbering its atoms in the state. Atoms
are identified up to unfolding of instances (without assigning metavariables), since the same
`p ↦ v` may come with syntactically different instance arguments. Also returns the atom
indices, in order. -/
private partial def reifySep (e : Expr) : StateT (Array Expr) MetaM (Expr × List Nat) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    let (l, li) ← reifySep args[0]!
    let (r, ri) ← reifySep args[1]!
    return (mkApp2 (mkConst ``SepAC.Tree.node) l r, li ++ ri)
  if fn.isConstOf `Aeneas.SepLogic.emp then return (mkConst ``SepAC.Tree.unit, [])
  let atom := e.consumeMData
  let atoms ← get
  let i ← match atoms.findIdx? (· == atom) with
    | some i => pure i
    | none =>
      match ← atoms.findIdxM? fun known =>
          withNewMCtxDepth <| withTransparency .instances <| isDefEq known atom with
      | some i => pure i
      | none => do set (atoms.push atom); pure atoms.size
  return (mkApp (mkConst ``SepAC.Tree.atom) (mkNatLit i), [i])

/-- Prove `lhs = rhs` for two `sep` trees with the same atoms, with one `SepAC.Tree.denote_eq`;
fall back to `ac_rfl`/`rfl` when the atoms only agree up to more than instance unfolding. -/
def proveEqAC (lhs rhs : Expr) : TacticM Expr := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return ← mkEqRefl lhs
  let eqType ← mkEq lhs rhs
  let (((l, li), (r, ri)), atoms) ← (do return (← reifySep lhs, ← reifySep rhs)).run #[]
  if li.toArray.qsort (· < ·) == ri.toArray.qsort (· < ·) then
    let env ← mkListLit (mkConst ``IProp) atoms.toList
    let proof := mkAppN (mkConst ``SepAC.Tree.denote_eq)
      #[env, l, r, ← mkEqRefl (mkConst ``Bool.true)]
    return ← mkExpectedTypeHint proof eqType
  let proof ← mkFreshExprSyntheticOpaqueMVar eqType
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create an equality proof goal"
  let tactic ← `(tactic|
    first
      | ac_rfl
      | rfl
      | (simp only [sep_emp_l_eq, sep_emp_r_eq] <;>
          first | ac_rfl | rfl))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove {eqType}"
  return proof

/-- Is `destination` a frame-inference shape `Hcallee ∗ ?F`? Then no side may be reorganized. -/
def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``sep && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return false
  return (← frameMVar? (← reducePostApplication args[1]!)).isSome

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Aeneas.Simp.SimpArgs) : TacticM MVarId := do
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Aeneas.Simp.simpAt simpOnly
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      args (.targets #[] true)
    match ← getGoals with
    | [] => throwError "the entailment was unexpectedly closed while normalizing it"
    | goal :: _ => pure goal
  finally
    setGoals saved

def floatExists (goal : MVarId) : TacticM MVarId :=
  simpEntailment goal true
    { addSimpThms :=
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq] }

def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← isimpsExt.getTheorems] }

private partial def exposeAll (e : Expr) : MetaM Expr := do
  let e ← reducePostApplication e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return mkApp2 (mkConst ``sep) (← exposeAll args[0]!) (← exposeAll args[1]!)
  return e

def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let exposed ← mkAppM ``Entails #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

/-- Split out the pure atoms of `assertion` (the first `limit` ones whose proposition satisfies
`select`). Returns the propositions, the assertion of the other atoms `rest`, and a proof of
`assertion = A₁ ∗ … ∗ Aₖ ∗ rest`, where `Aᵢ` is the original atom of `⌜Pᵢ⌝` (possibly a
definition unfolding to it). -/
def splitPures (assertion : Expr) (limit : Option Nat := none)
    (select : Expr → MetaM Bool := fun _ => pure true) :
    TacticM (Option (Array Expr × Expr × Expr)) := do
  let assertion ← reducePostApplication assertion
  let mut pures := #[]
  let mut props := #[]
  let mut others := #[]
  for atom in ← flatten assertion do
    let exposed := (← exposeConnective atom).consumeMData
    if limit.all (props.size < ·) && exposed.isAppOfArity ``ipure 1 then
      if ← select exposed.appArg! then
        pures := pures.push atom
        props := props.push exposed.appArg!
        continue
    others := others.push atom
  if props.isEmpty then return none
  let rest := mkStar others
  let reordered := pures.foldr (mkApp2 (mkConst ``sep) · ·) rest
  return some (props, rest, ← proveEqAC assertion reordered)

/-- A proof of `⌜P₁⌝ ∗ … ∗ ⌜Pₖ⌝ ∗ rest ⊢ destination` from
`next : P₁ → … → Pₖ → rest ⊢ destination`. -/
def introPures (props : Array Expr) (rest destination next : Expr) : MetaM Expr :=
  go props.toList next
where
  go : List Expr → Expr → MetaM Expr
    | [], next => return next
    | proposition :: more, next => do
      let tail := more.foldr
        (fun P acc => mkApp2 (mkConst ``sep) (mkApp (mkConst ``ipure) P) acc) rest
      let body ← withLocalDeclD (← mkFreshUserName `h) proposition fun h => do
        mkLambdaFVars #[h] (← go more (mkApp next h))
      return mkAppN (mkConst ``entails_pure_l) #[proposition, tail, destination, body]

/-- Open the leading existentials of the precondition. -/
private partial def openLeftExists (goal : MVarId) (opened := false) :
    MetaM (MVarId × Bool) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return (goal, opened)
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let (sourceFn, sourceArgs) :=
    source.consumeMData.withApp fun fn args => (fn, args)
  unless sourceFn.isConstOf ``iexists && sourceArgs.size = 2 do return (goal, opened)
  let some u := sourceFn.constLevels!.head?
    | throwError "could not determine the universe of {source}"
  let ι := sourceArgs[0]!
  let J := sourceArgs[1]!
  let newType ← withLocalDeclD (← mkFreshUserName `x) ι fun x => do
    mkForallFVars #[x] (← mkAppM ``Entails #[← Core.betaReduce (mkApp J x), destination])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``entails_exists_l [u]) #[ι, destination, J, newGoal])
  let (_, next) ← newGoal.mvarId!.intro1P
  openLeftExists next true

/-- Move all the pure facts of the precondition into the context, with one reordering. -/
private def pullPures (goal : MVarId) : TacticM (MVarId × Bool) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return (goal, false)
  let destination ← reducePostApplication args[1]!
  let some (props, rest, eq) ← splitPures args[0]! | return (goal, false)
  let newType ← props.foldrM (init := mkApp2 (mkConst ``Entails) rest destination)
    fun P acc => return mkForall (← mkFreshUserName `h) .default P acc
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  let extract ← introPures props rest destination newGoal
  let reordered := (← inferType eq).appArg!
  goal.assign (mkAppN (mkConst ``entails_trans)
    #[args[0]!, reordered, destination, mkAppN (mkConst ``entails_of_eq) #[args[0]!, reordered, eq],
      extract])
  let (_, next) ← newGoal.mvarId!.introNP props.size
  return (next, true)

/-- Move the existentials and pure facts of the precondition into the context. Each round
normalizes once, then opens every leading `∃` and pulls every `⌜P⌝`; a new round runs only if
the previous one exposed something. -/
partial def pullLeft (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then return goal
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  let (goal, opened) ← openLeftExists goal
  let (goal, pulled) ← pullPures goal
  if opened || pulled then pullLeft goal else return goal

end IFrame

def normalizeSep : TacticM Unit := withMainContext do
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq, ``sep_assoc_eq,
          ``entails_postWand_pure_eq] }
    (.targets #[] true)

end Aeneas.SepLogic
