module
public import Aeneas.SepLogic.Tactic.Init
public meta import Aeneas.SepLogic.Tactic.Init
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

namespace Normalize

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

/-- The atoms of the `sep` tree `e`; `frame` is kept as one atom. -/
partial def flatten (e : Expr) (frame : Option Expr := none) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  if frame == some e.consumeMData then return #[e]
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return (← flatten args[0]! frame) ++ (← flatten args[1]! frame)
  if fn.isConstOf `Aeneas.SepLogic.emp then
    return #[]
  return #[e]

def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst `Aeneas.SepLogic.emp
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``sep) atom rest

/-- The atoms of a reification, and the index of each (syntactic) atom. -/
private abbrev AtomEnv := Array Expr × Std.HashMap Expr Nat

/-- Reify the `sep` structure of `e` as a `SepAC.Tree`, numbering its atoms in the state. Also
returns the atom indices, in order. -/
private partial def reifySep (e : Expr) : StateT AtomEnv MetaM (Expr × List Nat) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    let (l, li) ← reifySep args[0]!
    let (r, ri) ← reifySep args[1]!
    return (mkApp2 (mkConst ``SepAC.Tree.node) l r, li ++ ri)
  if fn.isConstOf `Aeneas.SepLogic.emp then return (mkConst ``SepAC.Tree.unit, [])
  let atom := e.consumeMData
  let (atoms, index) ← get
  let i ← match index[atom]? with
    | some i => pure i
    | none => do set (atoms.push atom, index.insert atom atoms.size); pure atoms.size
  return (mkApp (mkConst ``SepAC.Tree.atom) (mkNatLit i), [i])

/-- Prove `lhs = rhs` for two `sep` trees over the same atoms, with one `SepAC.Tree.denote_eq`.
Atoms are compared syntactically, except that the pairs `(a, b)` of `aliases` (atoms that the
matcher unified) put `a` and `b` in the same class: the kernel checks that they are defeq. -/
def proveEqAC (lhs rhs : Expr) (aliases : Array (Expr × Expr) := #[]) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return ← mkEqRefl lhs
  let mut env : AtomEnv := (#[], {})
  for (a, b) in aliases do
    let a := (← instantiateMVars a).consumeMData
    let b := (← instantiateMVars b).consumeMData
    env := match env.2[a]?, env.2[b]? with
      | some i, some j => (env.1, env.2.map fun _ k => if k == j then i else k)
      | some i, none => (env.1, env.2.insert b i)
      | none, some j => (env.1, env.2.insert a j)
      | none, none => (env.1.push b, (env.2.insert b env.1.size).insert a env.1.size)
  let (((l, li), (r, ri)), (atoms, _)) ← (do return (← reifySep lhs, ← reifySep rhs)).run env
  unless li.toArray.qsort (· < ·) == ri.toArray.qsort (· < ·) do
    throwError "the assertions do not have the same atoms:\n{lhs}\nand\n{rhs}"
  let atomList ← mkListLit (mkConst ``IProp) atoms.toList
  let proof := mkAppN (mkConst ``SepAC.Tree.denote_eq)
    #[atomList, l, r, ← mkEqRefl (mkConst ``Bool.true)]
  mkExpectedTypeHint proof (← mkEq lhs rhs)

/-- The precondition and the postcondition of `goal`, if it is an `Entails`. -/
def entailment? (goal : MVarId) : MetaM (Option (Expr × Expr)) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Entails 2 do return none
  return some (target.appFn!.appArg!, target.appArg!)

/-- Is `destination` a frame-inference shape `Hcallee ∗ ?F`? Then no side may be reorganized. -/
def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``sep && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let some (_, destination) ← entailment? goal | return false
  return (← frameMVar? (← reducePostApplication destination)).isSome

/-- Simplify `goal`; `none` if this closed it. -/
def simpGoal (goal : MVarId) (simpOnly : Bool) (args : Aeneas.Simp.SimpArgs) :
    TacticM (Option MVarId) := do
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Aeneas.Simp.simpAt simpOnly
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      args (.targets #[] true)
    match ← getUnsolvedGoals with
    | [] => return none
    | [goal] => return some goal
    | _ => throwError "simplifying the entailment produced multiple goals"
  finally
    setGoals saved

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Aeneas.Simp.SimpArgs) : TacticM MVarId := do
  let some goal ← simpGoal goal simpOnly args
    | throwError "the entailment was unexpectedly closed while normalizing it"
  return goal

/-- Remove `emp` units and float existentials out of `∗`. -/
def sepNormThms : Array Name :=
  #[``sep_emp_l_eq, ``sep_emp_r_eq, ``sep_exists_l_eq, ``sep_exists_r_eq]

def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← isimpsExt.getTheorems] }

/-- `e` with the definitions hiding connectives unfolded along its `sep` spine, except in
`frame`. -/
private partial def exposeAll (e : Expr) (frame : Option Expr := none) : MetaM Expr := do
  let e ← reducePostApplication e
  if frame == some e.consumeMData then return e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return mkApp2 (mkConst ``sep) (← exposeAll args[0]! frame) (← exposeAll args[1]! frame)
  return e

def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let some (source, destination) ← entailment? goal | return goal
  let source' ← exposeAll source
  let destination' ← exposeAll destination
  if source' == source && destination' == destination then return goal
  try goal.change (mkApp2 (mkConst ``Entails) source' destination') catch _ => pure goal

/-- Split out the pure atoms of `assertion` (those whose proposition satisfies `select`). Returns
the propositions, the assertion of the other atoms `rest`, and a proof of
`assertion = A₁ ∗ … ∗ Aₖ ∗ rest`, where `Aᵢ` is the original atom of `⌜Pᵢ⌝` (possibly a
definition unfolding to it). -/
def splitPures (assertion : Expr) (select : Expr → MetaM Bool := fun _ => pure true) :
    TacticM (Option (Array Expr × Expr × Expr)) := do
  let assertion ← reducePostApplication assertion
  let mut pures := #[]
  let mut props := #[]
  let mut others := #[]
  for atom in ← flatten assertion do
    let exposed := (← exposeConnective atom).consumeMData
    if exposed.isAppOfArity ``ipure 1 then
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
def introPures (props : Array Expr) (rest destination next : Expr) : MetaM Expr := do
  -- the tails `⌜Pᵢ₊₁⌝ ∗ … ∗ rest`, sharing their subterms
  let tails := props.foldr (init := [rest]) fun P tails =>
    mkApp2 (mkConst ``sep) (mkApp (mkConst ``ipure) P) tails.head! :: tails
  go props.toList tails.tail! next
where
  go : List Expr → List Expr → Expr → MetaM Expr
    | proposition :: more, tail :: tails, next => do
      let body ← withLocalDeclD (← mkFreshUserName `h) proposition fun h => do
        mkLambdaFVars #[h] (← go more tails (mkApp next h))
      return mkAppN (mkConst ``entails_pure_l) #[proposition, tail, destination, body]
    | _, _, next => return next

partial def exposeEntailment? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Entails 2 then return some e
  match ← unfoldDefinition? e with
  | some e' => exposeEntailment? e'
  | none => return none

/-- `target`, an entailment `source ⊢ destination` possibly behind definitions, with the source
replaced by `newSource`. -/
def mkEntailmentLike (target source destination newSource : Expr) : MetaM Expr := do
  let (fn, targetArgs) :=
    target.consumeMData.withApp fun fn args => (fn, args)
  let newSourceType ← inferType newSource
  for h : i in [:targetArgs.size] do
    let argType ← inferType targetArgs[i]
    if ← isDefEq argType newSourceType then
      let candidate := mkAppN fn (targetArgs.set! i newSource)
      if let some exposed ← exposeEntailment? candidate then
        let args := exposed.getAppArgs
        if ← isDefEq args[0]! newSource then
          if ← isDefEq args[1]! destination then
            return candidate
  let replacement := target.replace fun e =>
    if e == source then some newSource else none
  if let some exposed ← exposeEntailment? replacement then
    let args := exposed.getAppArgs
    if ← isDefEq args[0]! newSource then
      if ← isDefEq args[1]! destination then
        return replacement
  mkAppM ``Entails #[newSource, destination]

/-- `e` with its `k`-th atom (in the order of `flatten`, after the unfolding of `exposeAll` if
`unfold`) replaced by `f k atom`, or dropped if `none`. The rest is unchanged: same `sep`
structure, and the definitions whose atoms are all kept stay folded. `none` if no atom is left. -/
private partial def mapAtoms (unfold : Bool) (frame : Option Expr)
    (f : Nat → Expr → Option Expr) (e : Expr) : StateT Nat MetaM (Option Expr) := do
  let e ← reducePostApplication e
  let atom : StateT Nat MetaM (Option Expr) := modifyGet fun k => (f k e, k + 1)
  if frame == some e.consumeMData then return ← atom
  let exposed ← if unfold then pure ((← exposeConnective? e).getD e) else pure e
  let (fn, args) := exposed.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    let l ← mapAtoms unfold frame f args[0]!
    let r ← mapAtoms unfold frame f args[1]!
    if l == some args[0]! && r == some args[1]! then return some e
    return match l, r with
      | some l, some r => some (mkApp2 (mkConst ``sep) l r)
      | l, none => l
      | none, r => r
  if fn.isConstOf `Aeneas.SepLogic.emp then return some e
  atom

/-- Move the existentials and pure facts of the precondition of `goal` (an entailment, possibly
behind definitions) into the context, without simp: each round either opens the first `∃` atom
(existentials come before the pure facts, wherever they are), replacing it by its body in place,
or removes the `⌜P⌝` atoms, from left to right; the rest of the precondition is unchanged. At
most `limit` items are moved. With `unfold`, definitions hiding connectives are looked into; the
atom `frame` is never looked into; with `names`, the binder names (`h` for the facts) stay
accessible. -/
partial def pullLeft (goal : MVarId) (unfold := true) (frame : Option Expr := none)
    (names := false) (limit : Option Nat := none) : TacticM MVarId := goal.withContext do
  if limit == some 0 then return goal
  if ← isFrameInference goal then return goal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← exposeEntailment? target | return goal
  let source := entailment.appFn!.appArg!
  let destination := entailment.appArg!
  let expose (e : Expr) : MetaM Expr :=
    if unfold then exposeAll e frame else reducePostApplication e
  let atoms ← flatten (← expose source) frame
  let edit (f : Nat → Expr → Option Expr) : MetaM Expr := do
    return ((← (mapAtoms unfold frame f source).run' 0).getD (mkConst `Aeneas.SepLogic.emp))
  -- `a ⊢ b` for assertions with the same atoms
  let reorder (a b : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``entails_of_eq) a b (← proveEqAC (← expose a) (← expose b))
  let trans (a b c pab pbc : Expr) := mkApp5 (mkConst ``entails_trans) a b c pab pbc
  let binderName (n : Name) : MetaM Name := if names then pure n else mkFreshUserName n
  let next (newSource : Expr) := mkEntailmentLike target source destination newSource
  let is (name : Name) (arity : Nat) (atom : Expr) :=
    frame != some atom.consumeMData && atom.consumeMData.isAppOfArity name arity
  if let some i := atoms.findIdx? (is ``iexists 2) then
    let atom := atoms[i]!.consumeMData
    let some u := atom.getAppFn.constLevels!.head?
      | throwError "could not determine the universe of {atom}"
    let ι := atom.appFn!.appArg!
    let J := atom.appArg!
    let rest ← edit fun k atom => if k == i then none else some atom
    let inPlace (x : Expr) : MetaM Expr := do
      let body ← Core.betaReduce (mkApp J x)
      edit fun k atom => if k == i then some body else some atom
    let x := match J with | .lam n .. => n | _ => `x
    let newType ← withLocalDeclD (← binderName x) ι fun x => do
      mkForallFVars #[x] (← next (← inPlace x))
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    -- `∀ x, J x ∗ rest ⊢ destination`, through `J x ∗ rest ⊢ inPlace x`
    let opened ← withLocalDeclD `x ι fun x => do
      let bodyRest := mkApp2 (mkConst ``sep) (← Core.betaReduce (mkApp J x)) rest
      let inPlace ← inPlace x
      mkLambdaFVars #[x] (trans bodyRest inPlace destination (← reorder bodyRest inPlace)
        (mkApp newGoal x))
    let reordered := mkApp2 (mkConst ``sep) atom rest
    goal.assign (trans source reordered destination (← reorder source reordered)
      (mkAppN (mkConst ``entails_exists_sep_l [u]) #[ι, rest, destination, J, opened]))
    let (_, newGoal) ← newGoal.mvarId!.intro1P
    return ← pullLeft newGoal unfold frame names (limit.map (· - 1))
  let selected := (Array.range atoms.size).filter (is ``ipure 1 atoms[·]!)
  let selected := match limit with | some n => selected.take n | none => selected
  if selected.isEmpty then return goal
  let props := selected.map (atoms[·]!.consumeMData.appArg!)
  let rest ← edit fun k atom => if selected.contains k then none else some atom
  let reordered := selected.foldr (mkApp2 (mkConst ``sep) atoms[·]! ·) rest
  let newType ← props.foldrM (init := ← next rest)
    fun P acc => return mkForall (← binderName `h) .default P acc
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (trans source reordered destination (← reorder source reordered)
    (← introPures props rest destination newGoal))
  let (_, newGoal) ← newGoal.mvarId!.introNP props.size
  pullLeft newGoal unfold frame names (limit.map (· - props.size))

/-- `pullLeft`, also returning the hypotheses it introduced, in order. -/
def pullLeftFVars (goal : MVarId) (unfold := true) (frame : Option Expr := none)
    (names := false) (limit : Option Nat := none) : TacticM (MVarId × Array FVarId) := do
  let before ← goal.withContext getLCtx
  let goal ← pullLeft goal unfold frame names limit
  let new ← goal.withContext do
    return (← getLCtx).foldl (init := #[]) fun new decl =>
      if before.contains decl.fvarId then new else new.push decl.fvarId
  return (goal, new)

/-- `pullLeft`, then rewrite the goal with the facts this introduced (if `useFacts`); `none` if
that closed the goal. -/
def pullAndRewrite (goal : MVarId) (useFacts := true) : TacticM (Option MVarId) := do
  let (goal, new) ← pullLeftFVars goal
  if !useFacts then return some goal
  let facts ← goal.withContext <| new.filterM fun fvar => do isProp (← fvar.getType)
  if facts.isEmpty then return some goal
  goal.withContext <| simpGoal goal true { hypsToUse := facts }

def normalizeSep : TacticM Unit := withMainContext do
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms := sepNormThms ++ #[``sep_assoc_eq, ``entails_postWand_pure_eq] }
    (.targets #[] true)

end Normalize

end Aeneas.SepLogic
