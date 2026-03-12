import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace higher_order

section tactic
open Lean Elab Tactic Meta

elab "infer_post" : tactic => do
  withMainContext do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)

  -- The goal should be of the form `?post arg`
  let (mvarFn, args) := goalTy.withApp fun f a => (f, a)
  unless mvarFn.isMVar do
    throwTacticEx `infer_post goal
      m!"goal should be of the form `?post args...`, got {goalTy}"
  let mvarId := mvarFn.mvarId!
  let argFVar ← match (← instantiateMVars args[0]!).fvarId? with
    | some fv => pure fv
    | none => throwTacticEx `infer_post goal m!"argument {args[0]!} is not a free variable"
  let argTy ← argFVar.getType

  let mvarLCtx := (← mvarId.getDecl).lctx
  let lctx ← getLCtx
  logInfo m!"lctx: {(←lctx.getDecls).map fun d => (d.userName, d.type)}"

  -- Must also quantify over non-prop free vars that aren't in the mvar's context
  let nonProps ← (← lctx.getDecls).filterMapM fun decl => do
    if mvarLCtx.contains decl.fvarId then return none
    if decl.fvarId == argFVar then return none
    if ← isProp decl.type then return none
    return some decl.fvarId
  logInfo
    m!"escaping nonprops: {(←nonProps.mapM fun f => f.getDecl).map fun d => d.userName}"

  -- Collect props mentioning argFVar or any escaping non-prop variable.
  let relevantFVars := nonProps ++ [argFVar]
  let relevantProps := (← lctx.getAssumptions).filter fun decl =>
    relevantFVars.any fun fv => decl.type.find? (·.isFVarOf fv) |>.isSome
  logInfo m!"relevant props: {relevantProps.map fun d => d.type}"

  -- Build postcondition:
  let postExpr ← withLocalDeclD `res argTy fun resExpr => do
    let eq ← mkEq resExpr (.fvar argFVar)
    let andBody ← relevantProps.foldrM (fun p acc => mkAppM ``And #[p.type, acc]) eq
    logInfo m!"andBody: {andBody}"

    -- Build existentials: innermost is ∃ arg', then wrap with escaping vars.
    let existsBody ← (nonProps ++ [argFVar]).foldrM (fun fVar acc => do
        let pred ← mkLambdaFVars #[.fvar fVar] acc
        mkAppOptM ``Exists #[none, some pred]
      ) andBody
    mkLambdaFVars #[resExpr] existsBody
  logInfo m!"expr: {postExpr}"
  mvarId.assign postExpr

  -- let grind close the postcondition goal
  evalTactic (←`(tactic|grind only))

end tactic

def applyF (f : U32 → Result U32) (x : U32) : Result U32 := f x

theorem applyF_spec (f : U32 → Result U32) (x : U32)
    (post : U32 → Prop)
    (hf : f x ⦃ post ⦄) :
    applyF f x ⦃ post ⦄ := by
  simp [applyF]; exact hf

example (a : U32) (h : a.val + 1 ≤ U32.max) :
    applyF (fun x => x + 1#u32) a ⦃ y => y.val = a.val + 1 ⦄ := by
  progress with applyF_spec
  case hf => progress as ⟨ b, hb ⟩; infer_post
  grind

-- Higher-order in 2 functions, operates on a pair of inputs/outputs
def callPair (f : U32 → Result U32) (g : U32 → Result U32) (xy : U32 × U32) : Result (U32 × U32) := do
  let a ← f xy.1
  let b ← g xy.2
  return (a, b)

theorem callPair_spec (f g : U32 → Result U32) (xy : U32 × U32)
    (postF : U32 → Prop) (postG : U32 → Prop)
    (hf : f xy.1 ⦃ postF ⦄) (hg : g xy.2 ⦃ postG ⦄) :
    callPair f g xy ⦃ fun p => postF p.1 ∧ postG p.2 ⦄ := by
  simp only [callPair]
  apply WP.spec_bind hf
  intro a ha
  apply WP.spec_bind hg
  intro b hb
  simp [WP.spec, WP.theta, WP.wp_return]
  exact ⟨ha, hb⟩

example (x y : U32) (hx : x.val + 1 ≤ U32.max) (hy : y.val + 2 ≤ U32.max) :
    callPair (fun a => a + 1#u32) (fun b => b + 2#u32) (x, y) ⦃ ab => ab.1.val = x.val + 1 ∧ ab.2.val = y.val + 2 ⦄ := by
  progress with callPair_spec
  case hf => progress as ⟨ a, ha ⟩; infer_post
  case hg => progress as ⟨ b, hb ⟩; infer_post
  grind

-- Calls f then g in sequence
def callFThenG (f g : U32 → Result U32) (x : U32) : Result U32 := do
  let y ← f x
  g y

theorem callFThenG_spec (f g : U32 → Result U32) (x : U32)
    (mid post : U32 → Prop)
    (hf : f x ⦃ mid ⦄)
    (hg : ∀ y, mid y → g y ⦃ post ⦄) :
    callFThenG f g x ⦃ post ⦄ := by
  simp only [callFThenG]
  apply WP.spec_bind hf
  intro y hy
  exact hg y hy

example (x : U32) (h1 : x.val + 1 ≤ U32.max) (h2 : x.val + 2 ≤ U32.max) :
    callFThenG (fun a => a + 1#u32) (fun b => b + 1#u32) x ⦃ y => y.val = x.val + 2 ⦄ := by
  progress with callFThenG_spec
  case hf => progress as ⟨ a, ha ⟩; infer_post
  case hg =>
    intro y hy
    progress as ⟨ b, hb ⟩
    infer_post
  grind

end higher_order
