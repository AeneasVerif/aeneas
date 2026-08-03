import Aeneas.Tactic.Step.Init
import Aeneas.Std.Primitives

/-!
# Bind-assoc simproc with binder-name preservation

The standard simp lemma `bind_assoc_eq` rewrites

    `bind (bind e g) h  =  bind e (fun x => bind (g x) h)`

but the RHS always carries the generic binder name `x`.  When `simp`
applies it repeatedly to a left-nested bind chain produced by `do`-block
inlining, **every** original continuation name is replaced by `x`, causing
name collisions (`x`, `x_1`, `x✝`) and making hypotheses inaccessible
after `step*`.

The `bindAssocPreservingNames` simproc below performs the identical rewrite
but reads the binder name from `g`'s lambda, so `z0`, `z1`, `o`, etc. are
carried through.
-/

namespace Aeneas.Step

open Lean Meta

/-- Simproc that reassociates `bind (bind e g) h` while preserving the binder
    name from the inner continuation `g`. -/
simproc_decl bindAssocPreservingNames
    (@Bind.bind _ _ _ _ (@Bind.bind _ _ _ _ _ _) _) := fun e => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``Bind.bind && args.size == 6 do return .continue
  let comp := args[4]!
  let compArgs := comp.getAppArgs
  unless comp.getAppFn.isConstOf ``Bind.bind && compArgs.size == 6 do return .continue
  -- Left-nested: bind (bind innerE innerG) outerH
  let innerE   := compArgs[4]!
  let innerG   := compArgs[5]!
  let outerH   := args[5]!
  -- Binder info from innerG
  let (name, bi, domain) :=
    if innerG.isLambda then (innerG.bindingName!, innerG.bindingInfo!, innerG.bindingDomain!)
    else (`x, BinderInfo.default, compArgs[2]!)
  -- Build result: bind innerE (fun NAME => bind (innerG NAME) outerH)
  let newCont ← withLocalDecl name bi domain fun fvar => do
    let gApplied :=
      if innerG.isLambda then innerG.bindingBody!.instantiate1 fvar
      else mkApp innerG fvar
    let innerBind := mkAppN fn #[args[0]!, args[1]!, compArgs[3]!, args[3]!, gApplied, outerH]
    mkLambdaFVars #[fvar] innerBind
  let newExpr := mkAppN fn #[args[0]!, args[1]!, compArgs[2]!, args[3]!, innerE, newCont]
  -- Proof: bind_assoc_eq innerE innerG outerH
  let proof ← mkAppM ``Aeneas.Std.bind_assoc_eq #[innerE, innerG, outerH]
  return .done { expr := newExpr, proof? := some proof }

attribute [step_simps_proc] bindAssocPreservingNames

end Aeneas.Step
