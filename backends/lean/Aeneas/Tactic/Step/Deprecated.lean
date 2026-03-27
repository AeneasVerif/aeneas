/-
Copyright (c) 2024-2025 Inria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho
-/
import Aeneas.Tactic.Step.Step
import Aeneas.Tactic.Step.StepStar
import Aeneas.Tactic.Step.StepArraySpec

/-!
# Deprecated `progress` syntax and attributes

The `progress` tactic has been renamed to `step`. This file provides backward-compatible
aliases that emit deprecation warnings. All deprecated names delegate to their `step`
counterparts.

Set `set_option Aeneas.Deprecated.progressWarning false` to silence the warnings.
-/

namespace Aeneas.Deprecated

open Lean Elab Meta Tactic

/-- When `true` (default), using the deprecated `progress` syntax emits a warning. -/
register_option Aeneas.Deprecated.progressWarning : Bool := {
  defValue := true
  descr := "Emit warnings when using the deprecated `progress` syntax (renamed to `step`)"
}

private def emitProgressWarning (what : String) : CoreM Unit := do
  if Aeneas.Deprecated.progressWarning.get (← getOptions) then
    logWarning m!"`{what}` has been renamed to `{what.replace "progress" "step"}`. \
      The `{what}` syntax is deprecated and will be removed in a future version. \
      Set `set_option Aeneas.Deprecated.progressWarning false` to silence this warning."

/-!
## Deprecated tactic syntax
-/

/-- **Deprecated:** Use `step` instead. -/
elab (name := deprecatedProgress) "progress" args:Step.stepArgs : tactic => do
  emitProgressWarning "progress"
  let (config, withArg, ids, idsUserProvided, postsBasename, byTac) ← Step.parseStepArgs args
  Step.evalStep config none withArg ids idsUserProvided postsBasename byTac *> return ()

/-- **Deprecated:** Use `step?` instead. -/
elab tk:"progress?" args:Step.stepArgs : tactic => do
  emitProgressWarning "progress?"
  let (config, withArg, ids, idsUserProvided, postsBasename, byTac) ← Step.parseStepArgs args
  let stats ← Step.evalStep config none withArg ids idsUserProvided postsBasename byTac
  let mut stxArgs := args.raw
  if stxArgs[1].isNone then
    let withArg := mkNullNode #[mkAtom "with", ← stats.toSyntax]
    stxArgs := stxArgs.setArg 1 withArg
  let tac := mkNode `Aeneas.Step.step #[mkAtom "step", stxArgs]
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq tac
  Meta.Tactic.TryThis.addSuggestion tk fmt.pretty (origSpan? := ← getRef)

/-- **Deprecated:** Use `step*` / `step*?` instead. -/
syntax (name := deprecatedProgressStar) "progress" noWs ("*" <|> "*?") StepStar.«step*_args» : tactic

@[tactic deprecatedProgressStar]
def evalDeprecatedProgressStarTac : Tactic := fun stx => do
  match stx with
  | `(tactic| progress* $args:«step*_args») =>
    emitProgressWarning "progress*"
    let (cfg, fuel) ← StepStar.parseArgs args
    StepStar.evalStepStar cfg fuel *> pure ()
  | `(tactic| progress*? $args:«step*_args») =>
    emitProgressWarning "progress*?"
    let (cfg, fuel) ← StepStar.parseArgs args
    let info ← StepStar.evalStepStar cfg fuel
    let suggestion ← info.script.toSyntax
    let suggestion ← `(tacticSeq|$(suggestion)*)
    Aesop.addTryThisTacticSeqSuggestion stx suggestion (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

/-!
## Deprecated command syntax
-/

/-- **Deprecated:** Use `step_array_spec` instead. -/
syntax (name := deprecatedProgressArraySpec)
  ("local" <|> "scoped")? "progress_array_spec" "(" "name" " := " ident ")" ident "[" ident "]" noWs "!"
    " { " ident " => " term " } " " by " tacticSeq : command

open Lean.Elab.Command in
@[command_elab deprecatedProgressArraySpec]
def evalDeprecatedProgressArraySpec : CommandElab := fun stx => do
  liftCoreM <| emitProgressWarning "progress_array_spec"
  match stx with
  | `($[$vis]? progress_array_spec (name := $thm_name:ident) $array:ident [ $i:ident ]! { $x:ident => $pred:term } by $tac:tacticSeq) => do
    -- Rewrite as step_array_spec and delegate
    let newStx ← match vis with
    | none => `(command| step_array_spec (name := $thm_name) $array[$i]! { $x => $pred } by $tac)
    | some vis =>
      if vis.raw.isOfKind `token.local then
        `(command| local step_array_spec (name := $thm_name) $array[$i]! { $x => $pred } by $tac)
      else if vis.raw.isOfKind `token.scoped then
        `(command| scoped step_array_spec (name := $thm_name) $array[$i]! { $x => $pred } by $tac)
      else throwUnsupportedSyntax
    elabCommand newStx
  | _ => throwUnsupportedSyntax

/-!
## Deprecated attributes

These register theorems in the same `step` database as their non-deprecated counterparts.
-/

/-- **Deprecated:** Use `@[step]` instead. -/
private def progressDeprecatedAttrImpl : AttributeImpl where
  «name» := `progress
  descr := "Deprecated: use `step` instead. Adds theorems to the `step` database."
  add := fun thName stx attrKind => do
    emitProgressWarning "progress"
    Attribute.Builtin.ensureNoArgs stx
    Step.stepAttr.attr.add thName stx attrKind
  erase := fun thName => do
    Step.stepAttr.attr.erase thName

initialize _progressDeprecatedAttr : Unit ←
  registerBuiltinAttribute progressDeprecatedAttrImpl

/-- **Deprecated:** Use `@[step_pure]` instead. -/
private def progressPureDeprecatedAttrImpl : AttributeImpl where
  «name» := `progress_pure
  descr := "Deprecated: use `step_pure` instead."
  add := fun thName stx attrKind => do
    emitProgressWarning "progress_pure"
    Step.stepPureAttribute.attr.add thName stx attrKind

initialize _progressPureDeprecatedAttr : Unit ←
  registerBuiltinAttribute progressPureDeprecatedAttrImpl

/-- **Deprecated:** Use `@[step_pure_def]` instead. -/
private def progressPureDefDeprecatedAttrImpl : AttributeImpl where
  «name» := `progress_pure_def
  descr := "Deprecated: use `step_pure_def` instead."
  add := fun thName stx attrKind => do
    emitProgressWarning "progress_pure_def"
    Step.stepPureDefAttribute.attr.add thName stx attrKind

initialize _progressPureDefDeprecatedAttr : Unit ←
  registerBuiltinAttribute progressPureDefDeprecatedAttrImpl

/-- **Deprecated:** Use `@[step_simps]` instead. Forwards to `step_simps`. -/
initialize do
  mkSimpAttr `progress_simps
    "Deprecated: use `step_simps` instead. Forwards to `step_simps`."
    Step.stepSimpExt

/-- **Deprecated:** Use `@[step_pre_simps]` instead. Forwards to `step_pre_simps`. -/
initialize do
  mkSimpAttr `progress_pre_simps
    "Deprecated: use `step_pre_simps` instead. Forwards to `step_pre_simps`."
    Step.stepPreSimpExt

/-- **Deprecated:** Use `@[step_post_simps]` instead. Forwards to `step_post_simps`. -/
initialize do
  mkSimpAttr `progress_post_simps
    "Deprecated: use `step_post_simps` instead. Forwards to `step_post_simps`."
    Step.stepPostSimpExt

/-- **Deprecated:** Use `@[step_post_simps_proc]` instead. Forwards to `step_post_simps_proc`. -/
initialize do
  Simp.mkSimprocAttr `progress_post_simps_proc
    "Deprecated: use `step_post_simps_proc` instead. Forwards to `step_post_simps_proc`."
    Step.stepPostSimprocExt `Aeneas.Deprecated.progressPostSimpsProcDeprecated

end Aeneas.Deprecated
