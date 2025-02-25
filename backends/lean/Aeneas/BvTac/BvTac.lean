import Aeneas.Bvify

namespace Aeneas.BvTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Bvify Utils

def disjConj : Std.HashSet Name := Std.HashSet.ofList [
  ``And, ``Or
]

def arithConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``BEq.beq, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

partial def getn : TacticM Expr := do
  let mgoal ← getMainGoal
  let goalTy ← mgoal.getType
  let raiseError : TacticM Expr :=
    throwError "The goal doesn't have the proper shape: expected a proposition only involving (in-)equality between bitvectors"
  let fromBitVecTy (ty : Expr) : TacticM Expr :=
    ty.consumeMData.withApp fun _ args => do
    if args.size == 1 then
      pure args[0]!
    else
      raiseError
  let rec aux (ty : Expr) : TacticM Expr := do
    ty.consumeMData.withApp fun f args => do
    if f.isConst then
      let f := f.constName!
      if f == ``Eq ∧ args.size == 3 then
        fromBitVecTy args[0]!
      else if f ∈ disjConj ∧ args.size == 2 then
        aux args[0]!
      else if f ∈ arithConsts ∧ args.size == 4 then
        fromBitVecTy args[0]!
      else
        raiseError
    else
      raiseError
  aux goalTy

partial def bvTacPreprocess : TacticM Unit := do
  /- First figure out the bisize, by looking at the goal -/
  let n ← getn
  /- Then apply bvify -/
  bvifyTac n Utils.Location.wildcard

elab "bv_tac_preprocess" : tactic =>
  bvTacPreprocess

open Lean.Elab.Tactic.BVDecide.Frontend in
elab "bv_tac" cfg:Parser.Tactic.optConfig : tactic =>
  withMainContext do
  -- Preprocess
  bvTacPreprocess
  -- Call bv_decide
  let cfg ← elabBVDecideConfig cfg
  IO.FS.withTempFile fun _ lratFile => do
    let cfg ← BVDecide.Frontend.TacticContext.new lratFile cfg
    liftMetaFinishingTactic fun g => do
      discard <| bvDecide g cfg

/-!
# Tests
-/
open Std

example (x y : U8) (h : x.val ≤ y.val) : x.bv ≤ y.bv := by
  bv_tac

example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv := by
  bv_tac

end Aeneas.BvTac
