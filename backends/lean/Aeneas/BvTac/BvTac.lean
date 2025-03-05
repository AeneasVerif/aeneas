import Aeneas.Bvify
import Aeneas.Std
import Aeneas.BvTac.Init

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
  let goalTy ← instantiateMVars (← mgoal.getType)
  let raiseError : TacticM Expr :=
    throwError "The goal doesn't have the proper shape: expected a proposition only involving (in-)equalities between bitvectors"
  let fromBitVecTy (ty : Expr) : TacticM Expr :=
    ty.consumeMData.withApp fun f args => do
    trace[BvTac] "fromBitVecTy: {f}, {args}"
    if args.size == 1 then
      pure args[0]!
    else
      raiseError
  trace[BvTac] "Goal type: {goalTy}"
  let rec aux (ty : Expr) : TacticM Expr := do
    ty.consumeMData.withApp fun f args => do
    trace[BvTac] "Exploring term: {f}, {args}"
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
  Elab.Tactic.focus do
  trace[BvTac] "Original goal: {← getMainGoal}"
  /- First try simplifying the goal - if it is an (in-)equality between scalars, it may get
     the bitwidth to use for the bit-vectors might be obvious from the goal: we marked some
     theorems wiht `bvify_simps` for this reason. -/
  Bvify.bvifyTacSimp (Utils.Location.targets #[] true)
  /- The simp call above may have proven the goal (unlikely, but we have to take this
     into account) -/
  allGoals do
    trace[BvTac] "Goal after `bvifyTacSimp`: {← getMainGoal}"
    /- Figure out the bitwith -/
    let n ← getn
    /- Then apply bvify -/
    bvifyTac n Utils.Location.wildcard
    trace[BvTac] "Goal after `bvifyTac`: {← getMainGoal}"
    /- Call `simp_all ` to normalize the goal a bit -/
    let simpLemmas ← bvifySimpExt.getTheorems
    Utils.simpAll {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 0} true
                  -- Simprocs
                  ScalarTac.scalarTacSimpRocs
                  -- Simp theorems
                  [simpLemmas]
                  -- Unfoldings
                  []
                  -- Simp lemmas
                  []
                  -- Hypotheses
                  []
    allGoals do
    trace[BvTac] "Goal after `simp_all`: {← getMainGoal}"

elab "bv_tac_preprocess" : tactic =>
  bvTacPreprocess

open Lean.Elab.Tactic.BVDecide.Frontend Lean.Elab in
elab "bv_tac" cfg:Parser.Tactic.optConfig : tactic =>
  withMainContext do
  Tactic.focus do
  -- Preprocess
  bvTacPreprocess
  -- The preprocessing step may have proven the goal
  allGoals do
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

example
  (a : U32)
  (b : U32)
  (ha : a.val < 3329)
  (hb : b.val < 3329)
  (c1 : U32)
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16#i32.toNat)
  (_ : ¬c3 = 0#u32) :
  c3 = 65535#u32
  := by
  bv_tac

end Aeneas.BvTac
