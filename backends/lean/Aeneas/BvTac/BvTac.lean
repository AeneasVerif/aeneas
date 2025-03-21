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
    throwError "Could not infer the bitwidth to use by from the goal, please provide it explicitly with the syntax: `bv_tac n`"
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

partial def bvTacPreprocess (n : Option Expr): TacticM Unit := do
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
    /- Figure out the bitwidth if the user didn't provide it -/
    let n ← do
      match n with
      | some n => pure n
      | none => getn
    /- Then apply bvify -/
    bvifyTac n Utils.Location.wildcard
    trace[BvTac] "Goal after `bvifyTac`: {← getMainGoal}"
    /- Call `simp_all ` to normalize the goal a bit -/
    let simpLemmas ← bvifySimpExt.getTheorems
    let simprocs ← bvifySimprocExt.getSimprocs
    Utils.simpAll {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 0} true
                  {simprocs := #[simprocs], simpThms := #[simpLemmas]}
    allGoals do
    trace[BvTac] "Goal after `simp_all`: {← getMainGoal}"

def optElabTerm (e : Option (TSyntax `term)) : TacticM (Option Expr) := do
  match e with
  | none => pure none
  | some e => pure (some (← Lean.Elab.Tactic.elabTerm e none))

elab "bv_tac_preprocess" n:(colGt term)? : tactic => do
  bvTacPreprocess (← optElabTerm n)

open Lean.Elab.Tactic.BVDecide.Frontend Lean.Elab in
/--
  `bv_tac` solves goals about bit-vectors.

  Calling `bv_tac n` is equivalent to:
  `bv_tac_preprocess n; bv_decide`
  which is itself mostly equivalent to:
  `bvify n at *; simp_all only; bv_decide`
-/
elab "bv_tac" cfg:Parser.Tactic.optConfig n:(colGt term)? : tactic =>
  withMainContext do
  Tactic.focus do
  -- Preprocess
  trace[BvTac] "Input bitwidth: {n}"
  bvTacPreprocess (← optElabTerm n)
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

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac
  simp

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac 32
  simp

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac 32; simp

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

example
  (a : U32)
  (b : U32)
  (ha : a.val < 3329)
  (hb : b.val < 3329)
  (c1 : U32)
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (_ : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (_ : c3.bv = c2.bv >>> 16#i32.toNat) :
  (c1.bv - 3329#32 + (3329#32 &&& c3.bv)) % 3329#32 = (a.bv + b.bv) % 3329#32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16#i32.toNat)
  (h : (↑a : ℕ) < 6658 ∧ (↑b : ℕ) = 3329)
  (_ : ¬c2 = 0#u32) :
  c2 = 65535#u32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (h0 : (↑a : ℕ) ≤ 6658)
  (ha : (↑a : ℕ) < (↑b : ℕ) + 3329)
  (hb : (↑b : ℕ) ≤ 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (hc3_1 : (↑c3 : ℕ) = (↑(3329#u32 &&& c2) : ℕ))
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = core.num.U32.wrapping_add c1 c3) :
  c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧ c4.bv < 3329#32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (c1 : U32)
  (hc1 : (↑c1 : ℕ) = (↑a : ℕ) + (↑b : ℕ))
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16)
  (h : ¬c3 = 0#u32) :
  c3 = 65535#u32
  := by bv_tac

example
  (a : U32)
  (b : U32)
  (h : a.val < 3329 ∧ b.val < 3329 ∨ a.val < 6658 ∧ b.val = 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16) :
  (decide (c2 = 0#u32) || decide (c2 = 65535#u32)) = true
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (h : a.val < 3329 ∧ b.val < 3329 ∨ a.val < 6658 ∧ b.val = 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (hc3_1 : c3.val = (3329#u32 &&& c2).val)
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = core.num.U32.wrapping_add c1 c3) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329) ∧ c4.val < 3329
  := by
  bv_tac 32

end Aeneas.BvTac
