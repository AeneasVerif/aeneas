import Aeneas.Std.Primitives
import Aeneas.Std.Delab
import Std.Do
import Aeneas.Std.Spec
import Aeneas.Std.WP
import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect
import Aeneas.Std
import Std
import Aeneas.Tactic.Step
import Aeneas

open Aeneas
open Std Result WP Data Coinductive Effect Lean.Order

def State := Nat

inductive CEffect.I where
| set : State → CEffect.I
| get : CEffect.I
| choose : CEffect.I
-- there is an issue that both threads have to return the return type.
-- maybe this is fine, and you can just bind an operation that returns Unit?
-- i could make a generalized ITree definition which allows you to do stuff to the return type in Effect?

def CEffect.O (i : CEffect.I) : Type :=
  match i with
  | .set _n => Unit
  | .get => State
  | .choose => Bool

def CEffect : Effect := {
  I := CEffect.I
  O := CEffect.O
}

def ITreeS : Type → Type := ITree CEffect

-- can just use coinductive props!
coinductive sspec {α} (p : Post α) : (s : State → Prop) → (x : ITreeS α) → Prop where
| ret : ∀ x s, p x → sspec p s (ITree.ret x)
| set : ∀ k s n, s n → sspec p s k → sspec p s (ITree.vis (.set n) (fun _ => k))
| get : ∀ k s, (∀ n, s n → sspec p s (k n)) → sspec p s (ITree.vis .get k)
| fork : ∀ k s, sspec p s (k true) → sspec p s (k false) → sspec p s (ITree.vis .choose k)

-- coinductive possible {α} : (T : Type) → State → (T → ITreeS α) → State → α → Prop where
-- | ret : ∀ T x s t pool, pool t = .ret x → possible T s pool s x
-- | fork : ∀ T pool s1 s2 a,
--   possible (Option T) s1 (fun x => match x with | .some x => _ | .none => _) s2 a
--   → possible T s1 pool s2 a

-- def choice {R : Type} (a b : ITreeS R) : ITreeS R := .vis .choose (fun b => if b then a else b)

-- def par {R} (t1 t2 : ITreeS R) : ITreeS R :=
  -- ITree.cases _ _ _ t1
