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

inductive SEffect.I where
| set : State → SEffect.I
| get : SEffect.I

def SEffect.O (i : SEffect.I) : Type :=
  match i with
  | .set _n => Unit
  | .get => State

def SEffect : Effect := {
   I := SEffect.I
   O := SEffect.O
}

def ITreeS : Type → Type := ITree SEffect

-- can just use coinductive props!
coinductive sspec {α} (p : Post α) : (s : State → Prop) → (x : ITreeS α) → Prop where
| ret : ∀ x s, p x → sspec p s (ITree.ret x)
| set : ∀ k s n, s n → sspec p s k → sspec p s (ITree.vis (.set n) (fun _ => k))
| get : ∀ k s, (∀ n, s n → sspec p s (k n)) → sspec p s (ITree.vis .get k)
-- | vis : ∀ k, (∀ b, coinSpec p (k b)) → coinSpec p (ITree.vis () k)
