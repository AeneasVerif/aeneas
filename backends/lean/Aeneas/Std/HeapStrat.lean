/- Stratified heap: a higher-order store without cycles. -/
module
public import Aeneas.Std.WP
@[expose] public section

/-! A stratified heap. Level 0 is `Heap0`; `HeapS L` adds on top of `L` a layer holding values one
universe higher. Code of level `n` runs in `Result%n`; a value stored at level `n + 1` may mention
`Result%n` but not `Result%(n+1)`, so no stored function reaches its own cell (no Landin's knot).
Lower-level code runs higher up through `MonadLift` (`liftLevel`), and `step` steps through the lift
(`SpecLift`). The `Stores` instances pick a pointer's layer from the universe of its pointee. -/

namespace Aeneas.Std

open Aeneas.Data.Coinductive

/-- The layer of values in `Type (v + 1)` on top of `L`. -/
structure HeapS (L : Type (v + 1)) : Type (v + 2) where
  lower : L
  upper : Heap.{v + 1}

/-- `Result%n`: the monad of level `n`, `ResultAt` on `Heap0` with `n` layers on top. `Result%0`
is `Result`. -/
macro:max "Result%" noWs n:num : term => do
  let mut h ← `(Heap0)
  for _ in [0:n.getNat] do
    h ← `(HeapS $h)
  `(ResultAt $h)

unseal ResultAt

variable {L : Type (v + 1)}

namespace Result

/-- An effect on `L`, run on the `lower` layers of `HeapS L`. -/
def liftInput : RustEffect.Input L → RustEffect.Input (HeapS L)
  | .guardedModify α pre modify =>
    .guardedModify (ULift.{v + 1} α) (pre ·.lower) fun h hPre =>
      let (a, lower) := modify h.lower hPre
      (⟨a⟩, { h with lower })
  | .fail e => .fail e

def liftOutput : (i : RustEffect.Input L) → RustEffect.Output (liftInput i) → RustEffect.Output i
  | .guardedModify .., o => ⟨o.down.down⟩
  | .fail _, o => nomatch o

/-- Runs code of level `n` at level `n + 1`. -/
def liftLevel {α : Type u} (x : ResultAt L α) : ResultAt (HeapS L) α :=
  match ITree.unfold x with
  | .ret a => ITree.ret a
  | .div => ITree.div
  | .vis i k => ITree.vis (liftInput i) fun o => liftLevel (k (liftOutput i o))
partial_fixpoint

instance : MonadLift (ResultAt L) (ResultAt (HeapS L)) := ⟨liftLevel⟩

/-- The lift into `HeapS L` (`liftM`, what Lean inserts) is `liftLevel` after the lift into `L`. -/
@[simp] theorem monadLift_eq_liftLevel {L' : Type (ul + 1)}
    [MonadLiftT (ResultAt.{ul, u} L') (ResultAt.{v, u} L)] {α : Type u} (x : ResultAt L' α) :
    (monadLift x : ResultAt (HeapS L) α) = liftLevel (monadLift x : ResultAt L α) := rfl

@[simp] theorem liftLevel_ok {α : Type u} (a : α) :
    liftLevel (ok a : ResultAt L α) = ok a := by
  rw [liftLevel.eq_def]; simp only [Result.ok, unfold_ret]; rfl

@[simp] theorem liftLevel_div {α : Type u} :
    liftLevel (div : ResultAt L α) = div := by
  rw [liftLevel.eq_def]; simp only [Result.div, unfold_tau]; rfl

theorem liftLevel_vis {α : Type u} (i : RustEffect.Input L) (k) :
    liftLevel (vis i k : ResultAt L α) =
      vis (liftInput i) fun o => liftLevel (k (liftOutput i o)) := by
  rw [liftLevel.eq_def]; simp only [Result.vis]; erw [unfold_vis]; rfl

@[simp] theorem liftLevel_bind {α : Type u} {β : Type w} (x : ResultAt L α)
    (f : α → ResultAt L β) :
    liftLevel (bind x f) = bind (liftLevel x) (fun a => liftLevel (f a)) := by
  apply CoInd.ext; intro n
  induction n generalizing x
  · rfl
  · rename_i n ih
    cases x using ResultAt.cases with
    | ret a => simp
    | div => simp
    | vis i k =>
      rw [bind_vis, liftLevel_vis, liftLevel_vis, bind_vis]
      simp only [Result.vis]
      erw [vis_approx_1, vis_approx_1]
      congr 1; funext o; exact ih _

open WP in
theorem spec_liftLevel {α : Type u} {x : ResultAt L α} {p : Post α} (h : spec x p) :
    spec (liftLevel x) p := by
  unfold spec at *
  refine DWP.induction
    (P := fun m s => DWP (effectWP (HeapS L)) (liftLevel m) (fun v _ => p v) s) ?_ ?_ h
  · intro v s hv; erw [liftLevel.eq_def]; simpa using hv
  · intro e k s hw; exact hw.elim

open WP in
theorem dspec_liftLevel {α : Type u} {x : ResultAt L α} {p : Post α} (h : dspec x p) :
    dspec (liftLevel x) p := by
  unfold dspec at *
  refine DWLP.coinduction
    (fun m s => ∃ y, m = liftLevel y ∧ DWLP (effectWP L) y (fun v _ => p v) s) ?_ ⟨x, rfl, h⟩
  intro m s ⟨y, hm, hy⟩
  subst hm
  rw [liftLevel.eq_def]
  cases y using ITree.cases with
  | ret v => simpa [FunctionalWP.ret] using hy
  | div => simp [FunctionalWP.div]
  | vis e k => exact (DWLP.vis_view hy).elim

end Result

/-- Lifting from level `L` to `H` (`monadLift`, inserted by Lean in code of level `H` that calls
code of level `L`) keeps the specs. `step` uses it to step through lifted calls; code generic in
the levels (`[MonadLiftT (ResultAt L) (ResultAt H)]`) takes it as an assumption to be proved. -/
class SpecLift (L : Type (ul + 1)) (H : Type (uh + 1))
    [MonadLiftT (ResultAt.{ul, u} L) (ResultAt.{uh, u} H)] : Prop where
  spec_monadLift {α : Type u} {x : ResultAt L α} {p : WP.Post α} :
    WP.spec x p → WP.spec (monadLift x : ResultAt H α) p
  dspec_monadLift {α : Type u} {x : ResultAt L α} {p : WP.Post α} :
    WP.dspec x p → WP.dspec (monadLift x : ResultAt H α) p

instance : SpecLift L L := ⟨id, id⟩

instance {M : Type (um + 1)} [MonadLiftT (ResultAt.{ul, u} L') (ResultAt.{um, u} M)]
    [SpecLift L' M] : SpecLift L' (HeapS M) :=
  ⟨fun h => Result.spec_liftLevel (SpecLift.spec_monadLift h),
   fun h => Result.dspec_liftLevel (SpecLift.dspec_monadLift h)⟩

/-- The top layer of `HeapS L` holds the values of `Type (v + 1)`. -/
instance Stores.upper {T : Type (v + 1)} : Stores (HeapS L) T where
  modify pre f := Result.guardedModify (pre ·.upper) fun h hPre =>
    let (a, upper) := f h.upper hPre
    (a, { h with upper })

/-- The layers below hold the values of the lower universes, through the lift. -/
instance Stores.lower {T : Type u} [Stores L T] : Stores (HeapS L) T where
  modify pre f := Result.liftLevel (Stores.modify (H := L) T pre f)

end Aeneas.Std
