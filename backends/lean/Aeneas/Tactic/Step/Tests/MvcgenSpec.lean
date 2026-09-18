import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Std.RawPtr
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Aeneas.SepLogic Aeneas.Data.Coinductive
open Aeneas.Std.WP
open _root_.Std.Do (Triple SPred PostCond WPMonad)

set_option mvcgen.warning false

/-! `Std.Do` terms are explicit to avoid collisions with the SL triple notation. -/

private abbrev heapTriple {α : Type u} (m : Result α) (P : Heap → Prop)
    (Q : α → Heap → Prop) : Prop :=
  Triple (ps := .arg (ULift.{u + 1} Heap) .pure) (Result.toMvcgen m)
    (fun heap => SPred.pure (P heap.down))
    (PostCond.noThrow fun value heap => SPred.pure (Q value.down heap.down))

example : WPMonad Result.{u + 1} (.arg (ULift.{u + 1} Heap) .pure) := inferInstance

example {α : Type u} (value : α) :
    heapTriple (pure value : Result α) (fun _ => True) (fun result _ => result = value) := by
  mvcgen

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    heapTriple (x + y) (fun _ => True) (fun z _ => z.val = x.val + y.val) := by
  mvcgen; scalar_tac

example {x y : U8} :
    heapTriple
      (do
        if x < 10#u8 then x * 2#u8 else pure y)
      (fun _ => True) (fun z _ => z.val ≠ y.val → z.val < 20) := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    heapTriple (Array.update arr i a) (fun _ => True) (fun r _ => r.get? i = some a) := by
  mvcgen <;> (intros; grind)

namespace Aeneas.MvcgenTests

def guardedIdentity (n : Nat) : Result Nat :=
  Result.guardedModify (fun _ => True) fun heap _ => (n, heap)

@[local step]
theorem guardedIdentity_spec (n : Nat) :
    spec (guardedIdentity n) (fun value => value = n) := by
  apply ispec_guardedModify
  intro heap _ frame hCompatible
  exact ⟨True.intro, heap, hCompatible, rfl, rfl⟩

example (n : Nat) :
    heapTriple
      (do
        let value ← guardedIdentity n
        guardedIdentity (value + 1))
      (fun _ => True) (fun value _ => value = n + 1) := by
  mvcgen; grind

example (value : Nat) :
    heapTriple (MutRawPtr.alloc value) (fun _ => True) (fun p heap => (p ↦ value) heap) := by
  mvcgen

example :
    heapTriple
      (do
        let p ← MutRawPtr.alloc (0 : Nat)
        p.write 7
        p.read)
      (fun _ => True) (fun value _ => value = 7) := by
  have hWrite (p : MutRawPtr Nat) := MutRawPtr.write.spec.mvcgen_spec p 0 7
  have hRead (p : MutRawPtr Nat) := RawPtr.read.spec.mvcgen_spec p 7
  mvcgen [hWrite, hRead]; grind [sep_pure_l]

example (p : MutRawPtr Nat) (value : Nat) :
    ispec (p ↦ value) p.read (fun result => ipure (result = value) ∗ p ↦ value) := by
  apply ispec_iff_mvcgen.mpr
  intro F
  have hFrame := ispec_to_mvcgen (ispec_frame (RawPtr.read.spec p value) F)
  exact hFrame

@[local step]
theorem read_partial (p : MutRawPtr Nat) (value : Nat) :
    dispec (p ↦ value) p.read (fun result => ipure (result = value) ∗ p ↦ value) :=
  ispec_dispec (RawPtr.read.spec p value)

example (p : MutRawPtr Nat) (value : Nat) :
    heapTriple p.read
      (fun heap => (p ↦ value) heap ∧ Result.terminates p.read heap)
      (fun result heap => (ipure (result = value) ∗ p ↦ value) heap) := by
  mvcgen [read_partial.mvcgen_spec]
  grind

def delayedDiv : Result Nat :=
  Result.vis (.guardedModify Unit (fun _ => True) fun heap _ => ((), heap))
    (fun _ => Result.div)

@[local step]
theorem delayedDiv_dspec : dspec delayedDiv (fun _ => False) := by
  rw [dspec, dispec_iff]
  intro F heap _
  exact PartialSpec.vis ⟨True.intro, PartialSpec.div⟩

example : delayedDiv ≠ Result.div := by
  simp [delayedDiv]

theorem delayedDiv_not_terminates (heap : Heap) :
    ¬ Result.terminates delayedDiv heap := by
  intro h
  exact TotalSpec.div_false (TotalSpec.vis_view h).2

example :
    heapTriple delayedDiv (Result.terminates delayedDiv) (fun _ _ => False) :=
  delayedDiv_dspec.mvcgen_spec

example :
    ¬ heapTriple delayedDiv (fun _ => True) (fun _ _ => True) := by
  intro h
  exact delayedDiv_not_terminates ∅ (Result.toMvcgen_totalSpec.mp (h ⟨∅⟩ True.intro))

def maybeDiv (n : Nat) : Result Nat :=
  if n = 0 then delayedDiv else Result.ok n

@[local step]
theorem maybeDiv_dspec (n : Nat) : dspec (maybeDiv n) (fun value => value = n) := by
  unfold maybeDiv
  split
  · exact dspec_mono delayedDiv_dspec (fun _ h => h.elim)
  · exact (dspec_ok n).mpr rfl

example (n : Nat) (h : n ≠ 0) :
    heapTriple (maybeDiv n) (fun _ => True) (fun value _ => value = n) := by
  mvcgen
  simp [Result.terminates, maybeDiv, h, Result.ok]

section
unseal Result

example (e : Error) :
    ¬ heapTriple (Result.fail e : Result Nat) (fun _ => True) (fun _ _ => True) := by
  intro h
  exact (Result.toMvcgen_totalSpec.mp (h ⟨∅⟩ True.intro)).vis_view

example :
    ¬ heapTriple (Result.div : Result Nat) (fun _ => True) (fun _ _ => True) := by
  intro h
  exact (Result.toMvcgen_totalSpec.mp (h ⟨∅⟩ True.intro)).div_false

end

end Aeneas.MvcgenTests
