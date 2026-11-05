module

public import RawMemoryViews.Initialization
public import Aeneas.Std.Heap.Execution
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model

@[expose] public section

open Aeneas Aeneas.Std SepLogic HeapWP

namespace raw_memory_views.ownership

/- The list records destructor observations, not an extra heap primitive.
   The Rust counterpart appends the payload to a Vec owned by its caller. -/
def dispose (p : RawPtr U8) (events : List U8) : Result (List U8) := do
  let value ← RawPtr.read Repr.u8 p
  Result.checkedModify (State.dealloc Repr.u8 p 1)
  pure (events ++ [value])

/-- The terminating destructor path records exactly one payload and consumes
    the allocation physically, preserving every external frame. -/
theorem dispose.spec (p : RawPtr U8) (value : U8) (events : List U8)
    (h F : Fragment) (s : Heap)
    (owned : sep (alloc Repr.u8 p p.address 1 true)
      (pointsTo Repr.u8 p p.address value) h)
    (disjoint : h.Disjoint F) (matching : Fragment.Matches s (h ∪ F))
    (inv : s.Inv) (authority : RootReturn s p.provenance) :
    Spec (dispose p events) (fun result stop =>
      result = events ++ [value] ∧ Fragment.Matches stop F ∧ stop.Inv ∧
      Heap.read Repr.u8 p stop = none) s := by
  unfold dispose
  apply Spec.bind (RootTriple.read_owned (roots := [p.provenance])
    Repr.u8 p p.address value true (by decide)
    h F s owned disjoint matching inv (by simpa using authority))
  rintro actual s₁ ⟨authority₁, h₁, hd, hm, hi, equal, hp⟩
  subst actual
  have free := dealloc.spec Repr.u8 p p.address value s₁ (by decide)
    (authority₁ p.provenance (by simp)) h₁ F hp hd hm hi
  have free' := Spec.checkedModify.mp free
  have observed : Spec (Result.checkedModify (State.dealloc Repr.u8 p 1))
      (fun _ stop =>
        (∃ h', h'.Disjoint F ∧ Fragment.Matches stop (h' ∪ F) ∧ stop.Inv ∧ empty h') ∧
        Heap.read Repr.u8 p stop = none) s₁ := by
    apply Spec.checkedModify.mpr
    refine ⟨free'.1, ?_⟩
    intro result stop run
    exact ⟨free'.2 result stop run, Heap.dealloc_read_rejected run Repr.u8⟩
  apply Spec.bind observed
  rintro _ stop ⟨⟨h', _, hm', hi', rfl⟩, dead⟩
  exact (Spec.pure _ _ _).mpr ⟨rfl, by simpa using hm', hi', dead⟩

def drop_owned_byte (value : U8) : Result (List U8) := do
  let pointer ← alloc.boxed.Box.into_raw Repr.u8 value
  dispose pointer []

/-- Complete owning-cell client: allocation, move (erased in the value model),
    one destructor observation, and physical reclamation. -/
theorem drop_owned_byte.spec (value : U8) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (drop_owned_byte value) (fun result stop =>
      result = [value] ∧ Fragment.Matches stop F ∧ stop.Inv) s := by
  unfold drop_owned_byte
  apply Spec.bind (intoRaw_return.spec Repr.u8 value s F hi hm)
  rintro pointer start ⟨authority, _, h, hd, hm', hi', hp⟩
  apply Spec.mono (dispose.spec pointer value [] h F start hp hd hm' hi' authority)
  rintro result stop ⟨equal, frame, inv, _⟩
  exact ⟨equal, frame, inv⟩

def p : RawPtr U8 := ⟨0, 256#usize⟩
def allocated : Heap :=
  ((Heap.newBlock Repr.u8 [#v[.data 37#u8]] true p.address none Heap.empty).getD
    (p, Heap.empty)).2
def freed : Heap := (Heap.dealloc Repr.u8 p 1 allocated).getD Heap.empty

private theorem selected {α : Type} (run : Option α) (fallback : α)
    (success : run.isSome = true) : run = some (run.getD fallback) := by
  cases run
  · contradiction
  · rfl

theorem dispose_runs : Runs (dispose p []) allocated [37#u8] freed := by
  unfold dispose
  apply Runs.bind (value := 37#u8) (s₁ := allocated)
  · exact Runs.checkedModify ⟨by native_decide, rfl⟩
  apply Runs.bind (value := ()) (s₁ := freed)
  · exact Runs.checkedModify (selected _ Heap.empty (by native_decide))
  exact Runs.pure _ _

theorem drop_owned_byte_runs :
    Runs (drop_owned_byte 37#u8) Heap.empty [37#u8] freed := by
  unfold drop_owned_byte alloc.boxed.Box.into_raw
  apply Runs.bind (value := p) (s₁ := allocated)
  · apply Runs.allocatingModify
    refine ⟨[#v[.data 37#u8]], p.address, none, ⟨rfl, trivial⟩, ?_⟩
    have success : (Heap.newBlock Repr.u8 [#v[.data 37#u8]] true
        p.address none Heap.empty).map Prod.fst = some p := by native_decide
    generalize h : Heap.newBlock Repr.u8 [#v[.data 37#u8]] true
      p.address none Heap.empty = run at *
    cases run
    · simp at success
    · rename_i pair
      have same := Option.some.inj success
      simp only [allocated, h, Option.getD_some]
      exact congrArg some (Prod.ext same rfl)
  exact dispose_runs

theorem no_double_free :
    (freed.allocations p.provenance).map Block.alive = some false ∧
      Heap.read Repr.u8 p freed = none ∧ Heap.dealloc Repr.u8 p 1 freed = none := by
  native_decide

end raw_memory_views.ownership
