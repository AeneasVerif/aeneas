module

public import Aeneas.Std.Heap.Specs
public import Aeneas.Std.Primitives
public import Aeneas.Std.WP
public import Aeneas.Data.Coinductive.ITreeWP.DWP
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Primitives

@[expose] public section

namespace Aeneas.Std.HeapWP

open Aeneas.Data.Coinductive SepLogic

unseal Result

/-- All admissible successors must satisfy the continuation. OOM is an accepted
    abort; other failures are rejected. Checked accesses still enforce enabledness. -/
def effectWP : EffectWP RustEffect where
  State := State
  wp effect C s :=
    match effect with
    | .guardedModify _ modify =>
      ∀ x s', modify s x s' → C ⟨x⟩ s'
    | .fail e => e = .oom

instance : effectWP.Monotonic where
  wp_monotonic := by
    intro effect C C' h s he
    cases effect
    · exact fun x s' hx => h _ _ (he x s' hx)
    · exact he

instance : effectWP.Conjunctive where
  wp_conj := by
    intro effect s demands hne hall
    cases effect
    · exact fun x s' hx C' hC' => hall C' hC' x s' hx
    · obtain ⟨C, hC⟩ := hne
      exact hall C hC

/-- Correctness of all returns, allowing OOM but not panic, UB, or divergence. -/
def Spec (c : Result α) (Q : α → State → Prop) (s : State) : Prop :=
  DWP effectWP c Q s

theorem Spec.pure (x : α) (Q : α → State → Prop) (s : State) :
    Spec (Result.ok x) Q s ↔ Q x s :=
  DWP.ret_iff

theorem Spec.bind {α : Type u} {β : Type v} {c : Result α} {k : α → Result β}
    {Q : α → State → Prop} {R : β → State → Prop}
    (hc : Spec c Q s) (hk : ∀ x s', Q x s' → Spec (k x) R s') :
    Spec (Aeneas.Std.bind c k) R s :=
  DWP.bind hc hk

theorem Spec.mono (hc : Spec c Q s) (hq : ∀ x s', Q x s' → R x s') :
    Spec c R s :=
  DWP.mono hc hq

theorem Spec.fail (e : Error) : Spec (Result.fail e : Result α) Q s ↔ e = .oom :=
  ⟨fun h => DWP.vis_view h, fun h => DWP.vis h⟩

theorem Spec.oom : Spec (Result.oom : Result α) Q s :=
  (Spec.fail .oom).mpr rfl

/-- Lift an effect-free specification without exposing Result's representation
    in client proofs. An OOM abort has no continuation or final-value obligation. -/
theorem Spec.of_spec {c : Result α} {P : α → Prop} (hc : WP.spec c P) (s : State) :
    Spec c (fun result s' => P result ∧ s' = s) s := by
  rcases WP.spec_ok_or_oom hc with ⟨value, rfl, hp⟩ | rfl
  · exact (Spec.pure _ _ _).mpr ⟨hp, rfl⟩
  · exact Spec.oom

theorem Spec.div : ¬ Spec (Result.div : Result α) Q s :=
  DWP.div_false

theorem Spec.guardedModify {modify : State → α → State → Prop} :
    Spec (Result.guardedModify modify) Q s ↔
      ∀ x s', modify s x s' → Q x s' := by
  constructor
  · intro h
    exact fun x s' hx => DWP.ret_iff.mp (DWP.vis_view h x s' hx)
  · intro hpost
    exact DWP.vis (fun x s' hx => DWP.ret_iff.mpr (hpost x s' hx))

theorem checked.enabled (modify : State → α → State → Prop) (s : State) :
    ∃ answer s', State.checked modify s answer s' := by
  classical
  by_cases h : ∃ value s', modify s value s'
  · obtain ⟨value, s', ht⟩ := h
    exact ⟨some value, s', ht⟩
  · exact ⟨none, s, h, rfl⟩

/-- On a disabled heap operation, the only effect answer is failure at the unchanged heap.
`checkedModify` then maps that answer to `Result.fail .undef` via `Result.ofOption`. -/
theorem checked.failure {modify : State → α → State → Prop}
    (disabled : ¬ ∃ value next, modify s value next) :
    State.checked modify s answer s' ↔ answer = none ∧ s' = s := by
  cases answer
  · simp [State.checked, disabled]
  · rename_i value
    constructor
    · intro h
      exact (disabled ⟨value, s', h⟩).elim
    · rintro ⟨h, _⟩
      cases h

/-- Invalid accesses cannot become vacuously correct: a disabled checked request
    produces undef, so its WP still requires a successful transition. -/
theorem Spec.checkedModify {modify : State → α → State → Prop} :
    Spec (Result.checkedModify modify) Q s ↔
      (∃ x s', modify s x s') ∧ ∀ x s', modify s x s' → Q x s' := by
  classical
  constructor
  · intro h
    have ht := DWP.vis_view h
    constructor
    · by_cases hn : ∃ x s', modify s x s'
      · exact hn
      · exact Error.noConfusion ((Spec.fail .undef).mp (ht none s ⟨hn, rfl⟩))
    · intro x s' hx
      exact DWP.ret_iff.mp (ht (some x) s' hx)
  · rintro ⟨henabled, hpost⟩
    apply DWP.vis
    intro answer s' ht
    cases answer
    · exact (ht.1 henabled).elim
    · rename_i value
      exact DWP.ret_iff.mpr (hpost value s' ht)

/-- Allocation/exposure has only universal success obligations. An unavailable
    placement returns OOM, unlike an invalid checked access. -/
theorem Spec.allocatingModify {modify : State → α → State → Prop} :
    Spec (Result.allocatingModify modify) Q s ↔
      ∀ x s', modify s x s' → Q x s' := by
  constructor
  · intro h x s' hx
    exact DWP.ret_iff.mp (DWP.vis_view h (some x) s' hx)
  · intro hpost
    apply DWP.vis
    intro answer s' ht
    cases answer
    · exact (Spec.fail .oom).mpr rfl
    · rename_i value
      exact DWP.ret_iff.mpr (hpost value s' ht)

/-- Every admissible encoding must satisfy the continuation.
    Encoding completeness is independent of this universal obligation. -/
theorem Spec.choose (repr : Repr ty) (value : ty)
    (Q : {data : Vector Byte repr.size // repr.encode value data} → State → Prop)
    (s : State) :
    Spec (repr.choose value) Q s ↔ ∀ data decoded, Q ⟨data, decoded⟩ s := by
  rw [Repr.choose, Spec.guardedModify]
  constructor
  · intro h data decoded
    exact h ⟨data, decoded⟩ s rfl
  · intro h
    exact fun ⟨data, decoded⟩ _ he => he ▸ h data decoded

theorem Spec.chooseList (repr : Repr ty) (values : List ty)
    (Q : {data : List (Vector Byte repr.size) //
      repr.encodeList values data} → State → Prop) (s : State) :
    Spec (repr.chooseList values) Q s ↔ ∀ data decoded, Q ⟨data, decoded⟩ s := by
  rw [Repr.chooseList, Spec.guardedModify]
  constructor
  · intro h data decoded
    exact h ⟨data, decoded⟩ s rfl
  · intro h
    exact fun ⟨data, decoded⟩ _ he => he ▸ h data decoded

/-- Choice always terminates with admissible bytes for the requested value, and
neither reads nor changes the heap. -/
theorem choose.spec (repr : Repr ty) (value : ty) (s : State) :
    Spec (repr.choose value)
      (fun data s' => repr.encode value data.val ∧ s' = s) s :=
  Spec.choose repr value _ s |>.mpr fun _ decoded => ⟨decoded, rfl⟩

/-- A framed separation contract for the generated computation itself. -/
def Triple (P : Assertion) (c : Result α) (Q : α → Assertion) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    Spec c (fun x s' => ∃ h', h'.Disjoint F ∧
      Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h') s

/-- State-specific effect contract, retaining arbitrary matching frames. -/
def TripleAt (P : Assertion) (c : Result α) (Q : α → Assertion) (s : State) : Prop :=
  ∀ h F, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    Spec c (fun x s' => ∃ h', h'.Disjoint F ∧
      Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h') s

theorem TripleAt.checkedModify {modify : State → α → State → Prop}
    (ht : SepLogic.TripleAt P modify Q s) :
    TripleAt P (Result.checkedModify modify) Q s := by
  intro h F hp hd hm hi
  exact Spec.checkedModify.mpr (ht h F hp hd hm hi)

theorem frameAt (ht : TripleAt P c Q s) :
    TripleAt (sep P R) c (fun x => sep (Q x) R) s := by
  intro h F ⟨a, b, hab, he, hp, hr⟩ hf hm hi
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  have ht' := ht a (b ∪ F) hp (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi
  apply DWP.mono ht'
  rintro x s' ⟨a', hd, hm', hi', hq⟩
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

theorem Triple.guardedModify {modify : State → α → State → Prop}
    (ht : SepLogic.Triple P modify Q) :
    Triple P (Result.guardedModify modify) Q := by
  intro h F s hp hd hm hi
  exact Spec.guardedModify.mpr (ht h F s hp hd hm hi).2

theorem Triple.checkedModify {modify : State → α → State → Prop}
    (ht : SepLogic.Triple P modify Q) :
    Triple P (Result.checkedModify modify) Q := by
  intro h F s hp hd hm hi
  exact Spec.checkedModify.mpr (ht h F s hp hd hm hi)

/-- The chosen encoding carries its admissibility proof and preserves the heap. -/
theorem Triple.choose (P : Assertion) (repr : Repr ty) (value : ty) :
    Triple P (repr.choose value) (fun _ => P) := by
  intro h F s hp hd hm hi
  apply Spec.choose _ _ _ _ |>.mpr
  exact fun _ _ => ⟨h, hd, hm, hi, hp⟩

theorem Triple.chooseList (P : Assertion) (repr : Repr ty) (values : List ty) :
    Triple P (repr.chooseList values) (fun _ => P) := by
  intro h F s hp hd hm hi
  apply Spec.chooseList _ _ _ _ |>.mpr
  exact fun _ _ => ⟨h, hd, hm, hi, hp⟩

theorem Triple.pure (P : Assertion) (x : α) :
    Triple P (Result.ok x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi
  exact Spec.pure _ _ _ |>.mpr ⟨h, hd, hm, hi, rfl, hp⟩

theorem Triple.bind {α : Type u} {β : Type v} {c : Result α} {k : α → Result β}
    {Q : α → Assertion} {R : β → Assertion}
    (hc : Triple P c Q) (hk : ∀ x, Triple (Q x) (k x) R) :
    Triple P (Aeneas.Std.bind c k) R := by
  intro h F s hp hd hm hi
  apply Spec.bind (hc h F s hp hd hm hi)
  rintro x s' ⟨h', hd', hm', hi', hq⟩
  exact hk x h' F s' hq hd' hm' hi'

theorem Triple.conseq (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : Triple P' c Q') : Triple P c Q := by
  intro h F s hP hd hm hi
  exact DWP.mono (ht h F s (hp h hP) hd hm hi) fun x s' ⟨h', hd', hm', hi', hQ⟩ =>
    ⟨h', hd', hm', hi', hq x h' hQ⟩

theorem Triple.pure_pre (ht : A → Triple P c Q) :
    Triple (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi
  exact ht ha h F s hp hd hm hi

theorem frame (ht : Triple P c Q) :
    Triple (sep P R) c (fun x => sep (Q x) R) := by
  intro h F s ⟨a, b, hab, he, hp, hr⟩ hf hm hi
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  have ht' := ht a (b ∪ F) s hp (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi
  apply DWP.mono ht'
  rintro x s' ⟨a', hd, hm', hi', hq⟩
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

end Aeneas.Std.HeapWP
