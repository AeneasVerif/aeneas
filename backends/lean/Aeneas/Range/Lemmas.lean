/- This pattern is often introduced when desugaring for loops -/
@[simp]
theorem List.foldl_Prod_to_MProd_fst_eq {α β : Type u} {γ : Type v} (f : α → β → γ → α × β)
  (a0 : α) (b0 : β) (l) :
  (List.foldl (fun b a => MProd.mk (f b.fst b.snd a).fst (f b.fst b.snd a).snd) ⟨a0, b0⟩ l).fst =
  (List.foldl (fun b a => (f b.fst b.snd a)) (a0, b0) l).fst := by
  revert a0 b0
  induction l <;>
  simp_all only [foldl_nil, implies_true, foldl_cons, implies_true]

/- This pattern is often introduced when desugaring for loops -/
@[simp]
theorem List.foldl_Prod_to_MProd_snd_eq {α β : Type u} {γ : Type v} (f : α → β → γ → α × β)
  (a0 : α) (b0 : β) (l) :
  (List.foldl (fun b a => MProd.mk (f b.fst b.snd a).fst (f b.fst b.snd a).snd) ⟨a0, b0⟩ l).snd =
  (List.foldl (fun b a => (f b.fst b.snd a)) (a0, b0) l).snd := by
  revert a0 b0
  induction l <;>
  simp_all only [foldl_nil, implies_true, foldl_cons, implies_true]

@[simp]
theorem mem_range'_step_one (x start len : Nat) :
  x ∈ List.range' start len ↔ (start ≤ x ∧ x < start + len) := by
  simp only [List.mem_range', Nat.one_mul]
  constructor <;> intro h
  . obtain ⟨ i, h ⟩ := h
    omega
  . exists x - start
    omega

@[simp]
theorem mem_std_range_step_one (x n0 n1 : Nat) :
  x ∈ [n0:n1] ↔ (n0 ≤ x ∧ x < n1) := by
  simp only [Membership.mem, Nat.mod_one, and_true]

@[simp]
theorem idRun_foldl (l : List α) (f : β → α → Id β) : l.foldlM f x = l.foldl f x := by
  revert x
  induction l <;> intros <;> simp only [List.foldlM_cons, bind, List.foldl_cons, List.foldlM_nil, pure, List.foldl_nil, *]
