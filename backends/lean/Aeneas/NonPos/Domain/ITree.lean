module
public import Aeneas.NonPos.Domain.Basic
public import Aeneas.Data.Coinductive.ITree

@[expose] public section

/-!
# Interaction trees as domains

`ITree E R` (for *any* effect signature `E`) comes with the chain-complete partial order used by
`partial_fixpoint`. We make it an `OmegaComplete` domain (the supremum of an ω-chain is its
`csup`), and we prove the continuity of the operations which build interaction trees: `ret`
(a constant), `vis` and `bind`.

Nothing here depends on the shape of the effects: the proofs go through the depth-indexed
characterization of the order (`CoInd.le_leN`, `CoInd.leN_le`) and the following description of
the supremum of a chain of trees:
- if some element is `ret r`, the supremum is `ret r` (`ITree.sup_eq_ret`);
- if some element is `vis i k`, the supremum is `vis i` of the suprema of the chains of children
  (`ITree.sup_eq_vis`);
- otherwise all the elements are `div` and so is the supremum (`ITree.sup_eq_div`).

The supremum is defined non-computably (with `csup`). For execution, it is implemented by
`ITree.supImpl`, which scans the chain for the first non-diverging element and builds the
resulting tree lazily (see the caveat there).
-/

namespace NonPos.Domain

open Lean.Order Aeneas.Data.Coinductive

universe u v w

/-! ## Chains as predicates -/

section Range

variable {α : Type u} [PartialOrder α]

/-- The range of a chain, as a predicate (the notion of chain used by `CCPO`). -/
def Chain.range (c : Chain α) : α → Prop := fun x => ∃ n, c n = x

theorem Chain.range_chain (c : Chain α) : chain c.range := by
  rintro x y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases Nat.le_total n m with h | h
  · exact Or.inl (c.le h)
  · exact Or.inr (c.le h)

end Range

/-! ## The domain structure -/

section ITreeDomain

variable {E : Effect.{v}} {R : Type u}

theorem ITree.pure_eq_ret (r : R) : (pure r : ITree E R) = ITree.ret r := rfl

theorem ITree.div_le (x : ITree E R) : (ITree.div : ITree E R) ⊑ x := by
  rw [← ITree.div_is_bot]
  exact bot_le x

/-- The supremum of an ω-chain of interaction trees. -/
noncomputable def ITree.sup (c : Chain (ITree E R)) : ITree E R :=
  CCPO.csup c.range_chain

theorem ITree.le_sup (c : Chain (ITree E R)) (n : Nat) : c n ⊑ ITree.sup c :=
  le_csup c.range_chain ⟨n, rfl⟩

theorem ITree.sup_le (c : Chain (ITree E R)) (x : ITree E R) (h : ∀ n, c n ⊑ x) :
    ITree.sup c ⊑ x :=
  csup_le c.range_chain (by rintro y ⟨n, rfl⟩; exact h n)

/-- The executable implementation of the supremum: scan the chain for the first non-diverging
element; if it is a `vis` node, the children are the (lazily computed) suprema of the chains of
children. If all the elements diverge, the scan diverges, which is the correct value of the
supremum. Evaluating an element may itself diverge without ever producing `div` (it is an
interaction tree, not a value), in which case the scan cannot skip it: execution may diverge even
though the logical value is defined. -/
unsafe def ITree.supImpl (c : Chain (ITree E R)) : ITree E R :=
  scan c.val 0
where
  scan (f : Nat → ITree E R) (n : Nat) : ITree E R :=
    match (f n).unfold with
    | .div => scan f (n + 1)
    | .ret r => .ret r
    | .vis i _ => .vis i fun o => scan (fun m => child (f (n + m)) o) 0
  /-- The child at `o` of a tree of the chain: all the non-diverging elements after the first
  `vis` node have the same shape, so the cast is safe. -/
  child (t : ITree E R) {i : E.I} (o : E.O i) : ITree E R :=
    match t.unfold with
    | .vis _ k => k (unsafeCast o)
    | _ => .div

attribute [implemented_by ITree.supImpl] ITree.sup

instance instOmegaCompleteITree : OmegaComplete (ITree E R) where
  bottom := .div
  bottom_le := ITree.div_le
  sup := ITree.sup
  le_sup := ITree.le_sup
  sup_le := ITree.sup_le

theorem ITree.bottom_eq : (OmegaComplete.bottom : ITree E R) = ITree.div := rfl

theorem ITree.sup_eq (c : Chain (ITree E R)) : OmegaSup.sup c = ITree.sup c := rfl

/-! ## Facts about the order -/

theorem ITree.le_of_ret {r : R} {y : ITree E R} (h : ITree.ret r ⊑ y) : y = ITree.ret r := by
  rw [ITree.le_unfold] at h
  rcases h with h | ⟨r', h1, h2⟩ | ⟨i, k1, k2, h1, _, _⟩
  · exact absurd h not_ret_div
  · rw [ret_inj] at h1; subst h1; exact h2
  · exact absurd h1 not_vis_ret

theorem ITree.le_of_vis {i : E.I} {k : E.O i → ITree E R} {y : ITree E R} (h : ITree.vis i k ⊑ y) :
    ∃ k', y = ITree.vis i k' ∧ ∀ o, k o ⊑ k' o := by
  rw [ITree.le_unfold] at h
  rcases h with h | ⟨r, h1, _⟩ | ⟨i', k1, k2, h1, h2, h3⟩
  · exact absurd h (fun h' => not_div_vis h'.symm)
  · exact absurd h1.symm not_vis_ret
  · have hi := vis_inj_effect h1
    subst hi
    have hk : k = k1 := by
      have := congrArg ITree.unfold h1
      simp only [unfold_vis, ITreeF.vis.injEq, heq_eq_eq, true_and] at this
      exact this
    subst hk
    exact ⟨k2, h2, h3⟩

theorem ITree.le_vis {x : ITree E R} {i : E.I} {k' : E.O i → ITree E R} (h : x ⊑ ITree.vis i k') :
    x = ITree.div ∨ ∃ k, x = ITree.vis i k ∧ ∀ o, k o ⊑ k' o := by
  rw [ITree.le_unfold] at h
  rcases h with h | ⟨r, _, h2⟩ | ⟨i', k1, k2, h1, h2, h3⟩
  · exact Or.inl h
  · exact absurd h2.symm not_vis_ret
  · have hi := vis_inj_effect h2
    subst hi
    have hk : k' = k2 := by
      have := congrArg ITree.unfold h2
      simp only [unfold_vis, ITreeF.vis.injEq, heq_eq_eq, true_and] at this
      exact this
    subst hk
    exact Or.inr ⟨k1, h1, h3⟩

theorem ITree.le_div {x : ITree E R} (h : x ⊑ ITree.div) : x = ITree.div :=
  ITree.le_div_is_div x h

/-- Every tree is `ret`, `vis` or `div`. -/
theorem ITree.cases_eq (x : ITree E R) :
    (∃ r, x = ITree.ret r) ∨ (∃ i k, x = ITree.vis i k) ∨ x = ITree.div := by
  cases x with
  | ret r => exact Or.inl ⟨r, rfl⟩
  | vis i k => exact Or.inr (Or.inl ⟨i, k, rfl⟩)
  | div => exact Or.inr (Or.inr rfl)

/-! ## The shape of the supremum of a chain -/

theorem ITree.sup_eq_div (c : Chain (ITree E R)) (h : ∀ n, c n = ITree.div) :
    ITree.sup c = ITree.div :=
  ITree.le_div (ITree.sup_le c _ (fun n => PartialOrder.rel_of_eq (h n)))

theorem ITree.sup_eq_ret (c : Chain (ITree E R)) {n : Nat} {r : R} (h : c n = ITree.ret r) :
    ITree.sup c = ITree.ret r := by
  have := ITree.le_sup c n
  rw [h] at this
  exact ITree.le_of_ret this

open Classical in
/-- The child at output `o` of a tree which is either `div` or a `vis i _` node (`div` otherwise). -/
noncomputable def ITree.child (i : E.I) (o : E.O i) (t : ITree E R) : ITree E R :=
  match t.unfold with
  | .vis i' k => if h : i = i' then k (cast (congrArg E.O h) o) else .div
  | _ => .div

@[simp] theorem ITree.child_vis (i : E.I) (o : E.O i) (k : E.O i → ITree E R) :
    ITree.child i o (ITree.vis i k) = k o := by
  simp [ITree.child, unfold_vis]

@[simp] theorem ITree.child_div (i : E.I) (o : E.O i) :
    ITree.child i o (ITree.div : ITree E R) = ITree.div := by
  simp [ITree.child, unfold_tau]

@[simp] theorem ITree.child_ret (i : E.I) (o : E.O i) (r : R) :
    ITree.child i o (ITree.ret r : ITree E R) = ITree.div := by
  simp [ITree.child, unfold_ret]

/-- A chain has `vis i`-shape if all its elements are `div` or `vis i _`. -/
def Chain.IsVisShaped (c : Chain (ITree E R)) (i : E.I) : Prop :=
  ∀ m, c m = ITree.div ∨ ∃ k, c m = ITree.vis i k

/-- A chain containing a `vis i` node has `vis i`-shape. -/
theorem Chain.isVisShaped_of_mem (c : Chain (ITree E R)) {n : Nat} {i : E.I} {k : E.O i → ITree E R}
    (h : c n = ITree.vis i k) : c.IsVisShaped i := by
  intro m
  rcases Nat.le_total m n with hmn | hnm
  · have := c.le hmn
    rw [h] at this
    rcases ITree.le_vis this with h' | ⟨k', h', _⟩
    · exact Or.inl h'
    · exact Or.inr ⟨k', h'⟩
  · have := c.le hnm
    rw [h] at this
    obtain ⟨k', h', _⟩ := ITree.le_of_vis this
    exact Or.inr ⟨k', h'⟩

/-- The chain of the children at `o` of a `vis i`-shaped chain. -/
noncomputable def Chain.children (c : Chain (ITree E R)) (i : E.I) (hc : c.IsVisShaped i) (o : E.O i) :
    Chain (ITree E R) where
  val m := ITree.child i o (c m)
  step m := by
    rcases hc m with h | ⟨k, h⟩
    · rw [h, ITree.child_div]
      exact ITree.div_le _
    · have hle := c.step m
      rw [h] at hle
      obtain ⟨k', h', hk⟩ := ITree.le_of_vis hle
      rw [h, h', ITree.child_vis, ITree.child_vis]
      exact hk o

@[simp] theorem Chain.children_apply (c : Chain (ITree E R)) (i : E.I) (hc : c.IsVisShaped i)
    (o : E.O i) (m : Nat) : c.children i hc o m = ITree.child i o (c m) := rfl

/-- The supremum of a chain containing a `vis i` node is `vis i` of the suprema of the children. -/
theorem ITree.sup_eq_vis (c : Chain (ITree E R)) {n : Nat} {i : E.I} {k : E.O i → ITree E R}
    (h : c n = ITree.vis i k) :
    ITree.sup c = ITree.vis i (fun o => ITree.sup (c.children i (c.isVisShaped_of_mem h) o)) := by
  have hc := c.isVisShaped_of_mem h
  -- The shape of the supremum
  have hs := ITree.le_sup c n
  rw [h] at hs
  obtain ⟨ks, hs, hks⟩ := ITree.le_of_vis hs
  apply PartialOrder.rel_antisymm
  · apply ITree.sup_le
    intro m
    rcases hc m with hm | ⟨km, hm⟩
    · rw [hm]; exact ITree.div_le _
    · rw [hm, ITree.le_unfold]
      right; right
      refine ⟨i, km, _, rfl, rfl, fun o => ?_⟩
      have := ITree.le_sup (c.children i hc o) m
      simpa only [Chain.children_apply, hm, ITree.child_vis] using this
  · rw [hs, ITree.le_unfold]
    right; right
    refine ⟨i, _, ks, rfl, rfl, fun o => ?_⟩
    apply ITree.sup_le
    intro m
    have hle := ITree.le_sup c m
    rw [hs] at hle
    rcases hc m with hm | ⟨km, hm⟩
    · simp only [Chain.children_apply, hm, ITree.child_div]
      exact ITree.div_le _
    · rw [hm] at hle
      obtain ⟨ks', hks', hkm⟩ := ITree.le_of_vis hle
      have : ks' = ks := by
        have := congrArg ITree.unfold hks'
        simp only [unfold_vis, ITreeF.vis.injEq, heq_eq_eq, true_and] at this
        exact this.symm
      subst this
      simp only [Chain.children_apply, hm, ITree.child_vis]
      exact hkm o

/-- Trichotomy for chains of trees. -/
theorem Chain.itree_cases (c : Chain (ITree E R)) :
    (∀ n, c n = ITree.div) ∨ (∃ n r, c n = ITree.ret r) ∨ (∃ n i k, c n = ITree.vis i k) := by
  by_cases h : ∀ n, c n = ITree.div
  · exact Or.inl h
  · right
    obtain ⟨n, hn⟩ := Classical.not_forall.mp h
    rcases ITree.cases_eq (c n) with ⟨r, hr⟩ | ⟨i, k, hk⟩ | hd
    · exact Or.inl ⟨n, r, hr⟩
    · exact Or.inr ⟨n, i, k, hk⟩
    · exact absurd hd hn

/-! ## Depth-indexed order -/

theorem ITree.leN_div (x : ITree E R) (n : Nat) :
    CoIndN.le (ITreeF E R) ((ITree.div : ITree E R).approx n) (x.approx n) := by
  cases n with
  | zero => simp [CoIndN.le]
  | succ n =>
    rw [CoIndN.le]
    left
    simp [CoIndN.bot] <;> rfl

theorem ITree.leN_of_le {x y : ITree E R} (h : x ⊑ y) (n : Nat) :
    CoIndN.le (ITreeF E R) (x.approx n) (y.approx n) :=
  CoInd.leN_le _ x y n h

/-! ## Continuity of `bind` -/

section Bind

variable {S : Type w}

theorem ITree.bind_mono_left (k : R → ITree E S) : monotone (fun x : ITree E R => ITree.bind x k) :=
  bind_mono (fun x => x) (fun _ => k) monotone_id (monotone_const k)

theorem ITree.bind_mono_right (x : ITree E R) : monotone (fun k : R → ITree E S => ITree.bind x k) :=
  bind_mono (fun _ => x) (fun k => k) (monotone_const x) monotone_id

/-- The children of the chain `bind (c ·) k` are the `bind` of the children of `c`. -/
theorem Chain.children_bind (c : Chain (ITree E R)) (k : R → ITree E S) (i : E.I)
    (hc : c.IsVisShaped i) (hc' : (c.map (fun x => ITree.bind x k) (ITree.bind_mono_left k)).IsVisShaped i)
    (o : E.O i) :
    (c.map (fun x => ITree.bind x k) (ITree.bind_mono_left k)).children i hc' o =
      (c.children i hc o).map (fun x => ITree.bind x k) (ITree.bind_mono_left k) := by
  apply Chain.ext
  intro m
  simp only [Chain.children_apply, Chain.map_apply]
  rcases hc m with h | ⟨km, h⟩
  · rw [h, itree_div_bind, ITree.child_div, ITree.child_div, itree_div_bind]
  · rw [h, itree_vis_bind, ITree.child_vis, ITree.child_vis]

/-- Continuity of `bind` in its first argument (the `⊑` direction). -/
theorem ITree.bind_sup_left (k : R → ITree E S) (c : Chain (ITree E R)) :
    ITree.bind (ITree.sup c) k ⊑ ITree.sup (c.map (fun x => ITree.bind x k) (ITree.bind_mono_left k)) := by
  apply CoInd.le_leN
  intro n
  induction n generalizing c with
  | zero => simp [CoIndN.le]
  | succ n ih =>
    rcases c.itree_cases with hdiv | ⟨m, r, hr⟩ | ⟨m, i, κ, hv⟩
    · rw [ITree.sup_eq_div c hdiv, itree_div_bind]
      exact ITree.leN_div _ _
    · rw [ITree.sup_eq_ret c hr, itree_ret_bind]
      apply ITree.leN_of_le
      have := ITree.le_sup (c.map (fun x => ITree.bind x k) (ITree.bind_mono_left k)) m
      simpa only [Chain.map_apply, hr, itree_ret_bind] using this
    · have hc := c.isVisShaped_of_mem hv
      rw [ITree.sup_eq_vis c hv, itree_vis_bind]
      have hv' : (c.map (fun x => ITree.bind x k) (ITree.bind_mono_left k)) m =
          ITree.vis i (fun o => ITree.bind (κ o) k) := by
        simp only [Chain.map_apply, hv, itree_vis_bind]
      rw [ITree.sup_eq_vis _ hv']
      apply vis_monoN
      intro o
      rw [Chain.children_bind c k i hc]
      exact ih _

/-- Continuity of `bind` in its second argument (the `⊑` direction). The supremum of a chain of
continuations is taken pointwise. -/
theorem ITree.bind_sup_right (x : ITree E R) (K : Chain (R → ITree E S)) :
    ITree.bind x (OmegaSup.sup K) ⊑ ITree.sup (K.map (fun k => ITree.bind x k) (ITree.bind_mono_right x)) := by
  apply CoInd.le_leN
  intro n
  induction n generalizing x with
  | zero => simp [CoIndN.le]
  | succ n ih =>
    cases x with
    | ret r =>
      rw [ITree.pure_eq_ret, itree_ret_bind]
      apply ITree.leN_of_le
      apply PartialOrder.rel_of_eq
      change ITree.sup (K.coord r) = _
      exact congrArg ITree.sup (Chain.ext (fun m => by simp [Chain.map_apply, itree_ret_bind]))
    | div =>
      rw [itree_div_bind]
      exact ITree.leN_div _ _
    | vis i κ =>
      rw [itree_vis_bind]
      have hv' : (K.map (fun k => ITree.bind (ITree.vis i κ) k) (ITree.bind_mono_right _)) 0 =
          ITree.vis i (fun o => ITree.bind (κ o) (K 0)) := by
        simp only [Chain.map_apply, itree_vis_bind]
      rw [ITree.sup_eq_vis _ hv']
      apply vis_monoN
      intro o
      have heq : (K.map (fun k => ITree.bind (ITree.vis i κ) k) (ITree.bind_mono_right _)).children i
          (Chain.isVisShaped_of_mem _ hv') o =
          K.map (fun k => ITree.bind (κ o) k) (ITree.bind_mono_right (κ o)) := by
        apply Chain.ext
        intro m
        simp only [Chain.children_apply, Chain.map_apply, itree_vis_bind, ITree.child_vis]
      rw [heq]
      exact ih (κ o)

theorem ITree.continuous_bind_left (k : R → ITree E S) :
    Continuous (fun x : ITree E R => ITree.bind x k) :=
  Continuous.of_le (ITree.bind_mono_left k) (fun c => ITree.bind_sup_left k c)

theorem ITree.continuous_bind_right (x : ITree E R) :
    Continuous (fun k : R → ITree E S => ITree.bind x k) :=
  Continuous.of_le (ITree.bind_mono_right x) (fun K => ITree.bind_sup_right x K)

/-- `bind` is jointly continuous. -/
theorem ITree.continuous_bind :
    Continuous (fun p : ITree E R × (R → ITree E S) => ITree.bind p.1 p.2) :=
  Continuous.of_separate (fun k => ITree.continuous_bind_left k) (fun x => ITree.continuous_bind_right x)

/-- The continuity rule for `bind`, in the form used by the `domain_continuity` tactic. -/
theorem Continuous.itree_bind {δ : Type x} [PartialOrder δ] [OmegaComplete δ]
    {m : δ → ITree E R} {k : δ → R → ITree E S}
    (hm : Continuous m) (hk : ∀ a, Continuous (fun d => k d a)) :
    Continuous (fun d => ITree.bind (m d) (k d)) :=
  ITree.continuous_bind.comp (Continuous.prod_mk hm (Continuous.pi_lam hk))

end Bind

/-! ## Continuity of `vis` -/

theorem ITree.vis_mono' (i : E.I) : monotone (fun k : E.O i → ITree E R => ITree.vis i k) :=
  vis_mono _ i (fun k => k) monotone_id

theorem ITree.continuous_vis (i : E.I) : Continuous (fun k : E.O i → ITree E R => ITree.vis i k) := by
  refine ⟨ITree.vis_mono' i, fun K => ?_⟩
  have h0 : (K.map (fun k => ITree.vis i k) (ITree.vis_mono' i)) 0 = ITree.vis i (K 0) := rfl
  change ITree.vis i (OmegaSup.sup K) = ITree.sup _
  rw [ITree.sup_eq_vis _ h0]
  congr 1
  funext o
  change ITree.sup (K.coord o) = _
  exact congrArg ITree.sup (Chain.ext (fun m => by simp [Chain.map_apply]))

theorem Continuous.itree_vis {δ : Type x} [PartialOrder δ] [OmegaComplete δ]
    (i : E.I) {k : δ → E.O i → ITree E R} (hk : ∀ o, Continuous (fun d => k d o)) :
    Continuous (fun d => ITree.vis i (k d)) :=
  (ITree.continuous_vis i).comp (Continuous.pi_lam hk)

end ITreeDomain

end NonPos.Domain
