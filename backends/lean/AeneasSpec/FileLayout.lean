module

public import AeneasSpec.Output
public import AeneasSpec.List.ClassReps
public import AeneasSpec.List.PullOrder
public import AeneasSpec.ToMathlib.Combinatorics.Digraph.Maps
public import AeneasSpec.ToMathlib.Data.Fintype.TransGen
public import AeneasSpec.ToMathlib.Data.List.Nodup
public import AeneasSpec.ToMathlib.Order.Condensation

/-!
# Choosing files and ordering declarations

The algorithm, given the items in source order (`src`):

1. Divide the items to write into subsets by the Rust module where they are defined.
2. Merge subsets that are mutually dependent: the files are the strongly connected components of
   the module graph. A file imports the files containing the dependencies of its items.
3. Within each file, group mutually dependent items into blocks (the strongly connected components
   of the item graph), and order the blocks by source position, moving a block forward to just
   before the first block that needs it.

Files are identified by their first item in source order (`FileId := ctxt.items`); naming them is
a separate step.

## Main definitions

* `Output.FilesFollowModules`: the choice of files made in steps 1 and 2.
* `TranslationCtx.algorithm`: the algorithm.

## Main statements

* `TranslationCtx.algorithm_spec`: the output satisfies Lean's requirements
  (`Output.LeanValid`) and the choice of files (`Output.FilesFollowModules`).
-/

@[expose] public section

namespace Aeneas.Spec

open Relation

namespace TranslationCtx

variable (ctxt : TranslationCtx)

/-- The module graph: module `a` uses module `b` when an item of `a` depends on an item of `b`. -/
def moduleGraph : Digraph RustModule :=
  ctxt.deps.map (·.val.rustModule)

end TranslationCtx

namespace Output

variable {ctxt : TranslationCtx} {FileId : Type*} (out : Output ctxt FileId)

/-- The algorithm's choice of files and of the order within them, given the items in source order
`src`: two items are in the same file exactly when their Rust modules are in the same strongly
connected component of the module graph, and blocks follow the source order except where a block is
moved forward for a block that needs it. -/
structure FilesFollowModules (src : List ctxt.items) : Prop where
  /-- Every file has at least one block. -/
  files_nonempty : ∀ f ∈ out.files, out.blocks f ≠ []
  /-- Items share a file exactly when their modules are in the same strongly connected component
  of the module graph: each module reaches the other. -/
  same_file_iff : ∀ i j : ctxt.items, ∀ f g, out.InFile i f → out.InFile j g →
    (f = g ↔ AntisymmRel (ReflTransGen ctxt.moduleGraph.Adj) i.val.rustModule j.val.rustModule)
  /-- Blocks are ordered by their first user: if an item `u` of the file is or needs `i` (directly
  or not), and comes in `src` before every item of the file that is or needs `j`, then the block of
  `i` comes before the block of `j`. So a block keeps its source position unless an earlier block
  needs it, and then it is moved forward to just before the first such block. -/
  source_order : ∀ i j u : ctxt.items, ∀ f k l, out.InBlock i f k → out.InBlock j f l →
    out.InFile u f → ReflTransGen ctxt.deps.Adj u i →
    (∀ v, out.InFile v f → ReflTransGen ctxt.deps.Adj v j → src.idxOf u < src.idxOf v) → k < l

variable {out}

theorem InBlock.inFile {i : ctxt.items} {f : FileId} {k : Nat} (h : out.InBlock i f k) :
    out.InFile i f := by
  obtain ⟨hf, hk, hi⟩ := h
  exact ⟨hf, List.mem_flatten.2 ⟨_, List.getElem_mem hk, hi⟩⟩

/-- If `i` comes before `j` in the source but the block of `j` comes before the block of `i`, then
`j` is needed, directly or not, by an item of the file that comes no later than `i` in the
source. -/
theorem FilesFollowModules.exists_transGen_of_lt {src : List ctxt.items}
    (h : out.FilesFollowModules src) {i j : ctxt.items} {f : FileId} {k l : Nat}
    (hik : out.InBlock i f k) (hjl : out.InBlock j f l) (hsrc : src.idxOf i < src.idxOf j)
    (hlk : l < k) :
    ∃ v, out.InFile v f ∧ src.idxOf v ≤ src.idxOf i ∧ TransGen ctxt.deps.Adj v j := by
  by_contra hne
  push Not at hne
  have := h.source_order i j i f k l hik hjl hik.inFile .refl fun v hv hvj => by
    rcases reflTransGen_iff_eq_or_transGen.1 hvj with rfl | hvj
    · exact hsrc
    · by_contra hle
      exact hne v hv (by omega) hvj
  omega

end Output

namespace TranslationCtx

/-! ### The algorithm -/

variable (ctxt : TranslationCtx) [DecidableRel ctxt.deps.Adj]

/-- One step of the module graph, on items: `i` and `j` are in the same module, or the module of
`i` uses the module of `j`. -/
def ModStep (i j : ctxt.items) : Prop :=
  i.val.rustModule = j.val.rustModule ∨ ctxt.moduleGraph.Adj i.val.rustModule j.val.rustModule

instance : DecidableRel ctxt.ModStep := fun i j => by
  unfold ModStep moduleGraph; infer_instance

variable (src : List ctxt.items)

/-- The items to write, in source order. -/
def itemsToWrite : List ctxt.items :=
  src.filter ctxt.NeedsWriting

/-- One item per file: the first item of each file, in source order. -/
def fileReps : List ctxt.items :=
  (ctxt.itemsToWrite src).classReps (AntisymmRel (ReflTransGen ctxt.ModStep))

/-- The items of file `f`, in source order. -/
def fileMembers (f : ctxt.items) : List ctxt.items :=
  (ctxt.itemsToWrite src).classOf (AntisymmRel (ReflTransGen ctxt.ModStep)) f

/-- One item per block of file `f` (its first item), in the order the blocks are written. -/
def blockOrder (f : ctxt.items) : List ctxt.items :=
  ((ctxt.fileMembers src f).classReps (AntisymmRel (ReflTransGen ctxt.deps.Adj))).pullOrder
    (CondensationAdj ctxt.deps.Adj ctxt.deps.Adj)

/-- The blocks of file `f`, in order. -/
def fileBlocks (f : ctxt.items) : List (List ctxt.items) :=
  (ctxt.blockOrder src f).map
    ((ctxt.fileMembers src f).classOf (AntisymmRel (ReflTransGen ctxt.deps.Adj)))

/-- The files that file `f` imports: those containing a dependency of one of its items. -/
def fileImports (f : ctxt.items) : Finset ctxt.items :=
  (ctxt.fileReps src).toFinset.filter (CondensationAdj ctxt.ModStep ctxt.deps.Adj f)

/-- The output of the algorithm. -/
def algorithm : Output ctxt ctxt.items where
  files := (ctxt.fileReps src).toFinset
  imports := ctxt.fileImports src
  blocks := ctxt.fileBlocks src

/-! ### Correctness -/

omit [DecidableRel ctxt.deps.Adj] in
/-- Following module steps between items is following module dependencies. -/
theorem reflTransGen_modStep_iff {i j : ctxt.items} :
    ReflTransGen ctxt.ModStep i j ↔
      ReflTransGen ctxt.moduleGraph.Adj i.val.rustModule j.val.rustModule := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      rcases hbc with h | h
      · exact h ▸ ih
      · exact ih.tail h
  · intro h
    suffices ∀ a, ReflTransGen ctxt.moduleGraph.Adj i.val.rustModule a →
        ∀ j : ctxt.items, j.val.rustModule = a → ReflTransGen ctxt.ModStep i j from
      this _ h j rfl
    intro a h
    induction h with
    | refl => intro j hj; exact .single (Or.inl hj.symm)
    | tail _ hcb ih =>
      intro j hj
      obtain ⟨i', j', hadj, hi', hj'⟩ := hcb
      exact (ih i' hi').tail (Or.inr ⟨i', j', hadj, rfl, hj'.trans hj.symm⟩)

omit [DecidableRel ctxt.deps.Adj] in
/-- Two items are in the same file exactly when their modules are strongly connected. -/
theorem antisymmRel_modStep_iff {i j : ctxt.items} :
    AntisymmRel (ReflTransGen ctxt.ModStep) i j ↔
      AntisymmRel (ReflTransGen ctxt.moduleGraph.Adj) i.val.rustModule j.val.rustModule :=
  ⟨fun h => ⟨ctxt.reflTransGen_modStep_iff.1 h.1, ctxt.reflTransGen_modStep_iff.1 h.2⟩,
    fun h => ⟨ctxt.reflTransGen_modStep_iff.2 h.1, ctxt.reflTransGen_modStep_iff.2 h.2⟩⟩

omit [DecidableRel ctxt.deps.Adj] in
theorem adj_le_modStep : ctxt.deps.Adj ≤ ctxt.ModStep :=
  fun i j h => Or.inr ⟨i, j, h, rfl, rfl⟩

variable {ctxt src}

omit [DecidableRel ctxt.deps.Adj] in
theorem mem_itemsToWrite (hsrc : ∀ i, i ∈ src) {i : ctxt.items} :
    i ∈ ctxt.itemsToWrite src ↔ ctxt.NeedsWriting i := by
  simp [itemsToWrite, hsrc]

theorem mem_fileMembers {f i : ctxt.items} :
    i ∈ ctxt.fileMembers src f ↔
      i ∈ ctxt.itemsToWrite src ∧ AntisymmRel (ReflTransGen ctxt.ModStep) f i :=
  List.mem_classOf

theorem blockOrder_spec (f : ctxt.items) :
    (ctxt.blockOrder src f).Nodup ∧
      (∀ x, x ∈ ctxt.blockOrder src f ↔
        x ∈ (ctxt.fileMembers src f).classReps (AntisymmRel (ReflTransGen ctxt.deps.Adj))) ∧
      ∀ (a b : Nat) (ha : a < (ctxt.blockOrder src f).length)
        (hb : b < (ctxt.blockOrder src f).length),
        CondensationAdj ctxt.deps.Adj ctxt.deps.Adj (ctxt.blockOrder src f)[a]
          (ctxt.blockOrder src f)[b] → b < a :=
  List.pullOrder_spec (condensationAdj_acyclic le_rfl)

theorem mem_flatten_fileBlocks (f i : ctxt.items) :
    i ∈ (ctxt.fileBlocks src f).flatten ↔ i ∈ ctxt.fileMembers src f := by
  apply List.mem_flatten_map_classOf
  intro x hx
  obtain ⟨r, hr, hrx⟩ :=
    List.exists_mem_classReps (equivalence_antisymmRel_reflTransGen ctxt.deps.Adj) hx
  exact ⟨r, ((blockOrder_spec f).2.1 r).2 hr, hrx⟩

theorem inFile_iff (i f : ctxt.items) :
    (ctxt.algorithm src).InFile i f ↔ f ∈ ctxt.fileReps src ∧ i ∈ ctxt.fileMembers src f := by
  simp only [Output.InFile, algorithm, List.mem_toFinset, mem_flatten_fileBlocks]

theorem inBlock_iff (i f : ctxt.items) (k : Nat) :
    (ctxt.algorithm src).InBlock i f k ↔ f ∈ ctxt.fileReps src ∧
      ∃ hk : k < (ctxt.blockOrder src f).length, i ∈ ctxt.fileMembers src f ∧
        AntisymmRel (ReflTransGen ctxt.deps.Adj) (ctxt.blockOrder src f)[k] i := by
  simp only [Output.InBlock, algorithm, List.mem_toFinset, fileBlocks, List.length_map,
    List.getElem_map, List.mem_classOf]

omit [DecidableRel ctxt.deps.Adj] in
/-- Whatever depends, directly or not, on an item that needs writing needs writing too. -/
theorem needsWriting_of_reflTransGen (hwf : ctxt.WellFormed) {w x : ctxt.items}
    (h : ReflTransGen ctxt.deps.Adj w x) (hx : ctxt.NeedsWriting x) : ctxt.NeedsWriting w := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact ih (hwf.aeneas.needsWritingOfDep _ _ hbc hx)

/-- A chain of dependencies between two items of a file stays in that file. -/
theorem mem_fileMembers_of_reflTransGen (hsrc : ∀ i, i ∈ src) (hwf : ctxt.WellFormed)
    {f u w i : ctxt.items} (hu : u ∈ ctxt.fileMembers src f) (hi : i ∈ ctxt.fileMembers src f)
    (huw : ReflTransGen ctxt.deps.Adj u w) (hwi : ReflTransGen ctxt.deps.Adj w i) :
    w ∈ ctxt.fileMembers src f := by
  rw [mem_fileMembers] at hu hi ⊢
  refine ⟨(mem_itemsToWrite hsrc).2 ?_, ?_, ?_⟩
  · exact needsWriting_of_reflTransGen hwf hwi ((mem_itemsToWrite hsrc).1 hi.1)
  · exact hu.2.1.trans (ReflTransGen.mono ctxt.adj_le_modStep _ _ huw)
  · exact (ReflTransGen.mono ctxt.adj_le_modStep _ _ hwi).trans hi.2.2

theorem fileMembers_sublist (f : ctxt.items) : (ctxt.fileMembers src f).Sublist src := by
  simp only [fileMembers, List.classOf, itemsToWrite]
  exact List.filter_sublist.trans List.filter_sublist

/-- The algorithm's output satisfies Lean's requirements and the proposed choice of files, for any
listing `src` of the items with each item exactly once. -/
theorem algorithm_spec (hsrc : ∀ i, i ∈ src) (hnd : src.Nodup) (hwf : ctxt.WellFormed) :
    (ctxt.algorithm src).LeanValid ∧ (ctxt.algorithm src).FilesFollowModules src := by
  have heF := equivalence_antisymmRel_reflTransGen ctxt.ModStep
  have heB := equivalence_antisymmRel_reflTransGen ctxt.deps.Adj
  have htwnd : (ctxt.itemsToWrite src).Nodup := hnd.filter _
  have hmnd : ∀ f, (ctxt.fileMembers src f).Nodup := fun f => htwnd.filter _
  have hrep_toWrite : ∀ f ∈ ctxt.fileReps src, f ∈ ctxt.itemsToWrite src :=
    fun f hf => List.mem_of_mem_classReps hf
  have hblock_rep : ∀ f b, b ∈ ctxt.blockOrder src f →
      b ∈ (ctxt.fileMembers src f).classReps (AntisymmRel (ReflTransGen ctxt.deps.Adj)) :=
    fun f b hb => ((blockOrder_spec f).2.1 b).1 hb
  -- Two files containing related items are the same file.
  have hsame_file : ∀ f ∈ ctxt.fileReps src, ∀ g ∈ ctxt.fileReps src, ∀ i j,
      AntisymmRel (ReflTransGen ctxt.ModStep) f i → AntisymmRel (ReflTransGen ctxt.ModStep) g j →
      AntisymmRel (ReflTransGen ctxt.ModStep) i j → f = g :=
    fun f hf g hg i j hfi hgj hij =>
      List.eq_of_mem_classReps heF hf hg (heF.trans hfi (heF.trans hij (heF.symm hgj)))
  -- Every item that needs writing is in some file.
  have hcover : ∀ i, ctxt.NeedsWriting i → ∃ f, (ctxt.algorithm src).InFile i f := by
    intro i hi
    have hiw := (mem_itemsToWrite hsrc).2 hi
    obtain ⟨f, hf, hfi⟩ := List.exists_mem_classReps heF hiw
    exact ⟨f, (inFile_iff i f).2 ⟨hf, mem_fileMembers.2 ⟨hiw, hfi⟩⟩⟩
  refine ⟨⟨?imports_subset, ?imports_acyclic, ?blocks_nonempty, ?nodup, ?unique_file,
    ?complete, ?deps_visible, ?mutual_exact, ?mutual_same_kind⟩,
    ⟨?files_nonempty, ?same_file, ?source_order⟩⟩
  case imports_subset =>
    intro f _ g hg
    exact (Finset.mem_filter.1 hg).1
  case imports_acyclic =>
    intro f h
    exact condensationAdj_acyclic ctxt.adj_le_modStep f
      (TransGen.mono (fun _ _ hab => (Finset.mem_filter.1 hab).2) f f h)
  case blocks_nonempty =>
    intro f _ b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have hcm := List.mem_of_mem_classReps (hblock_rep f c hc)
    exact List.ne_nil_of_mem (List.mem_classOf.2 ⟨hcm, heB.refl c⟩)
  case nodup =>
    intro f _
    refine List.nodup_flatten_map_classOf heB (hmnd f) (blockOrder_spec f).1 ?_
    intro b hb c hc hbc
    exact List.eq_of_mem_classReps heB (hblock_rep f b hb) (hblock_rep f c hc) hbc
  case unique_file =>
    intro i f g hf hg
    obtain ⟨hf, hif⟩ := (inFile_iff i f).1 hf
    obtain ⟨hg, hig⟩ := (inFile_iff i g).1 hg
    exact hsame_file f hf g hg i i (mem_fileMembers.1 hif).2 (mem_fileMembers.1 hig).2
      (heF.refl i)
  case complete =>
    intro i
    refine ⟨fun ⟨f, hf⟩ => ?_, hcover i⟩
    exact (mem_itemsToWrite hsrc).1 (mem_fileMembers.1 ((inFile_iff i f).1 hf).2).1
  case deps_visible =>
    intro i j f g k l hik hjl hij
    obtain ⟨hf, hk, hif, hbi⟩ := (inBlock_iff i f k).1 hik
    obtain ⟨hg, hl, hjg, hbj⟩ := (inBlock_iff j g l).1 hjl
    by_cases hfg : f = g
    · subst hfg
      left
      refine ⟨rfl, ?_⟩
      by_cases hkl : k = l
      · exact hkl ▸ le_refl k
      · -- Different blocks of the same file: the block of `j` comes first.
        have hne : (ctxt.blockOrder src f)[k] ≠ (ctxt.blockOrder src f)[l] := fun h =>
          hkl ((blockOrder_spec f).1.getElem_inj_iff.1 h)
        have hdep : CondensationAdj ctxt.deps.Adj ctxt.deps.Adj (ctxt.blockOrder src f)[k]
            (ctxt.blockOrder src f)[l] := by
          refine ⟨fun h => hne ?_, i, j, hbi, hbj, hij⟩
          exact List.eq_of_mem_classReps heB (hblock_rep f _ (List.getElem_mem hk))
            (hblock_rep f _ (List.getElem_mem hl)) h
        exact le_of_lt ((blockOrder_spec f).2.2 k l hk hl hdep)
    · -- Different files: `f` imports `g`.
      right
      refine TransGen.single (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hg, ?_⟩)
      refine ⟨fun h => hfg (List.eq_of_mem_classReps heF hf hg h), i, j,
        (mem_fileMembers.1 hif).2, (mem_fileMembers.1 hjg).2, hij⟩
  case mutual_exact =>
    intro i j f k hik hjk
    obtain ⟨_, _, _, hbi⟩ := (inBlock_iff i f k).1 hik
    obtain ⟨_, _, _, hbj⟩ := (inBlock_iff j f k).1 hjk
    exact antisymmRel_reflTransGen_iff.1 (heB.trans (heB.symm hbi) hbj)
  case mutual_same_kind =>
    intro i j f k hik hjk
    obtain ⟨_, _, hif, hbi⟩ := (inBlock_iff i f k).1 hik
    obtain ⟨_, _, _, hbj⟩ := (inBlock_iff j f k).1 hjk
    rcases antisymmRel_reflTransGen_iff.1 (heB.trans (heB.symm hbi) hbj) with rfl | hmut
    · rfl
    · exact hwf.aeneas.noMixedRecursion i j
        ((mem_itemsToWrite hsrc).1 (mem_fileMembers.1 hif).1) hmut
  case files_nonempty =>
    intro f hf
    have hf := List.mem_toFinset.1 hf
    have hfm : f ∈ ctxt.fileMembers src f := mem_fileMembers.2 ⟨hrep_toWrite f hf, heF.refl f⟩
    obtain ⟨b, hb, -⟩ := List.exists_mem_classReps heB hfm
    simp only [algorithm, fileBlocks, ne_eq, List.map_eq_nil_iff]
    exact List.ne_nil_of_mem (((blockOrder_spec f).2.1 b).2 hb)
  case same_file =>
    intro i j f g hif hjg
    obtain ⟨hf, hif⟩ := (inFile_iff i f).1 hif
    obtain ⟨hg, hjg⟩ := (inFile_iff j g).1 hjg
    have hfi := (mem_fileMembers.1 hif).2
    have hgj := (mem_fileMembers.1 hjg).2
    rw [← antisymmRel_modStep_iff]
    constructor
    · rintro rfl
      exact heF.trans (heF.symm hfi) hgj
    · intro hij
      exact hsame_file f hf g hg i j hfi hgj hij
  case source_order =>
    intro i j u f k l hik hjl huf hui hfirst
    obtain ⟨hf, hk, hif, hbi⟩ := (inBlock_iff i f k).1 hik
    obtain ⟨-, hl, -, hbj⟩ := (inBlock_iff j f l).1 hjl
    have huf := ((inFile_iff u f).1 huf).2
    -- The blocks of the file, one representative each, in source order.
    set Lf := (ctxt.fileMembers src f).classReps (AntisymmRel (ReflTransGen ctxt.deps.Adj))
      with hLf
    have hmemb : ∀ x, x ∈ ctxt.blockOrder src f ↔ x ∈ Lf := (blockOrder_spec f).2.1
    have hLf_sub : Lf.Sublist (ctxt.fileMembers src f) := List.classReps_sublist _
    have hmem_pair : (ctxt.fileMembers src f).Pairwise (fun a b => src.idxOf a < src.idxOf b) :=
      hnd.pairwise_idxOf_lt.sublist (fileMembers_sublist f)
    -- The block of `u`, which comes no later than `u`.
    obtain ⟨ru, hru, hruu⟩ := List.exists_mem_classReps heB huf
    have hru_le : src.idxOf ru ≤ src.idxOf u :=
      List.Pairwise.rel_of_mem_classReps heB (R := fun a b => src.idxOf a ≤ src.idxOf b)
        (fun _ => le_rfl) (hmem_pair.imp le_of_lt) hru huf hruu
    -- The chain from `u` to `i` gives a chain of blocks.
    have hpath : ∀ w, ReflTransGen ctxt.deps.Adj u w → ReflTransGen ctxt.deps.Adj w i →
        ∃ rw ∈ Lf, AntisymmRel (ReflTransGen ctxt.deps.Adj) rw w ∧
          ReflTransGen (fun a b => CondensationAdj ctxt.deps.Adj ctxt.deps.Adj a b ∧ b ∈ Lf)
            ru rw := by
      intro w huw
      induction huw with
      | refl => intro _; exact ⟨ru, hru, hruu, .refl⟩
      | @tail a b hua hab ih =>
        intro hbi'
        obtain ⟨ra, hra, hraa, hpa⟩ := ih (ReflTransGen.head hab hbi')
        have hb := mem_fileMembers_of_reflTransGen hsrc hwf huf hif (hua.tail hab) hbi'
        obtain ⟨rb, hrb, hrbb⟩ := List.exists_mem_classReps heB hb
        by_cases hrab : AntisymmRel (ReflTransGen ctxt.deps.Adj) ra rb
        · obtain rfl := List.eq_of_mem_classReps heB hra hrb hrab
          exact ⟨ra, hra, hrbb, hpa⟩
        · exact ⟨rb, hrb, hrbb, hpa.tail ⟨⟨hrab, a, b, hraa, hrbb, hab⟩, hrb⟩⟩
    obtain ⟨ri, hri, hrii, hpi⟩ := hpath i hui .refl
    obtain rfl : ri = (ctxt.blockOrder src f)[k] :=
      List.eq_of_mem_classReps heB hri ((hmemb _).1 (List.getElem_mem hk))
        (heB.trans hrii (heB.symm hbi))
    -- `pullOrder` compares items with `DecidableEq`.
    have hlt :
        @List.idxOf _ instBEqOfDecidableEq (ctxt.blockOrder src f)[k] (ctxt.blockOrder src f) <
        @List.idxOf _ instBEqOfDecidableEq (ctxt.blockOrder src f)[l] (ctxt.blockOrder src f) := by
      refine List.pullOrder_idxOf_lt (condensationAdj_acyclic le_rfl) (fun a => src.idxOf a)
        (hmem_pair.sublist hLf_sub) hru hpi ?_
      -- Everything in the file that needs the block of `j` needs `j`, so comes after `u`.
      intro v hv hvb
      have hvj : ReflTransGen ctxt.deps.Adj v j := by
        refine (reflTransGen_closed (fun a b hab => ?_) v _ hvb).trans hbj.1
        obtain ⟨⟨-, i', j', hai, hbj', hij⟩, -⟩ := hab
        exact (hai.1.tail hij).trans hbj'.2
      exact lt_of_le_of_lt hru_le (hfirst v ((inFile_iff v f).2 ⟨hf, hLf_sub.subset hv⟩) hvj)
    rwa [@List.Nodup.idxOf_getElem _ instBEqOfDecidableEq _ _ (blockOrder_spec f).1,
      @List.Nodup.idxOf_getElem _ instBEqOfDecidableEq _ _ (blockOrder_spec f).1] at hlt

end TranslationCtx

end Aeneas.Spec
