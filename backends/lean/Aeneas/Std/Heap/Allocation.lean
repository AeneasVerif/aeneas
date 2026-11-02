module

public import Aeneas.Std.Heap.Specs
import all Aeneas.Std.Scalar.Types

/-! Fresh view creation and whole-view retirement. Placement feasibility is an
input-state obligation; indexed cleanup resources do not imply root authority
or absence of active aliases. Retirement does not kill the physical root. -/

@[expose] public section

namespace Aeneas.Std

namespace Heap

theorem createRepr.enabled (s : Heap) (blk : Block) (hf : s.allocations s.next = none)
    (valid : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).check = true) :
    s.createRepr blk = some (s.next, ⟨update s.allocations s.next (some blk), s.next + 1⟩) := by
  simp [createRepr, hf, commit, valid]

theorem createRepr.success {s s' : Heap} {blk : Block} {base : Nat}
    (h : s.createRepr blk = some (base, s')) :
    base = s.next ∧
      s' = ⟨update s.allocations s.next (some blk), s.next + 1⟩ := by
  unfold createRepr at h
  split at h
  · obtain ⟨result, hc, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hb, hs⟩ := Prod.mk.inj he
    exact ⟨hb.symm, hs ▸ (commit_success _ _ hc).1⟩
  · contradiction

theorem live_create {s : Heap} {blk fresh : Block} {s' : Heap} {id : Nat}
    (hinv : s.Inv) (hlive : s.live blk = true)
    (hcreate : s.createRepr fresh = some (id, s')) : s'.live blk = true := by
  obtain ⟨_, rfl⟩ := createRepr.success hcreate
  cases hr : s.allocations blk.root
  · simp [live, hr] at hlive
  · have hne : blk.root ≠ s.next := by have := hinv.base_lt hr; grind
    simpa [live, update, hne, hr] using hlive

/-- An exclusive exposure cannot retain pointer lanes justified by a different
readable view: that contribution would conflict with its new writer. -/
theorem newBlock_exposure_carries (repr : Repr ty) (value : ty)
    (bytes : Vector Byte repr.size) (bptr : BasePtr) (root : Option Nat)
    {s s' : Heap} {p : RawPtr ty} (hinv : s.Inv)
    (exposed : State.exposes repr s bptr.val value bytes)
    (created : Heap.newBlock repr [bytes] false bptr root s = some (p, s')) :
    ∀ i : Fin repr.size, ∀ q lane, bytes[i.val] = .pointer q lane → repr.Carries value q := by
  unfold Heap.newBlock at created
  simp only [Bool.not_false, Bool.true_or, Bool.and_true] at created
  split at created
  · obtain ⟨⟨id, result⟩, hcreate, _⟩ := Option.map_eq_some_iff.mp created
    have success := createRepr.success hcreate
    have hi := createRepr_Inv _ _ _ _ hinv hcreate
    have fresh :
        result.allocations s.next =
          some ⟨bptr, root.getD s.next, repr.create [bytes] 0, false, true, true⟩ := by
      simp [success.2, update]
    intro i q lane byte
    have source := exposed.2 i
    rw [byte] at source
    rcases source with carried | ⟨other, blk, index, depth, hl, live, address, cell⟩
    · exact carried
    · have hlt := hinv.base_lt hl
      have different : other ≠ s.next := Nat.ne_of_lt hlt
      have old : result.allocations other = some blk := by
        simpa [success.2, update, different] using hl
      have compatible := (compatible_iff _ _).mp
        (hi.compatible fresh old (Ne.symm different))
      have active : blk.active = true := by
        simp only [Heap.live, Bool.and_eq_true] at live
        exact live.1
      have pairs := compatible.resolve_left (by simp) |>.resolve_left (by simp [active])
      have indexBound := List.getElem?_eq_some_iff.mp cell
      have sizeBound : i.val < (repr.create [bytes] 0).length := by
        simp [Repr.create]
      have conflict := pairs i.val sizeBound index indexBound.1 address.symm
      simp [Repr.create, byte, indexBound.2, Cell.compatible] at conflict
  · contradiction

theorem retire_support (s : Heap) (id : Nat) (hinv : s.Inv) (hid : id < s.next) :
    ∀ j, (s.retire id).next ≤ j → (s.retire id).allocations j = none := by
  intro j hj
  have hne : j ≠ id := by change s.next ≤ j at hj; grind
  simpa [retire, update, hne] using hinv.1 j hj

@[simp] theorem validByte_retire (s : Heap) (id : Nat) (byte : Byte) :
    (s.retire id).validByte byte = s.validByte byte := by
  cases byte
  · rfl
  · rfl
  · rename_i p lane
    by_cases he : p.provenance = id
    · simp [validByte, retire, update, he]
    · simp [validByte, retire, update, he]

@[simp] theorem validBlock_retire (s : Heap) (id : Nat) (blk : Block) :
    (s.retire id).validBlock blk = s.validBlock blk := by
  simp only [validBlock, validByte_retire]
  by_cases he : blk.root = id
  · simp [retire, update, he]
    cases s.allocations id
    · rfl
    · rfl
  · simp [retire, update, he]

theorem validBlock_inactive {s : Heap} {blk : Block} (h : s.validBlock blk = true) :
    s.validBlock { blk with active := false } = true := by
  unfold validBlock at *
  cases hr : s.allocations blk.root
  · simp [hr] at h
  · simp [hr, bounded] at h ⊢
    exact ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩

/-- Retirement only removes a view's permission contribution. Immutable root
metadata, pointer payload validity, and physical liveness are unchanged. -/
theorem retire_Inv {s : Heap} (hinv : s.Inv) (id : Nat) : (s.retire id).Inv := by
  have support : ∀ j, (s.retire id).next ≤ j → (s.retire id).allocations j = none := by
    intro j hj
    have hn := hinv.1 j hj
    by_cases he : j = id
    · subst j
      simp [retire, update, hn]
    · simp [retire, update, he, hn]
  refine ⟨support, List.all_eq_true.mpr ?_⟩
  intro i hi
  have row := List.all_eq_true.mp hinv.2 i hi
  cases hl : s.allocations i
  · simp [hl] at row
  · rename_i a
    simp only [hl, Bool.and_eq_true] at row
    have pair := row.2
    have valid := row.1
    by_cases he : i = id
    · subst i
      have hli : (s.retire id).allocations id = some { a with active := false } := by
        simp [retire, update, hl]
      rw [hli]
      simp only [Bool.and_eq_true]
      constructor
      · rw [validBlock_retire]
        exact validBlock_inactive valid
      · apply List.all_eq_true.mpr
        intro j hj
        by_cases hjid : j = id
        · simp [hjid]
        · have entry := List.all_eq_true.mp pair j hj
          cases hjl : s.allocations j
          · simp [Ne.symm hjid, hjl] at entry
          · have hlj : (s.retire id).allocations j = s.allocations j := by
              simp [retire, update, hjid]
            simp [Ne.symm hjid, hjl] at entry
            simp [Ne.symm hjid, hlj, hjl, compatible, overlaps]
            have hn := entry.1
            simp [overlaps] at hn
            agrind
    · have hli : (s.retire id).allocations i = some a := by
        simp [retire, update, he, hl]
      rw [hli]
      simp only [Bool.and_eq_true]
      constructor
      · simpa using valid
      · apply List.all_eq_true.mpr
        intro j hj
        by_cases hji : i = j
        · simp [hji]
        · have entry := List.all_eq_true.mp pair j hj
          cases hjl : s.allocations j
          · simp [hji, hjl] at entry
          · rename_i b
            by_cases hjid : j = id
            · have hlj : (s.retire id).allocations j = some { b with active := false } := by
                simp [retire, update, hjid, show s.allocations id = some b from hjid ▸ hjl]
              simp [hji, hjl] at entry
              simp [hji, hlj, compatible, overlaps]
              have hn := entry.1
              simp [overlaps] at hn
              agrind
            · have hlj : (s.retire id).allocations j = s.allocations j := by
                simp [retire, update, hjid]
              simpa [hji, hlj, hjl] using entry

end Heap

namespace SepLogic

theorem matches_create_frame {s s' : Heap} {F : Fragment} {blk : Block} {base : Nat}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (h : s.createRepr blk = some (base, s')) : Fragment.Matches s' F := by
  have he := (Heap.createRepr.success h).2
  intro resource hr
  have hh := hm resource hr
  obtain ⟨actual, hl⟩ := hh.live
  have hne : resource.base ≠ s.next := by have := hi.base_lt hl; grind
  cases resource
  · obtain ⟨actual, hl, hlive, ha, hv⟩ := hh
    simp only [Resource.base] at hne
    refine ⟨actual, ?_, Heap.live_create hi hlive h, ha, hv⟩
    simpa [he, update, Resource.base, hne] using hl
  · obtain ⟨actual, hl, hn, hlive, ha, ho⟩ := hh
    simp only [Resource.base] at hne
    refine ⟨actual, ?_, hn, Heap.live_create hi hlive h, ha, ho⟩
    simpa [he, update, Resource.base, hne] using hl

theorem fresh_disjoint {s : Heap} {F h : Fragment}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨actual, hl⟩ := (hm other ho).live
  have hlt := hi.base_lt hl
  left
  rw [hfresh r hr]
  grind

/-- Creation may alias another view physically; its fresh ghost ID gives linear
resource disjointness, while the checked invariant gives physical compatibility. -/
theorem createRepr.spec (s : Heap) (blk : Block)
    (valid : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).check = true)
    (live : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).live blk = true) :
    TripleAt emp (fun s base s' => s.createRepr blk = some (base, s'))
      (fun base h => base = s.next ∧
        h = Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
          cellsHeap blk.bptr base 0 blk.repr) s := by
  rintro h F rfl hd hm hinv
  have old := (Fragment.matches_union _ _ _).mp hm |>.2
  have hrun := Heap.createRepr.enabled s blk (Heap.fresh s hinv) valid
  refine ⟨⟨s.next, _, hrun⟩, ?_⟩
  intro base s' hs'
  obtain ⟨rfl, rfl⟩ := Heap.createRepr.success hs'
  let resource := Fragment.single (.cleanup s.next blk.repr.length blk.bptr blk.owned) ∪
    cellsHeap blk.bptr s.next 0 blk.repr
  have fresh : ∀ r, resource r → r.base = s.next := by
    rintro r (rfl | ⟨i, hi, rfl⟩)
    · rfl
    · rfl
  refine ⟨resource, fresh_disjoint hinv old fresh, ?_,
    Heap.createRepr_Inv s blk _ _ hinv hrun, rfl, rfl⟩
  apply (Fragment.matches_union _ _ _).mpr
  refine ⟨?_, matches_create_frame hinv old hrun⟩
  apply (Fragment.matches_union _ _ _).mpr
  constructor
  · exact (Fragment.matches_single _ _).mpr
      ⟨blk, by simp [update], rfl, live, rfl, rfl⟩
  · rw [matches_cellsHeap]
    intro i hi
    exact ⟨blk, by simp [update], live, rfl, by simp [List.getElem?_eq_getElem hi]⟩

/-- Every compatible placement creates the same fresh indexed resources, even
when nonowning exposure reuses a physical root. -/
theorem newBlock_single.resources (repr : Repr ty) (data : Vector Byte repr.size)
    (own : Bool) (bptr : BasePtr) (root : Option Nat) {s s' : Heap} {p : RawPtr ty}
    (hinv : s.Inv) {F : Fragment} (hm : Fragment.Matches s F)
    (hrun : Heap.newBlock repr [data] own bptr root s = some (p, s')) :
    s'.next = s.next + 1 ∧ ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
      sep (alloc repr p p.address 1 own)
        (block repr p p.address (data.map (Cell.shared 0)).toList) h := by
  have extract {α β : Type} (condition : Bool) (input : Option α) (f : α → β) (y : β)
      (h : (if condition then input.map f else none) = some y) :
      condition = true ∧ ∃ x, input = some x ∧ f x = y := by
    cases hc : condition
    · simp [hc] at h
    · exact ⟨rfl, Option.map_eq_some_iff.mp (by simpa [hc] using h)⟩
  unfold Heap.newBlock at hrun
  obtain ⟨guard, ⟨id, result⟩, hcreate, he⟩ := extract _ _ _ _ hrun
  have ha : repr.align.val ∣ bptr.val := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact guard.1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  let fresh : Block := ⟨bptr, root.getD s.next, repr.create [data] 0, own, true, true⟩
  have hs := Heap.createRepr.success hcreate
  have hinv' := Heap.createRepr_Inv s fresh id result hinv hcreate
  have hl : result.allocations id = some fresh := by simp [hs.1, hs.2, update, fresh]
  have live : result.live fresh = true := by
    have hv := hinv'.validBlock hl
    cases hr : result.allocations fresh.root
    · simp [Heap.validBlock, hr] at hv
    · simp [Heap.validBlock, Heap.live, hr, fresh] at hv ⊢
      exact hv.1.2.2
  have valid : (Heap.mk (update s.allocations s.next (some fresh)) (s.next + 1)).check =
      true := hs.2 ▸ hinv'.2
  have live' : (Heap.mk (update s.allocations s.next (some fresh)) (s.next + 1)).live fresh =
      true := hs.2 ▸ live
  obtain ⟨_, post⟩ := createRepr.spec s fresh valid live' ∅ F rfl
    (Fragment.disjoint_empty_left F) (by simpa using hm) hinv
  obtain ⟨h, hd, hm', hi', _, hh⟩ := post id result hcreate
  refine ⟨by simp [hs.2], h, hd, hm', hi',
    allocHeap repr bptr id 1 own,
    cellsHeap bptr id 0 (data.map (Cell.shared 0)).toList, ?_, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rintro _ rfl _ ⟨i, hi, rfl⟩
    right
    simp [Resource.key]
  · simpa [fresh, allocHeap, Repr.create, Vector.toList_map] using hh
  · exact ⟨Nat.le_refl _, ha, by simp [RawPtr.offsetFrom]⟩

theorem matches_retire_frame {s : Heap} {F : Fragment} {base : Nat}
    (hm : Fragment.Matches s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches (s.retire base) F := by
  intro resource hr
  have hh := hm resource hr
  have hne' := hne resource hr
  have hlive : ∀ blk, s.live blk = true → (s.retire base).live blk = true := by
    intro blk hv
    by_cases he : blk.root = base
    · simpa [Heap.live, Heap.retire, update, he, Option.map_map, Function.comp_def] using hv
    · simpa [Heap.live, Heap.retire, update, he] using hv
  cases resource
  · obtain ⟨blk, hl, hv, ha, hc⟩ := hh
    simp only [Resource.base] at hne'
    exact ⟨blk, by simpa [Heap.retire, update, Resource.base, hne'] using hl,
      hlive blk hv, ha, hc⟩
  · obtain ⟨blk, hl, hn, hv, ha, ho⟩ := hh
    simp only [Resource.base] at hne'
    exact ⟨blk, by simpa [Heap.retire, update, Resource.base, hne'] using hl,
      hn, hlive blk hv, ha, ho⟩

/-- Whole indexed ownership excludes same-view resources from the frame.
It says nothing about different-view aliases of that root. -/
theorem frame_base_absent {s : Heap} {base : Nat} {blk : Block} {F : Fragment}
    (hl : s.allocations base = some blk)
    (hd : (Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
      cellsHeap blk.bptr base 0 blk.repr).Disjoint F)
    (hm : Fragment.Matches s F) : ∀ r, F r → r.base ≠ base := by
  intro resource hr hb
  obtain ⟨ha, hc⟩ := Fragment.disjoint_union_left.mp hd
  cases resource
  · rename_i other index bptr value
    obtain ⟨actual, hs, _, _, hv⟩ := hm _ hr
    change other = base at hb
    subst other
    have he : actual = blk := Option.some.inj (hs.symm.trans hl)
    subst actual
    have hi := List.getElem?_eq_some_iff.mp hv |>.1
    have hh := hc (.cell base index blk.bptr blk.repr[index])
      ⟨index, hi, by simp⟩ (.cell base index bptr value) hr
    simp [Resource.Compatible, Resource.base, Resource.key] at hh
  · rename_i other size bptr own
    change other = base at hb
    subst other
    have hh := ha _ rfl _ hr
    simp [Resource.Compatible, Resource.base, Resource.key] at hh

/-- Reusable retirement contract. Concrete runtime guards still belong to the
operation-specific theorem; no claim of physical death or safe return authority. -/
theorem retire.spec (s : Heap) (base : Nat) (blk : Block)
    (hl : s.allocations base = some blk) :
    TripleAt
      (fun h => h = Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
        cellsHeap blk.bptr base 0 blk.repr)
      (fun s (_ : Unit) s' => Heap.commit (s.retire base) = some s')
      (fun _ => emp) s := by
  rintro h F rfl hd hm hinv
  have old := (Fragment.matches_union _ _ _).mp hm |>.2
  have preserved := Heap.retire_Inv hinv base
  have hr : Heap.commit (s.retire base) = some (s.retire base) := by
    simp [Heap.commit, preserved.2]
  refine ⟨⟨(), _, hr⟩, ?_⟩
  intro _ s' he
  have he := Option.some.inj (hr.symm.trans he)
  subst s'
  exact ⟨∅, Fragment.disjoint_empty_left _,
    by simpa using matches_retire_frame old (frame_base_absent hl hd old),
    preserved, rfl⟩

/-- Layout cleanup is not root-return authority. These state-specific conditions
are still required until safe backward resources track all outstanding views. -/
def RootReturn (s : Heap) (base : Nat) : Prop :=
  ∀ blk, s.allocations base = some blk →
    ∃ root, s.allocations blk.root = some root ∧ blk.bptr = root.bptr ∧
      blk.repr.length = root.repr.length ∧ s.noAliases base blk.root = true

@[simp] theorem noAliases_storeRepr (s : Heap) (id base root : Nat) (bytes : List Cell) :
    (s.storeRepr id bytes).noAliases base root = s.noAliases base root := by
  unfold Heap.noAliases
  apply congrArg (List.all _)
  funext j
  by_cases he : j = id
  · subst j
    simp [Heap.storeRepr, update, Option.map_map, Function.comp_def]
  · simp [Heap.storeRepr, update, he]

/-- Byte updates retain root-return authority; clients need not inspect aliases. -/
theorem RootReturn.storeRepr {s : Heap} {base id : Nat} {blk : Block}
    (authority : RootReturn s base) (hl : s.allocations id = some blk)
    (bytes : List Cell) (length : bytes.length = blk.repr.length) :
    RootReturn (s.storeRepr id bytes) base := by
  intro actual ha
  by_cases hb : base = id
  · subst base
    have he : actual = { blk with repr := bytes } := by
      simpa [Heap.storeRepr, update, hl] using ha.symm
    subst actual
    obtain ⟨root, hr, hptr, hlen, hn⟩ := authority blk hl
    by_cases hroot : blk.root = id
    · have he : root = blk := Option.some.inj ((hroot ▸ hr).symm.trans hl)
      subst root
      exact ⟨{ blk with repr := bytes }, by simp [Heap.storeRepr, update, hroot, hl],
        rfl, rfl, by simpa using hn⟩
    · exact ⟨root, by simpa [Heap.storeRepr, update, hroot] using hr,
        hptr, length.trans hlen, by simpa using hn⟩
  · have old : s.allocations base = some actual := by
      simpa [Heap.storeRepr, update, hb] using ha
    obtain ⟨root, hr, hptr, hlen, hn⟩ := authority actual old
    by_cases hroot : actual.root = id
    · have he : root = blk := Option.some.inj ((hroot ▸ hr).symm.trans hl)
      subst root
      exact ⟨{ blk with repr := bytes }, by simp [Heap.storeRepr, update, hroot, hl],
        hptr, hlen.trans length.symm, by simpa using hn⟩
    · exact ⟨root, by simpa [Heap.storeRepr, update, hroot] using hr,
        hptr, hlen, by simpa using hn⟩

theorem RootReturn.modify {s s' : Heap} {base : Nat} {repr : Repr ty}
    {p : RawPtr ty}
    {change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)}
    (authority : RootReturn s base) (run : Heap.modify repr p change s = some s') :
    RootReturn s' base := by
  unfold Heap.modify at run
  cases hl : s.allocations p.provenance
  · simp [hl] at run
  · rename_i blk
    simp only [hl, Bind.bind, Option.bind] at run
    split at run
    · cases hc : change blk.bytes (p.offsetFrom blk.bptr)
      · simp [hc] at run
      · rename_i bytes
        simp only [hc] at run
        have he := (Heap.commit_success _ _ run).1
        subst s'
        exact authority.storeRepr hl bytes.toList (by simp)
    · contradiction

theorem RootReturn.retire {s : Heap} {base : Nat} (authority : RootReturn s base)
    (id : Nat) : RootReturn (s.retire id) base := by
  have aliases {root : Nat} (hn : s.noAliases base root = true) :
      (s.retire id).noAliases base root = true := by
    apply List.all_eq_true.mpr
    intro j hj
    have old := List.all_eq_true.mp hn j hj
    by_cases he : j = id
    · subst j
      simp [Heap.retire, update, Option.map_map, Function.comp_def]
      cases s.allocations id <;> simp
    · simpa [Heap.retire, update, he] using old
  intro actual ha
  by_cases hb : base = id
  · subst base
    cases hl : s.allocations id
    · simp [Heap.retire, update, hl] at ha
    · rename_i blk
      have he : actual = { blk with active := false } := by
        simpa [Heap.retire, update, hl] using ha.symm
      subst actual
      obtain ⟨root, hr, hptr, hlen, hn⟩ := authority blk hl
      by_cases hroot : blk.root = id
      · have hr' : s.allocations id = some root := hroot ▸ hr
        exact ⟨{ root with active := false },
          by simp [Heap.retire, update, hroot, hr'],
          hptr, hlen, aliases hn⟩
      · exact ⟨root, by simpa [Heap.retire, update, hroot] using hr,
          hptr, hlen, aliases hn⟩
  · have old : s.allocations base = some actual := by
      simpa [Heap.retire, update, hb] using ha
    obtain ⟨root, hr, hptr, hlen, hn⟩ := authority actual old
    by_cases hroot : actual.root = id
    · have hr' : s.allocations id = some root := hroot ▸ hr
      exact ⟨{ root with active := false },
        by simp [Heap.retire, update, hroot, hr'],
        hptr, hlen, aliases hn⟩
    · exact ⟨root, by simpa [Heap.retire, update, hroot] using hr,
        hptr, hlen, aliases hn⟩

/-- Every owned placement supplies the authority required to return that view,
including reacquisition of an inactive owned root. -/
theorem owned_newBlock_root {s s' : Heap} {repr : Repr ty}
    {data : List (Vector Byte repr.size)} {bptr : BasePtr} {root : Option Nat}
    {p : RawPtr ty} (hi : s.Inv)
    (run : Heap.newBlock repr data true bptr root s = some (p, s')) :
    RootReturn s' p.provenance := by
  have extract {α : Type} (flag : Bool) (x : Option α) (y : α)
      (h : (if flag then x else none) = some y) : flag = true ∧ x = some y := by
    cases flag
    · contradiction
    · exact ⟨rfl, h⟩
  unfold Heap.newBlock at run
  obtain ⟨guard, selected⟩ := extract _ _ _ run
  clear run
  obtain ⟨⟨id, result⟩, created, he⟩ := Option.map_eq_some_iff.mp selected
  clear selected
  obtain ⟨hp, hs⟩ := Prod.mk.inj he
  subst p
  subst s'
  obtain ⟨hid, hstate⟩ := Heap.createRepr.success created
  subst id
  subst result
  let fresh : Block := ⟨bptr, root.getD s.next, repr.create data 0, true, true, true⟩
  have lookup : (Heap.mk (update s.allocations s.next (some fresh)) (s.next + 1)).allocations
      s.next = some fresh := by simp [update]
  intro blk hl
  have he : blk = fresh := Option.some.inj (hl.symm.trans lookup)
  subst blk
  cases root
  · refine ⟨fresh, lookup, rfl, rfl, ?_⟩
    apply List.all_eq_true.mpr
    intro j hj
    have hj' : j < s.next + 1 := List.mem_range.mp hj
    by_cases he : j = s.next
    · simp [he]
    · have hjlt : j < s.next := by agrind
      cases ho : s.allocations j
      · simp [update, he, ho]
      · rename_i old
        have hv := hi.validBlock ho
        have hrootlt : old.root < s.next := by
          cases hr : s.allocations old.root
          · simp [Heap.validBlock, hr] at hv
          · exact hi.base_lt hr
        simp [update, he, ho, fresh, show old.root ≠ s.next by agrind]
  · rename_i ancestor
    have available : s.ownershipAvailable ancestor bptr (data.length * repr.size) = true := by
      simp only [Bool.and_eq_true] at guard
      simpa using guard.2
    cases hr : s.allocations ancestor
    · simp [Heap.ownershipAvailable, hr] at available
    · rename_i parent
      have ancestorLt := hi.base_lt hr
      have fields := available
      simp [Heap.ownershipAvailable, hr, and_assoc] at fields
      obtain ⟨_, _, inactive, _, pointer, size, noaliases⟩ := fields
      have hptr : bptr = parent.bptr := by
        change (parent.bptr.bv == bptr.bv) = true at pointer
        have he : parent.bptr.bv = bptr.bv := by simpa using pointer
        exact congrArg (@UScalar.mk .Usize) he.symm
      refine ⟨parent, by simp [update, show ancestor ≠ s.next by agrind, fresh, hr],
        hptr, ?_, ?_⟩
      · have total : ∀ xs : List (Vector Byte repr.size),
            (xs.map fun _ => repr.size).sum = xs.length * repr.size := by
          intro xs
          induction xs
          · simp
          · rename_i item tail ih
            simp [ih, Nat.add_mul, Nat.add_comm]
        simpa [fresh, Repr.create, total data] using size.symm
      · apply List.all_eq_true.mpr
        intro j hj
        have hj' : j < s.next + 1 := List.mem_range.mp hj
        by_cases he : j = s.next
        · simp [he]
        · have hjlt : j < s.next := by agrind
          have old := List.all_eq_true.mp noaliases j (List.mem_range.mpr hjlt)
          by_cases hja : j = ancestor
          · subst j
            simp [update, he, hr, inactive, fresh]
          · simpa [update, he, fresh, hja] using old

theorem RootReturn.newOwned {s s' : Heap} {base : Nat} {actual : Block}
    {repr : Repr ty} {data : List (Vector Byte repr.size)}
    {bptr : BasePtr} {root : Option Nat} {p : RawPtr ty}
    (hi : s.Inv) (authority : RootReturn s base)
    (old : s.allocations base = some actual) (active : actual.active = true)
    (run : Heap.newBlock repr data true bptr root s = some (p, s')) :
    RootReturn s' base := by
  have extract {α : Type} (flag : Bool) (x : Option α) (y : α)
      (h : (if flag then x else none) = some y) : flag = true ∧ x = some y := by
    cases flag
    · contradiction
    · exact ⟨rfl, h⟩
  unfold Heap.newBlock at run
  obtain ⟨guard, selected⟩ := extract _ _ _ run
  clear run
  obtain ⟨⟨id, result⟩, created, he⟩ := Option.map_eq_some_iff.mp selected
  clear selected
  obtain ⟨_, hs⟩ := Prod.mk.inj he
  subst s'
  obtain ⟨hid, hstate⟩ := Heap.createRepr.success created
  subst result
  obtain ⟨parent, hr, hptr, hlen, aliases⟩ := authority actual old
  have baseLt := hi.base_lt old
  have rootLt := hi.base_lt hr
  have different : root.getD s.next ≠ actual.root := by
    cases root
    · simp
      agrind
    · rename_i ancestor
      have available : s.ownershipAvailable ancestor bptr (data.length * repr.size) = true := by
        simp only [Bool.and_eq_true] at guard
        simpa using guard.2
      cases hp : s.allocations ancestor
      · simp [Heap.ownershipAvailable, hp] at available
      · rename_i block
        simp [Heap.ownershipAvailable, hp, and_assoc] at available
        obtain ⟨_, _, inactive, _, _, _, noaliases⟩ := available
        by_cases same : base = ancestor
        · have eq : actual = block := Option.some.inj ((same ▸ old).symm.trans hp)
          have live : block.active = true := eq ▸ active
          cases live.symm.trans inactive
        · have allowed := List.all_eq_true.mp noaliases base (List.mem_range.mpr baseLt)
          have unequal : actual.root ≠ ancestor := by
            simpa only [old, Option.map_some, Option.getD_some, active,
              Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
              bne_iff_ne, same, false_or] using allowed
          exact Ne.symm unequal
  intro block lookup
  have eq : block = actual := by
    have same : s.allocations base = some block := by
      simpa [update, show base ≠ s.next by agrind] using lookup
    exact Option.some.inj (same.symm.trans old)
  subst block
  refine ⟨parent, by simpa [update, show actual.root ≠ s.next by agrind] using hr,
    hptr, hlen, ?_⟩
  apply List.all_eq_true.mpr
  intro j hj
  have bound : j < s.next + 1 := List.mem_range.mp hj
  by_cases same : j = s.next
  · simp [same, update, different]
  · have bound' : j < s.next := by agrind
    have allowed := List.all_eq_true.mp aliases j (List.mem_range.mpr bound')
    simpa [update, same] using allowed

theorem whole_readable {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {value : ty} {own : Bool} {depth : Nat} {s : Heap} {h : Fragment}
    (hsize : 0 < repr.size)
    (hp : sep (alloc repr p bptr 1 own) (readable repr p bptr value depth) h)
    (hm : Fragment.Matches s h) :
    ∃ blk, s.allocations p.provenance = some blk ∧ s.live blk = true ∧
      p.address = blk.bptr ∧ repr.align.val ∣ blk.bptr.val ∧ blk.owned = own ∧
      blk.repr.length = repr.size ∧
      blk.repr.all (fun cell => cell.depth == some depth) = true ∧
      h = Fragment.single (.cleanup p.provenance blk.repr.length blk.bptr blk.owned) ∪
        cellsHeap blk.bptr p.provenance 0 blk.repr := by
  obtain ⟨a, b, _, rfl, ⟨haddr, rfl⟩, data, _, hlo, ha, rfl⟩ := hp
  obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨blk, hl, hlen, hlive, hbptr, hown⟩ := hma _ rfl
  obtain ⟨actual, hb, hl', _, hbptr', selected⟩ := bytes_of_matches hsize hmb
  have he : actual = blk := Option.some.inj (hl'.symm.trans hl)
  subst actual
  have hrepr : blk.repr = (data.map (Cell.shared depth)).toList := by
    have hs := congrArg Vector.toList selected
    have ht : blk.repr.take repr.size = blk.repr := by
      rw [← show blk.repr.length = repr.size by simpa using hlen, List.take_length]
    simpa [Repr.select_toList, Block.bytes, haddr, hbptr, RawPtr.offsetFrom, ht] using hs
  refine ⟨blk, hl, hlive, haddr.trans hbptr.symm, hbptr ▸ (haddr ▸ ha), hown,
    by simpa using hlen, ?_, ?_⟩
  · simp [hrepr, Cell.depth]
  · simp [allocHeap, hbptr, hown, hrepr, haddr, RawPtr.offsetFrom]

/-- Baseline exposures retire uniformly. Returning an owned view additionally
requires exact root coverage and absence of other active views, not just bytes. -/
theorem returnView.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (value : ty) (own : Bool) (s : Heap) (hsize : 0 < repr.size)
    (authority : own = true → RootReturn s p.provenance) :
    TripleAt (sep (alloc repr p bptr 1 own) (readable repr p bptr value))
      (fun s (_ : Unit) s' =>
        (if own then Heap.returnOwned repr p 1 s else Heap.endExposureAt repr p 1 0 s) = some s')
      (fun _ => emp) s := by
  intro h F hp hd hm hinv
  obtain ⟨blk, hl, hlive, haddr, ha, hown, hlen, hdepth, hh⟩ :=
    whole_readable hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  have preserved := Heap.retire_Inv hinv p.provenance
  have depths : ∀ cell ∈ blk.repr, cell.depth = some 0 := by
    simpa [-Cell.depth] using hdepth
  have commit : Heap.commit (s.retire p.provenance) = some (s.retire p.provenance) := by
    simp [Heap.commit, preserved.2]
  have run : (if own then Heap.returnOwned repr p 1 s
      else Heap.endExposureAt repr p 1 0 s) = some (s.retire p.provenance) := by
    cases ho : own
    · simp [-Cell.depth, Heap.endExposureAt, hl, hlive, hown, ho, haddr, ha, hlen, commit]
      exact depths
    · obtain ⟨root, hr, hbase, hrlen, hno⟩ := authority ho blk hl
      simp [-Cell.depth, Heap.returnOwned, hl, hr, hlive, hown, ho, haddr,
        ← hrlen, ha, hlen, hno, commit]
      constructor
      · change (blk.bptr.bv == root.bptr.bv) = true
        simp [hbase]
      · exact depths
  obtain ⟨_, post⟩ := retire.spec s p.provenance blk hl h F hh hd hm hinv
  refine ⟨⟨(), s.retire p.provenance, run⟩, ?_⟩
  intro _ s' he
  have hs : s' = s.retire p.provenance := Option.some.inj (he.symm.trans run)
  subst s'
  exact post () _ commit

end SepLogic
end Aeneas.Std
