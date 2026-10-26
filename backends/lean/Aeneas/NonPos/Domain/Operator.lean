module
public import Aeneas.NonPos.Domain.Limit

@[expose] public section

/-!
# Domain theory: domain operators and the solution of recursive domain equations

A `DomainOperator I` is an operator `F` on `I`-indexed families of domains which:
- lifts embedding-projection pairs (`mapEP`), and
- commutes with inverse limits (`commute`).

A `Signature I` is an `I`-indexed family of such operators; it describes the system of domain
equations `D j ≅ (F j) D` for `j : I`. `solve F j` is the inverse limit of the tower

```
D₀ j = PUnit,   Dₙ₊₁ j = (F j) Dₙ
```

and `familySolution F j : solve F j ≅ (F j) (solve F)` is the (genuine) isomorphism solving the
equation. `roll`/`unroll` are its two directions.

The operators we provide are:
- `DomainOperator.constant A`: a fixed domain (no recursive occurrence);
- `DomainOperator.variable j`: the recursive occurrence `D j`;
- `DomainOperator.pi F`: dependent products (used for the "data" arguments of methods and for the
  type parameters of methods);
- `DomainOperator.arrow F G`: the space of continuous maps (used for the "dictionary" arguments
  of methods: this handles the negative occurrences);
- `DomainOperator.product F G`: binary products (used to combine the fields of a trait).
-/

namespace NonPos.Domain

open Lean.Order OmegaComplete OmegaSup

universe i u v w x

/-! ## Products of towers -/

section PiTower

variable {ι : Type w}

abbrev piTower (T : ι → Tower.{u}) : Tower.{max w u} where
  obj n := piDomain (fun j => (T j).obj n)
  bond n := piEP (fun j => (T j).bond n)

def splitThread (T : ι → Tower.{u}) (x : limit (piTower T)) : (j : ι) → limit (T j) :=
  fun j => {
    coord := fun n => x n j
    coherent := fun n => congrArg (fun f => f j) (x.coherent n)
  }

def joinThreads (T : ι → Tower.{u}) (x : (j : ι) → limit (T j)) : limit (piTower T) where
  coord n j := x j n
  coherent n := funext (fun j => (x j).coherent n)

theorem join_split (T : ι → Tower.{u}) (x : limit (piTower T)) :
    joinThreads T (splitThread T x) = x :=
  Thread.ext (fun _ => rfl)

theorem split_join (T : ι → Tower.{u}) (x : (j : ι) → limit (T j)) :
    splitThread T (joinThreads T x) = x := by
  funext j
  exact Thread.ext (fun _ => rfl)

def piLimitIso (T : ι → Tower.{u}) :
    DomainIso (limit (piTower T)) (piDomain (fun j => limit (T j))) where
  forward := continuousOfInverse (splitThread T) (joinThreads T)
    (fun _ _ related j n => related n j)
    (fun _ _ related n j => related j n)
    (join_split T) (split_join T)
  backward := continuousOfInverse (joinThreads T) (splitThread T)
    (fun _ _ related n j => related j n)
    (fun _ _ related j n => related n j)
    (split_join T) (join_split T)
  backward_forward := join_split T
  forward_backward := split_join T

end PiTower

/-! ## Constant towers -/

abbrev constantTower (A : Domain.{u}) : Tower.{u} where
  obj _ := A
  bond _ := EP.id A

def constantThread (A : Domain.{u}) (x : A) : limit (constantTower A) where
  coord _ := x
  coherent _ := rfl

theorem constant_coord (A : Domain.{u}) (x : limit (constantTower A)) (n : Nat) : x n = x 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (x.coherent n).trans ih

def constantLimitIso (A : Domain.{u}) : DomainIso (limit (constantTower A)) A where
  forward := coordinate (constantTower A) 0
  backward := {
    toFun := constantThread A
    cont := ⟨fun _ _ related _ => related, fun _ => Thread.ext (fun _ => rfl)⟩
  }
  backward_forward x := Thread.ext (fun n => (constant_coord A x n).symm)
  forward_backward _ := rfl

/-! ## Function spaces of towers -/

section ArrowTower

variable (T : Tower.{u}) (S : Tower.{v})

abbrev arrowTower : Tower.{max u v} where
  obj n := functionSpace (T.obj n) (S.obj n)
  bond n := arrowEP (T.bond n) (S.bond n)

def arrowApprox (x : limit (arrowTower T S)) (n : Nat) : ContinuousMap (limit T) (limit S) :=
  (approx S n).embed.comp ((x n).comp (coordinate T n))

def arrowChain (x : limit (arrowTower T S)) : Chain (ContinuousMap (limit T) (limit S)) where
  val n := arrowApprox T S x n
  step n y := by
    change (approx S n).embed (x n (y n)) ⊑ (approx S (n + 1)).embed (x (n + 1) (y (n + 1)))
    rw [← x.coherent n, approx_step]
    apply (approx S (n + 1)).embed.mono
    apply PartialOrder.rel_trans ((S.bond n).embed_project _)
    apply (x (n + 1)).mono
    rw [← y.coherent n]
    exact (T.bond n).embed_project (y (n + 1))

def arrowDecode (x : limit (arrowTower T S)) : ContinuousMap (limit T) (limit S) :=
  OmegaSup.sup (arrowChain T S x)

def arrowEncode (f : ContinuousMap (limit T) (limit S)) : limit (arrowTower T S) where
  coord n := (coordinate S n).comp (f.comp (approx T n).embed)
  coherent n := by
    apply ContinuousMap.ext
    intro a
    change (S.bond n).project
      ((f ((approx T (n + 1)).embed ((T.bond n).embed a))) (n + 1)) =
        (f ((approx T n).embed a)) n
    rw [← approx_step]
    exact (f ((approx T n).embed a)).coherent n

theorem arrowDecode_encode (f : ContinuousMap (limit T) (limit S)) :
    arrowDecode T S (arrowEncode T S f) = f := by
  apply ContinuousMap.ext
  intro x
  let inputs := approximationChain T x
  let grid : Chain (Chain (limit S)) := {
    val := fun m => approximationChain S (f (inputs m))
    step := fun m n => (approx S n).embed.mono _ _
      ((approx S n).project.mono _ _ (f.mono _ _ (inputs.step m)))
  }
  change OmegaSup.sup (ContinuousMap.evalChain (arrowChain T S (arrowEncode T S f)) x) = f x
  calc
    OmegaSup.sup (ContinuousMap.evalChain (arrowChain T S (arrowEncode T S f)) x) =
        OmegaSup.sup grid.diagonal := by
      apply sup_congr
      intro n
      simp only [ContinuousMap.evalChain, arrowChain, arrowApprox, arrowEncode,
        ContinuousMap.comp_apply, coordinate, Chain.diagonal, grid, inputs,
        approximationChain, approx_project]
    _ = OmegaSup.sup grid.sups := (sup_diagonal grid).symm
    _ = OmegaSup.sup (inputs.map f f.mono) := by
      apply sup_congr
      intro n
      exact approximation_sup S (f (inputs n))
    _ = f (OmegaSup.sup inputs) := (f.continuous inputs).symm
    _ = f x := congrArg f (approximation_sup T x)

theorem arrowApprox_stable (x : limit (arrowTower T S)) (k n : Nat) (a : T.obj n) :
    (arrowApprox T S x (n + k) ((approx T n).embed a)) n = x n a := by
  induction k generalizing n with
  | zero =>
    change ((approx S n).embed (x n (((approx T n).embed a) n))) n = x n a
    rw [approx_coordinate, approx_coordinate]
  | succ k ih =>
    rw [show n + (k + 1) = (n + 1) + k by omega, approx_step]
    rw [← (arrowApprox T S x ((n + 1) + k)
      ((approx T (n + 1)).embed ((T.bond n).embed a))).coherent n]
    rw [ih]
    exact congrArg (fun f : ContinuousMap (T.obj n) (S.obj n) => f a) (x.coherent n)

theorem arrowEncode_decode (x : limit (arrowTower T S)) :
    arrowEncode T S (arrowDecode T S x) = x := by
  apply Thread.ext
  intro n
  apply ContinuousMap.ext
  intro a
  change (coordinate S n)
    (OmegaSup.sup (ContinuousMap.evalChain (arrowChain T S x) ((approx T n).embed a))) = x n a
  rw [(coordinate S n).continuous]
  have at_n : (arrowApprox T S x n ((approx T n).embed a)) n = x n a :=
    arrowApprox_stable T S x 0 n a
  apply PartialOrder.rel_antisymm
  · apply OmegaSup.sup_le
    intro m
    rcases Nat.le_total m n with before | after
    · have below := (arrowChain T S x).le before ((approx T n).embed a) n
      change (arrowApprox T S x m ((approx T n).embed a)) n ⊑
        (arrowApprox T S x n ((approx T n).embed a)) n at below
      rw [at_n] at below
      exact below
    · have same : m = n + (m - n) := by omega
      rw [same]
      exact PartialOrder.rel_of_eq (arrowApprox_stable T S x (m - n) n a)
  · have below := OmegaSup.le_sup
      ((ContinuousMap.evalChain (arrowChain T S x) ((approx T n).embed a)).map
        (coordinate S n) (coordinate S n).mono) n
    change (arrowApprox T S x n ((approx T n).embed a)) n ⊑ _ at below
    rw [at_n] at below
    exact below

theorem arrowEncode_mono : monotone (arrowEncode T S) := by
  intro f g related n a
  exact related ((approx T n).embed a) n

theorem arrowDecode_mono : monotone (arrowDecode T S) := by
  intro x y related a
  apply sup_mono
  intro n
  exact (approx S n).embed.mono _ _ (related n (a n))

/-- Function spaces commute with inverse limits, including both variance directions. -/
def arrowLimitIso : DomainIso (limit (arrowTower T S)) (functionSpace (limit T) (limit S)) where
  forward := continuousOfInverse (arrowDecode T S) (arrowEncode T S)
    (arrowDecode_mono T S) (arrowEncode_mono T S) (arrowEncode_decode T S) (arrowDecode_encode T S)
  backward := continuousOfInverse (arrowEncode T S) (arrowDecode T S)
    (arrowEncode_mono T S) (arrowDecode_mono T S) (arrowDecode_encode T S) (arrowEncode_decode T S)
  backward_forward := arrowEncode_decode T S
  forward_backward := arrowDecode_encode T S

end ArrowTower

/-! ## Binary products of towers -/

section ProductTower

variable (T : Tower.{u}) (S : Tower.{v})

abbrev productTower : Tower.{max u v} where
  obj n := prodDomain (T.obj n) (S.obj n)
  bond n := prodEP (T.bond n) (S.bond n)

def productSplit (x : limit (productTower T S)) : limit T × limit S :=
  (⟨fun n => (x n).1, fun n => congrArg Prod.fst (x.coherent n)⟩,
    ⟨fun n => (x n).2, fun n => congrArg Prod.snd (x.coherent n)⟩)

def productJoin (x : limit T × limit S) : limit (productTower T S) where
  coord n := (x.1 n, x.2 n)
  coherent n := Prod.ext (x.1.coherent n) (x.2.coherent n)

theorem productJoin_split (x : limit (productTower T S)) :
    productJoin T S (productSplit T S x) = x :=
  Thread.ext (fun _ => rfl)

theorem productSplit_join (x : limit T × limit S) :
    productSplit T S (productJoin T S x) = x :=
  Prod.ext (Thread.ext (fun _ => rfl)) (Thread.ext (fun _ => rfl))

theorem productSplit_mono : monotone (productSplit T S) := by
  intro x y related
  exact ⟨fun n => (related n).1, fun n => (related n).2⟩

theorem productJoin_mono : monotone (productJoin T S) := by
  intro x y related n
  exact ⟨related.1 n, related.2 n⟩

def productLimitIso : DomainIso (limit (productTower T S)) (prodDomain (limit T) (limit S)) where
  forward := continuousOfInverse (productSplit T S) (productJoin T S)
    (productSplit_mono T S) (productJoin_mono T S) (productJoin_split T S) (productSplit_join T S)
  backward := continuousOfInverse (productJoin T S) (productSplit T S)
    (productJoin_mono T S) (productSplit_mono T S) (productSplit_join T S) (productJoin_split T S)
  backward_forward := productJoin_split T S
  forward_backward := productSplit_join T S

end ProductTower

/-! ## Domain operators -/

/-- A family of towers indexed by `I`. -/
structure FamilyTower (I : Type i) : Type (max i (u + 1)) where
  obj : Nat → I → Domain.{u}
  bond : ∀ n j, EP (obj n j) (obj (n + 1) j)

abbrev FamilyTower.component {I : Type i} (T : FamilyTower.{i, u} I) (j : I) : Tower.{u} where
  obj n := T.obj n j
  bond n := T.bond n j

abbrev FamilyTower.limit {I : Type i} (T : FamilyTower.{i, u} I) (j : I) : Domain.{u} :=
  NonPos.Domain.limit (T.component j)

/-- An operator on `I`-indexed families of domains, which lifts embedding-projection pairs and
commutes with inverse limits. -/
structure DomainOperator (I : Type i) : Type (max i (u + 1) (v + 1)) where
  obj : (I → Domain.{u}) → Domain.{v}
  mapEP {A B : I → Domain.{u}} : (∀ j, EP (A j) (B j)) → EP (obj A) (obj B)
  commute (T : FamilyTower.{i, u} I) :
    DomainIso
      (limit { obj := fun n => obj (T.obj n), bond := fun n => mapEP (T.bond n) })
      (obj T.limit)

namespace DomainOperator

variable {I : Type i}

abbrev mapTower (F : DomainOperator.{i, u, v} I) (T : FamilyTower.{i, u} I) : Tower.{v} where
  obj n := F.obj (T.obj n)
  bond n := F.mapEP (T.bond n)

/-- A constant operator: no recursive occurrence. -/
abbrev constant (A : Domain.{v}) : DomainOperator.{i, u, v} I where
  obj _ := A
  mapEP _ := EP.id A
  commute _ := constantLimitIso A

/-- The space of continuous maps between two operators. -/
abbrev arrow (F : DomainOperator.{i, u, v} I) (G : DomainOperator.{i, u, w} I) :
    DomainOperator.{i, u, max v w} I where
  obj A := functionSpace (F.obj A) (G.obj A)
  mapEP p := arrowEP (F.mapEP p) (G.mapEP p)
  commute T := DomainIso.trans (arrowLimitIso (F.mapTower T) (G.mapTower T))
    (arrowIso (F.commute T) (G.commute T))

/-- A dependent product of operators. -/
abbrev pi {ι : Type w} (F : ι → DomainOperator.{i, u, v} I) :
    DomainOperator.{i, u, max w v} I where
  obj A := piDomain (fun j => (F j).obj A)
  mapEP p := piEP (fun j => (F j).mapEP p)
  commute T := DomainIso.trans (piLimitIso (fun j => (F j).mapTower T))
    (piIso (fun j => (F j).commute T))

/-- The binary product of two operators. -/
abbrev product (F : DomainOperator.{i, u, v} I) (G : DomainOperator.{i, u, w} I) :
    DomainOperator.{i, u, max v w} I where
  obj A := prodDomain (F.obj A) (G.obj A)
  mapEP p := prodEP (F.mapEP p) (G.mapEP p)
  commute T := DomainIso.trans (productLimitIso (F.mapTower T) (G.mapTower T))
    (prodIso (F.commute T) (G.commute T))

/-- The unit operator (used to terminate lists of fields). Its universe is the one of the family so
that it does not introduce unconstrained universe levels. -/
abbrev unit : DomainOperator.{i, u, u} I := constant unitDomain.{u}

end DomainOperator

/-- The recursive occurrence `D j`. (Defined outside of the namespace because `variable` is a
keyword.) -/
abbrev DomainOperator.variable {I : Type i} (j : I) : DomainOperator.{i, u, u} I where
  obj A := A j
  mapEP p := p j
  commute T := DomainIso.refl (limit (T.component j))

/-! ## Signatures and their solutions -/

/-- A system of domain equations: for each `j : I`, the operator giving the right-hand side of
the equation `D j ≅ (F j) D`. -/
abbrev Signature (I : Type i) := I → DomainOperator.{i, u, u} I

section Signature

variable {I : Type i}

def unitEP (A : Domain.{u}) : EP unitDomain.{u} A where
  embed := ContinuousMap.const _ _ OmegaComplete.bottom
  project := ContinuousMap.const _ _ PUnit.unit
  project_embed _ := Subsingleton.elim _ _
  embed_project x := OmegaComplete.bottom_le x

/-- The finite stages: `D₀ j = PUnit`, `Dₙ₊₁ j = (F j) Dₙ`. -/
abbrev stages (F : Signature.{i, u} I) : Nat → I → Domain.{u}
  | 0 => fun _ => unitDomain
  | n + 1 => fun j => (F j).obj (stages F n)

abbrev bonds (F : Signature.{i, u} I) :
    (n : Nat) → ∀ j, EP (stages F n j) (stages F (n + 1) j)
  | 0, j => unitEP ((F j).obj (stages F 0))
  | n + 1, j => (F j).mapEP (bonds F n)

abbrev signatureTower (F : Signature.{i, u} I) : FamilyTower.{i, u} I :=
  ⟨stages F, bonds F⟩

/-- The solution of the system of equations. -/
abbrev solve (F : Signature.{i, u} I) (j : I) : Domain.{u} :=
  (signatureTower F).limit j

/-- The isomorphism `solve F j ≅ (F j) (solve F)`. -/
def familySolution (F : Signature.{i, u} I) (j : I) :
    DomainIso (solve F j) ((F j).obj (solve F)) where
  forward := ((F j).commute (signatureTower F)).forward.comp
    (dropMap ((signatureTower F).component j))
  backward := (consMap ((signatureTower F).component j)).comp
    ((F j).commute (signatureTower F)).backward
  backward_forward x := by
    exact (congrArg (consMap ((signatureTower F).component j))
      (((F j).commute (signatureTower F)).backward_forward x.drop)).trans x.cons_drop
  forward_backward y := by
    exact (congrArg ((F j).commute (signatureTower F)).forward
      (Thread.drop_cons (T := (signatureTower F).component j)
        (((F j).commute (signatureTower F)).backward y))).trans
      (((F j).commute (signatureTower F)).forward_backward y)

/-- Build an element of the solution from its unfolding. -/
def roll (F : Signature.{i, u} I) (j : I) : ((F j).obj (solve F)) → solve F j :=
  (familySolution F j).backward

/-- Unfold an element of the solution. -/
def unroll (F : Signature.{i, u} I) (j : I) : solve F j → (F j).obj (solve F) :=
  (familySolution F j).forward

theorem unroll_roll (F : Signature.{i, u} I) (j : I) (fields : (F j).obj (solve F)) :
    unroll F j (roll F j fields) = fields :=
  (familySolution F j).forward_backward fields

theorem roll_unroll (F : Signature.{i, u} I) (j : I) (value : solve F j) :
    roll F j (unroll F j value) = value :=
  (familySolution F j).backward_forward value

theorem unroll_continuous (F : Signature.{i, u} I) (j : I) : Continuous (unroll F j) :=
  (familySolution F j).forward.cont

theorem roll_continuous (F : Signature.{i, u} I) (j : I) : Continuous (roll F j) :=
  (familySolution F j).backward.cont

theorem roll_injective (F : Signature.{i, u} I) (j : I) {x y : (F j).obj (solve F)}
    (h : roll F j x = roll F j y) : x = y := by
  have := congrArg (unroll F j) h
  simpa only [unroll_roll] using this

end Signature

end NonPos.Domain
