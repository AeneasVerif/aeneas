namespace Aeneas.Data.Coinductive

structure Effect : Type (u + 1) where
  I : Type u
  O : I → Type u

def SumE (E₁ : Effect.{u}) (E₂ : Effect.{u}) : Effect.{u} where
  I := E₁.I ⊕ E₂.I
  O
  | .inl i => E₁.O i
  | .inr i => E₂.O i

infixr:30 " ⊕ₑ " => SumE

-- we cannot make `SumE` reducible since we want to key on it in TC search,
-- but we also need to make sure that SumE.O reduces at reducible transparency
-- thus we add the following unification hints
unif_hint (E₁ E₂ : Effect.{u}) (T : Type u) (e : E₁.I)  where
  E₁.O e ≟ T |- (E₁ ⊕ₑ E₂).O (Sum.inl e) ≟ T
unif_hint (E₁ E₂ : Effect.{u}) (T : Type u) (e : E₂.I)  where
  E₂.O e ≟ T |- (E₁ ⊕ₑ E₂).O (Sum.inr e) ≟ T

class Subeffect (E₁ : Effect.{u}) (E₂ : Effect.{v}) where
  map : (i₁ : E₁.I) → ((i₂ : E₂.I) × (E₂.O i₂ → E₁.O i₁))

infix:20 " -< " => Subeffect

instance {E : Effect} : E -< E where
  map i := ⟨i, λ x => x⟩

instance {E₁ : Effect} {E₂ : Effect} {E' : Effect} [subl : E₁ -< E'] [subr : E₂ -< E'] : (E₁ ⊕ₑ E₂) -< E' where
  map
  | .inl x => subl.map x
  | .inr x => subr.map x

instance (priority:=mid) {E₁ : Effect} {E₂ : Effect} {E' : Effect} [sub : E₁ -< E₂] : E₁ -< (E₂ ⊕ₑ E') where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inl i, f⟩

instance (priority:=low) {E₁ : Effect} {E₂ : Effect} {E' : Effect} [sub : E₁ -< E₂] : E₁ -< E' ⊕ₑ E₂ where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inr i, f⟩

end Aeneas.Data.Coinductive
