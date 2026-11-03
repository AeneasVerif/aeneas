module
public import Aeneas.NonPos.Top

@[expose] public section
-- `partial_fixpoint` misses the fixed parameters of a self-referential instance when the `by` proof
-- in its body is abstracted into an auxiliary theorem, as happens by default in a public section.
set_option backward.proofsInPublic true
/-!
# Tests, over `Option`
-/
namespace NonPos.Test
open NonPos NonPos.Domain Lean.Order

universe u w

/-! ## `Option` as a supported monad

Its order is the flat one of Lean core (`FlatOrder none`), for which every chain is attained, so
monotone functions out of it are continuous. -/
section OptionMonad
variable {α : Type u}

theorem Option.le_iff {x y : Option α} : x ⊑ y ↔ x = none ∨ x = y := by
  constructor
  · intro h
    cases h with
    | bot => exact Or.inl rfl
    | refl => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl

theorem Option.chain_attained (c : Chain (Option α)) : ∃ n, ∀ m, c m ⊑ c n := by
  by_cases h : ∃ n a, c n = some a
  · obtain ⟨n, a, hn⟩ := h
    refine ⟨n, fun m => ?_⟩
    rcases Nat.le_total m n with hm | hm
    · exact c.le hm
    · have hnm := c.le hm
      rw [hn] at hnm
      rcases Option.le_iff.1 hnm with h' | h'
      · cases h'
      · rw [hn, ← h']
  · refine ⟨0, fun m => ?_⟩
    have hm : c m = none := by
      cases hm : c m with
      | none => rfl
      | some a => exact absurd ⟨m, a, hm⟩ h
    rw [hm]; exact FlatOrder.rel.bot

theorem Option.cont_of_mono {B : Type w} [Dom B] {f : Option α → B}
    (mono : ∀ x y, x ⊑ y → Dom.le (f x) (f y)) : @Cont (Option α) B (Dom.ofCCPO (Option α)) _ f := by
  refine Cont.mk' _ mono (fun c => ?_)
  obtain ⟨n, hn⟩ := Option.chain_attained c
  rw [show @Dom.sup _ (Dom.ofCCPO (Option α)) c = c n from
    @sup_eq_of_attained _ (Dom.ofCCPO (Option α)).po (Dom.ofCCPO (Option α)).os c n hn]
  exact (@sup_eq_of_attained B Dom.po Dom.os (@Chain.map _ _ (Dom.ofCCPO (Option α)).po Dom.po c f mono) n
    (fun m => mono _ _ (hn m))).symm

noncomputable instance : NonPosMonad Option where
  bind_cont := fun {α β} => by
    letI : Dom (Option α) := Dom.ofCCPO (Option α)
    letI : Dom (Option β) := Dom.ofCCPO (Option β)
    refine Cont.puncurry (f := fun (x : Option α) (k : α → Option β) => x >>= k) (fun k => ?_) (fun x => ?_)
    · refine Option.cont_of_mono (fun x y h => ?_)
      cases h with
      | bot => exact FlatOrder.rel.bot
      | refl => exact PartialOrder.rel_refl
    · cases x with
      | none => exact Cont.const none
      | some a => exact Cont.app (f := fun k : α → Option β => k) Cont.id a
end OptionMonad

/-! ## The example of the goal -/

nonpos_structure Example1 : Type where
  to_nat : Nat
  f : Example1 → Option Nat

#check @Example1.mk
#check @Example1.to_nat
#check @Example1.f
#check @Example1.f_mk

/-- A method applied to the dictionary being varied itself. -/
example : Cont (fun d : Example1 => d.f d) := by nonpos_cont

/-! ## `Bla`, with `Option` in place of `Result` -/

nonpos_structure Bla (Self : Type) : Type 1 where
  to_num : Self → Option Int
  add : ∀ {Other : Type} (BlaInst : Bla Other), Other → Self → Option Int

#check @Bla.mk
#check @Bla.add

/-- The method bodies, as Aeneas would generate them. -/
def IntBla.to_num (self : Int) : Option Int := some self
def IntBla.add {Other : Type} (BlaInst : Bla Other) (o : Other) (s : Int) : Option Int := do
  let i ← BlaInst.to_num o
  let i1 ← IntBla.to_num s
  pure (i + i1)

/-- The instance: the condition is discharged by the tactic. -/
def IntBla : Bla Int :=
  Bla.mk IntBla.to_num (fun {Other} (BlaInst : Bla Other) => IntBla.add BlaInst) (by nonpos_cont)

example (x : Int) : Bla.to_num IntBla x = some x := by simp [IntBla, IntBla.to_num]
example {O : Type} (inst : Bla O) (o : O) (s : Int) : Bla.add IntBla inst o s = IntBla.add inst o s := by
  simp [IntBla]
/-! ## A mutual group -/

mutual
nonpos_structure A (Self : Type) : Type 1 where
  fa : ∀ {O : Type} (BInst : B O), Self → O → Option Nat
nonpos_structure B (Self : Type) : Type 1 where
  fb : ∀ {O : Type} (AInst : A O), Self → O → Option Nat
end

#check @A.fa
#check @B.mk

/-! ## Parameters of several kinds -/

nonpos_structure WithParams (Self : Type) (n : Nat) : Type 1 where
  get : Self → Option (Fin n)
  comb : ∀ {O : Type} {m : Nat} (inst : WithParams O m), O → Self → Option Nat

#check @WithParams.comb

end NonPos.Test

namespace NonPos.Test
open NonPos

/-! ## A generic instance: `mk` under a binder -/

structure Wrapper (T : Type) where
  x : T

def WrapperBla.to_num {T : Type} (BlaInst : Bla T) (self : Wrapper T) : Option Int :=
  BlaInst.to_num self.x
def WrapperBla.add {T Other : Type} (BlaInst : Bla T) (BlaInst1 : Bla Other) (o : Other) (s : Wrapper T) :
    Option Int :=
  BlaInst.add BlaInst1 o s.x

def WrapperBla {T : Type} (BlaInst : Bla T) : Bla (Wrapper T) :=
  Bla.mk (WrapperBla.to_num BlaInst) (fun {Other} (BlaInst1 : Bla Other) => WrapperBla.add BlaInst BlaInst1)
    (by nonpos_cont)

/-- The generic instance is itself continuous (as Aeneas's `use_wrapper` needs). -/
example {T : Type} : Cont (fun BlaInst : Bla T => WrapperBla BlaInst) := by nonpos_cont

/-! ## Bodies with `match`, `if`, and a helper -/

def helper {O : Type} (BlaInst : Bla O) (o : O) : Option Int := do
  let i ← BlaInst.to_num o
  pure (i * 2)

def Forms.add {Other : Type} (BlaInst : Bla Other) (o : Other) (s : Int) : Option Int := do
  let n ← helper BlaInst o
  match (n > 10 : Bool) with
  | true => none
  | false =>
    if s < 0 then BlaInst.to_num o
    else pure (n + s)

example {Other : Type} : Cont (fun BlaInst : Bla Other => Forms.add BlaInst) := by nonpos_cont

/-! ## A self-referential instance (`Sym`): the method passes its own instance along -/

def SymBla : Bla Int :=
  Bla.mk (fun s => some s) (fun {Other} (BlaInst : Bla Other) o s => BlaInst.add SymBla s o) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)

example {O : Type} (inst : Bla O) (o : O) (s : Int) : Bla.add SymBla inst o s = inst.add SymBla s o := by
  conv => lhs; rw [SymBla.eq_1]
  simp

/-- A generic self-referential instance: depends on a dictionary parameter, and is itself continuous
in it (covered by `Cont.fix`, since `partial_fixpoint` elaborates to `Lean.Order.fix`). -/
def SymWrap {T : Type} (b : Bla T) : Bla (Wrapper T) :=
  Bla.mk (fun w => b.to_num w.x) (fun {O} (i : Bla O) o w => i.add (SymWrap b) w o) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)

example {T : Type} : Cont (fun b : Bla T => SymWrap b) := by nonpos_cont

/-! Mutually recursive self-referential instances of the mutual pair `A`/`B`. -/
mutual
def natA2 : A Nat := A.mk (fun {O} (_ : B O) s _ => B.fb natB2 natA2 (s + 1) (s + 1)) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)
def natB2 : B Nat := B.mk (fun {O} (_ : A O) s _ => if s = 0 then A.fa natA2 natB2 1 1 else some s) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)
end

/-! ## A plain field holding a dictionary of a recursive structure -/

nonpos_structure RecParent (Self : Type) : Type 1 where
  rp : ∀ {O : Type} (inst : RecParent O), Self → O → Option Nat

structure Child2 (Self : Type) where
  RecParentInst : RecParent Self
  c2 : Self → Option Nat

/-! ## A plain dictionary field (a supertrait), with a self-referential instance, and a mixed structure -/

nonpos_structure Parent (Self : Type) : Type 1 where
  pf : Self → Option Nat
nonpos_structure Child (Self : Type) : Type 1 where
  parent : Parent Self
  cf : ∀ {O : Type} (inst : Child O), Self → O → Option Nat

example : Pointed (Child Int) := inferInstance

def SymChild : Child Int :=
  Child.mk (Parent.mk (fun _ => some 0) (by nonpos_cont))
    (fun {O} (inst' : Child O) s o => inst'.cf SymChild o s) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)

example {O : Type} (inst' : Child O) (s : Int) (o : O) : Child.cf SymChild inst' s o = inst'.cf SymChild o s := by
  conv => lhs; rw [SymChild.eq_1]
  simp

/-- Data, a plain dictionary field and a function field together. -/
nonpos_structure Mixed (Self : Type) : Type 1 where
  n : Nat
  parent : Parent Self
  mf : Self → Option Nat

noncomputable example (m : Mixed Int) : Nat := m.n
example : Cont (fun m : Mixed Int => m.mf) := by nonpos_cont

/-! ## `partial_fixpoint` with a dictionary parameter -/

def countdown {O : Type} (BlaInst : Bla O) (o : O) (n : Nat) : Option Int :=
  match n with
  | 0 => BlaInst.to_num o
  | n + 1 => do
    let _ ← BlaInst.to_num o
    countdown BlaInst o n
partial_fixpoint

example {O : Type} (o : O) : Cont (fun BlaInst : Bla O => countdown BlaInst o) := by nonpos_cont

/-! ## A mutual `partial_fixpoint`, packed into a `PProd` -/

mutual
def evenC {O : Type} (BlaInst : Bla O) (o : O) (n : Nat) : Option Int :=
  match n with
  | 0 => BlaInst.to_num o
  | n + 1 => do let _ ← BlaInst.to_num o; oddC BlaInst o n
partial_fixpoint
def oddC {O : Type} (BlaInst : Bla O) (o : O) (n : Nat) : Option Int :=
  match n with
  | 0 => pure 1
  | n + 1 => evenC BlaInst o n
partial_fixpoint
end

example {O : Type} (o : O) : Cont (fun BlaInst : Bla O => evenC BlaInst o) := by nonpos_cont
example {O : Type} (o : O) : Cont (fun BlaInst : Bla O => oddC BlaInst o) := by nonpos_cont

/-! ## Compiled evaluation

The definitions above are not `noncomputable`: dictionaries are compiled as their tuples of fields
(section 3 of `Top.lean`).  `#guard` evaluates with the compiled code and fails the build on a wrong
result.  This includes the self-referential `SymBla` and `SymChild`, defined by `partial_fixpoint`. -/

def StrBla : Bla String :=
  Bla.mk (fun s => some s.length) (fun {Other} (_ : Bla Other) _ s => some (2 * s.length)) (by nonpos_cont)

#guard Bla.to_num IntBla 7 = some 7
#guard Bla.add IntBla StrBla "hello" 10 = some 15        -- `IntBla.add` calls the other dictionary's `to_num`
#guard Bla.add IntBla IntBla 2 3 = some 5
#guard Bla.to_num (WrapperBla StrBla) ⟨"abc"⟩ = some 3    -- a generic instance
#guard Forms.add StrBla "abcdef" 4 = none                -- `match` in the body: `n = 12 > 10`
#guard Forms.add StrBla "ab" 4 = some 8
#guard countdown StrBla "xyz" 5 = some 3                 -- `partial_fixpoint`
#guard evenC StrBla "xy" 3 = some 1                      -- mutual `partial_fixpoint`

-- self-referential instances: `SymBla.add inst o s = inst.add SymBla s o`
#guard Bla.add SymBla IntBla 2 3 = some 5                -- `IntBla.add SymBla 3 2 = SymBla.to_num 3 + 2`
#guard Bla.add SymBla StrBla "hello" 2 = some 10         -- `StrBla.add SymBla 2 "hello" = 2 * 5`

def NatChild : Child Nat :=
  Child.mk (Parent.mk (fun n => some n) (by nonpos_cont)) (fun {O} (_ : Child O) s _ => some s) (by nonpos_cont)

#guard Parent.pf (Child.parent SymChild) 3 = some 0
#guard Child.cf SymChild NatChild 7 4 = some 4           -- `NatChild.cf SymChild 4 7 = some 4`
#guard Bla.to_num (SymWrap IntBla) ⟨6⟩ = some 6
#guard Bla.add (SymWrap IntBla) IntBla 1 ⟨2⟩ = some 3      -- `IntBla.add (SymWrap IntBla) ⟨2⟩ 1`
#guard A.fa natA2 natB2 4 7 = some 5                     -- `natB2.fb natA2 5 5 = some 5`

/-! ## A cycle closed by an `= Self` equation (simba's `ComplexField`/`RealField`, ark-ff's `Field`/`PrimeField`)

```rust
pub trait Complex: Sized {
    type Re: Real;                       // an associated type bounded by the other trait
    fn abs(self) -> Self::Re;
}
pub trait Real: Complex<Re = Self> {     // the other trait has the first as supertrait, with `Re = Self`
    fn sqrt(self) -> Self;
}
impl Complex for u32 { type Re = u32; fn abs(self) -> u32 { self } }
impl Real for u32 { fn sqrt(self) -> u32 { self } }
```

The `Complex` dictionary of `u32` holds the `Real` dictionary of `u32`, which holds the `Complex`
dictionary of `u32` again, without end.

**As Aeneas outputs it today** (`AeneasTests/exp8*`, 2026-10-26).  With the equation `Re = Self`
Aeneas stops with an internal error.  Without it (`trait Real: Complex`) it emits what follows, with
`sorry.Re` in place of `Re` in the type of `abs`, and warns that the result will not type-check: the
associated type of a recursive group stays a field, so `Complex` is a dependent structure, and the two
structures are emitted one after the other. -/

/--
error: Unknown identifier `Real`

Note: It is not possible to treat `Real` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
set_option autoImplicit false in
structure Complex (Self : Type) where
  Re : Type
  ReRealInst : Real Re
  abs : Self → Option Re

/-! Putting the two in a `mutual` block does not help: a field of type `Real Re` applies the type being
defined to a field, not to a parameter, which inductive types do not allow. -/
/--
error: (kernel) invalid occurrence of datatype 'NonPos.Test.Real' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mutual
structure Complex (Self : Type) where
  Re : Type
  ReRealInst : Real Re
  abs : Self → Option Re
structure Real (Self : Type) where
  ComplexInst : Complex Self
  sqrt : Self → Option Self
end

/-! The impls Aeneas emits are two plain `def`s, each using the other (`U32.Insts.Complex` holds
`U32.Insts.Real` and conversely), which Lean rejects as well, even where the types exist.

**Option 2** (see the discussion of Aeneas issue #176): Aeneas turns the associated type into a
parameter and substitutes the equation, so `Real S` holds `Complex S S`.  The dictionaries become
finite values that refer to themselves, which the command accepts as a mutual group: -/

mutual
nonpos_structure Complex2 (Self : Type) (Re : Type) : Type 1 where
  ReRealInst : Real2 Re
  abs : Self → Option Re
nonpos_structure Real2 (Self : Type) : Type 1 where
  ComplexInst : Complex2 Self Self
  sqrt : Self → Option Self
end

/-! The impls would then be mutual self-referential instances, as `natA2`/`natB2` above.  This is
where the present library stops: totality is a least fixed point, so a cycle of plain dictionary
fields has no total element: `Complex2 Nat Nat` is empty (as `partial_fixpoint` reports), so it is
not pointed and has no `CCPO` instance.  Option 2 needs the totality of such groups changed in the model (every element
of a group without data fields counts as total), under a well-formedness condition that would
return to Top. -/

/--
error: failed to compile definition 'NonPos.Test.natComplex2' using `partial_fixpoint`, could not prove that the type
  Complex2 Nat Nat
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
mutual
def natComplex2 : Complex2 Nat Nat := Complex2.mk natReal2 (fun s => some s) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)
def natReal2 : Real2 Nat := Real2.mk natComplex2 (fun s => some s) (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)
end

end NonPos.Test
