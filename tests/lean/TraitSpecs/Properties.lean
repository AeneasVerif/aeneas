module
public import Aeneas
public import TraitSpecs.TraitSpecs
public section

open Aeneas Aeneas.Std Result

/-! Library specs for any instance, assuming specs of its methods; applied with `step*` alone. -/

namespace trait_specs

/-! ## The library -/

@[step]
theorem Priced.with_tax.default_spec {Self : Type} (inst : Priced Self) (f : Self → Nat)
    (hprice : ∀ x, f x ≤ U32.max → inst.price x ⦃ p => p.val = f x ⦄)
    (x : Self) (h : f x + f x / 5 ≤ U32.max) :
    Priced.with_tax.default inst x ⦃ r => r.val = f x + f x / 5 ⦄ := by
  unfold Priced.with_tax.default
  step*

@[step]
theorem max_key_spec {T : Type} (inst : Keyed T) (f : T → Nat)
    (hkey : ∀ x, inst.key x ⦃ k => k.val = f x ⦄) (a b : T) :
    max_key inst a b ⦃ r => r.val = max (f a) (f b) ⦄ := by
  unfold max_key
  step* <;> grind

@[step]
theorem Fee.total.default_spec {Self : Type} (inst : Fee Self) (f : Self → U32 → Nat)
    (hfee : ∀ x n, f x n ≤ U32.max → inst.fee x n ⦃ r => r.val = f x n ⦄)
    (x : Self) (n : U32) (h : n.val + f x n ≤ U32.max) :
    Fee.total.default inst x n ⦃ r => r.val = n.val + f x n ⦄ := by
  unfold Fee.total.default
  step*

@[step]
theorem Account.deposit_two.default_spec {Self : Type} (inst : Account Self) (v : Self → Nat)
    (hdeposit : ∀ x n, v x + n.val ≤ U32.max → inst.deposit x n ⦃ y => v y = v x + n.val ⦄)
    (x : Self) (a b : U32) (h : v x + a.val + b.val ≤ U32.max) :
    Account.deposit_two.default inst x a b ⦃ y => v y = v x + a.val + b.val ⦄ := by
  unfold Account.deposit_two.default
  step*

@[step]
theorem Bounded.clamp.default_spec {Self : Type} (inst : Bounded Self) (lo hi : Self → Nat)
    (hlo : ∀ x, inst.lo x ⦃ r => r.val = lo x ⦄) (hhi : ∀ x, inst.hi x ⦃ r => r.val = hi x ⦄)
    (x : Self) (n : U32) (h : lo x ≤ hi x) :
    Bounded.clamp.default inst x n ⦃ r => lo x ≤ r.val ∧ r.val ≤ hi x ⦄ := by
  unfold Bounded.clamp.default
  step*

@[step]
theorem Pair.Insts.Trait_specsPriced.price_spec {T : Type} (inst : Priced T) (f : T → Nat)
    (hprice : ∀ x, f x ≤ U32.max → inst.price x ⦃ p => p.val = f x ⦄)
    (p : Pair T) (h : f p.first + f p.second ≤ U32.max) :
    Pair.Insts.Trait_specsPriced.price inst p ⦃ r => r.val = f p.first + f p.second ⦄ := by
  unfold Pair.Insts.Trait_specsPriced.price
  step*

/-! ## The user

The methods are unfolded, except `Employee`'s `key`: a ghost can't be inferred from a method which
branches, so it gets a spec. -/

attribute [local step_simps]
  Item.Insts.Trait_specsPriced.price
  PercentFee.Insts.Trait_specsFee.fee
  Wallet.Insts.Trait_specsAccount.deposit
  Percent.Insts.Trait_specsBounded.lo
  Percent.Insts.Trait_specsBounded.hi

@[step]
theorem Employee.Insts.Trait_specsKeyed.key_spec (e : Employee) :
    Employee.Insts.Trait_specsKeyed.key e ⦃ k => k.val = max e.salary.val e.bonus.val ⦄ := by
  unfold Employee.Insts.Trait_specsKeyed.key
  step* <;> grind

/-- A generic function; the method has its own spec. -/
theorem max_employee_key_spec (a b : Employee) :
    max_employee_key a b ⦃ r => r.val = max (max a.salary.val a.bonus.val)
      (max b.salary.val b.bonus.val) ⦄ := by
  unfold max_employee_key
  step*

/-- A method with an extra argument: a two-argument ghost. -/
theorem percent_total_spec (f : PercentFee) (n : U32)
    (h : n.val + n.val / 100 * f.percent.val ≤ U32.max) :
    percent_total f n ⦃ r => r.val = n.val + n.val / 100 * f.percent.val ⦄ := by
  unfold percent_total
  step*

/-- A `&mut self` method: the ghost measures the state. -/
theorem wallet_deposit_two_spec (w : Wallet) (a b : U32)
    (h : w.cents.val + a.val + b.val ≤ U32.max) :
    wallet_deposit_two w a b ⦃ w' => w'.cents.val = w.cents.val + a.val + b.val ⦄ := by
  unfold wallet_deposit_two
  step*

/-- Two methods returning constants. -/
theorem clamp_percent_spec (n : U32) : clamp_percent n ⦃ r => r.val ≤ 100 ⦄ := by
  unfold clamp_percent
  step*

/-- A default method calling a fallible method, of a generic impl whose method needs a spec of
its parameter: nested discharge. -/
theorem pair_with_tax_spec (p : Pair Item)
    (h : let s := p.first.unit.val * p.first.qty.val + p.second.unit.val * p.second.qty.val
      s + s / 5 ≤ U32.max) :
    pair_with_tax p ⦃ r => let s := p.first.unit.val * p.first.qty.val +
      p.second.unit.val * p.second.qty.val; r.val = s + s / 5 ⦄ := by
  unfold pair_with_tax
  step*

end trait_specs
