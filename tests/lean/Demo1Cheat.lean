import Base
open Primitives
open Result

namespace demo

namespace ex
  inductive List (a : Type) where
  | nil : List a
  | cons (head : a) (tail : List a) : List a

  namespace List

    @[simp]
    def len {a : Type} (ls : List a) : ℤ :=
      match ls with
      | nil => 0
      | cons _ tl => 1 + tl.len

    @[simp]
    def append {a : Type} (l0 l1 : List a) : List a :=
      match l0 with
      | nil => l1
      | cons h tl => cons h (append tl l1)

    def append_len_eq {a : Type} (l0 l1 : List a) : (l0.append l1).len = l0.len + l1.len := by
      induction l0
      . unfold append
        conv => rhs; lhs; unfold len
        simp
      . unfold append
        rename a => h
        rename List a => tl
        rename _ => hi
        conv => lhs; unfold len
        conv => rhs; lhs; unfold len
        rw [hi]
        scalar_tac

    def append_len_eq1 {a : Type} (l0 l1 : List a) : (l0.append l1).len = l0.len + l1.len := by
      induction l0
      . simp
      . simp [*]
        scalar_tac

    def append_len_eq2 {a : Type} (l0 l1 : List a) : (l0.append l1).len = l0.len + l1.len := by
      match l0 with
      | nil => simp
      | cons h tl =>
        have hi := append_len_eq2 tl l1
        simp [*]
        scalar_tac

  end List
end ex

structure MySubtype {α : Type} (p : α → Prop) where
  val : α
  property : p val

#check Subtype
def Vec (a : Type) (n : ℤ) := { l : List a // l.len = n }

-- set_option pp.explicit true
-- set_option pp.universes true
-- set_option pp.notation false

#check Vec
#print Vec

def append {a : Type} {n m : ℤ} (v : Vec a n) (w : Vec a m) : Vec a (n + m) :=
  let ⟨ vl, hv ⟩ := v
  match vl with
  | .nil =>
    ⟨ w.val, by cases w; simp_all ⟩
  | .cons x vtl =>
    let vtl : Vec a (n - 1) := ⟨ vtl, by simp_all; int_tac ⟩
    let ⟨ vw, hvw ⟩ := append vtl w
    ⟨ x :: vw, by simp_all; int_tac ⟩ 
termination_by append v w => v.val

end demo
