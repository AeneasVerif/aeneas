module

public import Aeneas.Std.Core.Pointee
public import Aeneas.Std.Array.Array

/-! The representation of the arrays: their elements one after the other (as nested pairs, see
`Repr.prod`; the size of an element is a multiple of its alignment, so there is no padding). -/

@[expose] public section

namespace Aeneas.Std

/-- The lists of length `n`, as `n` elements one after the other. -/
def Repr.listN {T : Type} (r : Repr T) : (n : Nat) → Repr {l : List T // l.length = n}
  | 0 => Repr.unit _ ⟨[], rfl⟩ (by
      rintro ⟨l, h⟩
      cases l with
      | nil => rfl
      | cons _ _ => simp at h)
  | n + 1 => Repr.iso (Repr.prod r (Repr.listN r n))
      (fun l => match l with
        | ⟨x :: xs, h⟩ => (x, ⟨xs, by simpa using h⟩)
        | ⟨[], h⟩ => absurd h (by simp))
      (fun p => ⟨p.1 :: p.2.val, by simp [p.2.property]⟩)
      (by
        rintro ⟨l, h⟩
        cases l with
        | nil => simp at h
        | cons x xs => rfl)

instance {T : Type} [Pointee T] {N : Usize} : Pointee (Array T N) :=
  ⟨Repr.iso (Repr.listN (Pointee.repr (T := T)) N.val) (fun a => ⟨a.val, a.property⟩)
    (fun l => Array.from l.val l.property) (fun a => Array.val_from a a.property)⟩

end Aeneas.Std
