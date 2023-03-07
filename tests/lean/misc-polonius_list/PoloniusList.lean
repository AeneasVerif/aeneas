-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [polonius_list]
import Base.Primitives

structure OpaqueDefs where
  
  /- [polonius_list::List] -/
  inductive list_t (T : Type) :=
  | ListCons : T -> list_t T -> list_t T
  | ListNil : list_t T
  
  /- [polonius_list::get_list_at_x] -/
  def get_list_at_x_fwd
    (ls : list_t UInt32) (x : UInt32) : Result (list_t UInt32) :=
    match h: ls with
    | list_t.ListCons hd tl =>
      if h: hd = x
      then Result.ret (list_t.ListCons hd tl)
      else get_list_at_x_fwd tl x
    | list_t.ListNil => Result.ret list_t.ListNil
  
  /- [polonius_list::get_list_at_x] -/
  def get_list_at_x_back
    (ls : list_t UInt32) (x : UInt32) (ret0 : list_t UInt32) :
    Result (list_t UInt32)
    :=
    match h: ls with
    | list_t.ListCons hd tl =>
      if h: hd = x
      then Result.ret ret0
      else
        do
          let tl0 ← get_list_at_x_back tl x ret0
          Result.ret (list_t.ListCons hd tl0)
    | list_t.ListNil => Result.ret ret0
  