open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory
open primitivesBaseTacLib

val _ = new_theory "primitivesArith"

(* TODO: we need a better library of lemmas about arithmetic *)

(* We generate and save an induction theorem for positive integers *)
Theorem int_induction:
  !(P : int -> bool). P 0 /\ (!i. 0 <= i /\ P i ==> P (i+1)) ==> !i. 0 <= i ==> P i
Proof
  ntac 4 strip_tac >>
  Induct_on ‘Num i’ >> rpt strip_tac
  >-(sg ‘i = 0’ >- cooper_tac >> fs []) >>
  last_assum (qspec_assume ‘i-1’) >>
  fs [] >> pop_assum irule >>
  rw [] >> try_tac cooper_tac >>
  first_assum (qspec_assume ‘i - 1’) >>
  pop_assum irule >>
  rw [] >> try_tac cooper_tac
QED

val _ = TypeBase.update_induction int_induction

(* TODO: add those as rewriting theorems by default *)
val not_le_eq_gt = store_thm("not_le_eq_gt", “!(x y: int). ~(x <= y) <=> x > y”, cooper_tac)
val not_lt_eq_ge = store_thm("not_lt_eq_ge", “!(x y: int). ~(x < y) <=> x >= y”, cooper_tac)
val not_ge_eq_lt = store_thm("not_ge_eq_lt", “!(x y: int). ~(x >= y) <=> x < y”, cooper_tac)
val not_gt_eq_le = store_thm("not_gt_eq_le", “!(x y: int). ~(x > y) <=> x <= y”, cooper_tac)

val ge_eq_le = store_thm("ge_eq_le", “!(x y : int). x >= y <=> y <= x”, cooper_tac)
val le_eq_ge = store_thm("le_eq_ge", “!(x y : int). x <= y <=> y >= x”, cooper_tac)
val gt_eq_lt = store_thm("gt_eq_lt", “!(x y : int). x > y <=> y < x”, cooper_tac)
val lt_eq_gt = store_thm("lt_eq_gt", “!(x y : int). x < y <=> y > x”, cooper_tac)

Theorem int_of_num:
  ∀i. 0 ≤ i ⇒ &Num i = i
Proof
  fs [INT_OF_NUM]
QED

Theorem int_add:
  ∀m n. &(m + n) = &m + &n
Proof
  fs [INT_ADD]
QED

Theorem int_of_num_inj:
  !n m. &n = &m ==> n = m
Proof
  rpt strip_tac >>
  fs [Num]
QED

Theorem num_sub_eq:
  !(x y z : int). x = y - z ==> 0 <= x ==> 0 <= z ==> Num y = Num z + Num x
Proof
  rpt strip_tac >>
  sg ‘0 <= y’ >- cooper_tac >>
  rfs [] >>
  (* Convert to integers *)
  irule int_of_num_inj >>
  imp_res_tac int_of_num >>
  (* Associativity of & *)
  pure_rewrite_tac [int_add] >>
  fs []
QED

Theorem num_sub_1_eq:
  !(x y : int). x = y - 1 ==> 0 <= x ==> Num y = SUC (Num x)
Proof
  rpt strip_tac >>
  (* Get rid of the SUC *)
  sg ‘SUC (Num x) = 1 + Num x’ >-(rw [ADD]) >> rw [] >>
  (* Massage a bit the goal *)
  qsuff_tac ‘Num y = Num (y − 1) + Num 1’ >- cooper_tac >>
  (* Apply the general theorem *)
  irule num_sub_eq >>
  cooper_tac
QED

Theorem pos_mul_pos_is_pos:
  !(x y : int). 0 <= x ==> 0 <= y ==> 0 <= x * y
Proof
  rpt strip_tac >>
  sg ‘0 <= &(Num x) * &(Num y)’ >- (rw [INT_MUL_CALCULATE] >> cooper_tac) >>
  sg_dep_rewrite_all_tac int_of_num >> try_tac cooper_tac >> fs []
QED

Theorem pos_div_pos_is_pos:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x / y
Proof
  rpt strip_tac >>
  rw [le_eq_ge] >>
  sg ‘y <> 0’ >- cooper_tac >>
  qspecl_then [‘\x. x >= 0’, ‘x’, ‘y’] ASSUME_TAC INT_DIV_FORALL_P >>
  fs [] >> pop_ignore_tac >> rw [] >- cooper_tac >>
  fs [not_lt_eq_ge] >>
  (* Proof by contradiction: assume k < 0 *)
  spose_not_then assume_tac >>
  fs [not_ge_eq_lt] >>
  sg ‘k * y = (k + 1) * y + - y’ >- (fs [INT_RDISTRIB] >> cooper_tac) >>
  sg ‘0 <= (-(k + 1)) * y’ >- (irule pos_mul_pos_is_pos >> cooper_tac) >>
  cooper_tac
QED

Theorem pos_div_pos_le:
  !(x y d : int). 0 <= x ==> 0 <= y ==> 0 < d ==> x <= y ==> x / d <= y / d
Proof
  rpt strip_tac >>
  sg ‘d <> 0’ >- cooper_tac >>
  qspecl_assume [‘\k. k = x / d’, ‘x’, ‘d’] INT_DIV_P >>
  qspecl_assume [‘\k. k = y / d’, ‘y’, ‘d’] INT_DIV_P >>
  rfs [not_lt_eq_ge] >> try_tac cooper_tac >>
  sg ‘y = (x / d) * d + (r' + y - x)’ >- cooper_tac >>
  qspecl_assume [‘(x / d) * d’, ‘r' + y - x’, ‘d’] INT_ADD_DIV >>
  rfs [] >>
  Cases_on ‘x = y’ >- fs [] >>
  sg ‘r' + y ≠ x’ >- cooper_tac >> fs [] >>
  sg ‘((x / d) * d) / d = x / d’ >- (irule INT_DIV_RMUL >> cooper_tac) >>
  fs [] >>
  sg ‘0 <= (r' + y − x) / d’ >- (irule pos_div_pos_is_pos >> cooper_tac) >>
  metis_tac [INT_LE_ADDR]
QED

Theorem pos_div_pos_le_init:
  !(x y : int). 0 <= x ==> 0 < y ==> x / y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- cooper_tac >>
  qspecl_assume [‘\k. k = x / y’, ‘x’, ‘y’] INT_DIV_P >>
  rfs [not_lt_eq_ge] >- cooper_tac >>
  sg ‘y = (y - 1) + 1’ >- rw [] >>
  sg ‘x = x / y + ((x / y) * (y - 1) + r)’ >-(
    qspecl_assume [‘1’, ‘y-1’, ‘x / y’] INT_LDISTRIB >>
    rfs [] >>
    cooper_tac
  ) >>
  sg ‘!a b c. 0 <= c ==> a = b + c ==> b <= a’ >- cooper_tac >>
  pop_assum irule >>
  exists_tac “x / y * (y − 1) + r” >>
  sg ‘0 <= x / y’ >- (irule pos_div_pos_is_pos >> cooper_tac) >>
  sg ‘0 <= (x / y) * (y - 1)’ >- (irule pos_mul_pos_is_pos >> cooper_tac) >>
  cooper_tac
QED

Theorem pos_mod_pos_is_pos:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x % y
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- cooper_tac >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- cooper_tac >> fs []
QED

Theorem pos_mod_pos_le_init:
  !(x y : int). 0 <= x ==> 0 < y ==> x % y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- cooper_tac >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- cooper_tac >> fs [] >>
  sg ‘0 <= x % y’ >- (irule pos_mod_pos_is_pos >> cooper_tac) >>
  sg ‘0 <= x / y’ >- (irule pos_div_pos_is_pos >> cooper_tac) >>
  sg ‘0 <= (x / y) * y’ >- (irule pos_mul_pos_is_pos >> cooper_tac) >>
  cooper_tac
QED

val _ = export_theory ()
