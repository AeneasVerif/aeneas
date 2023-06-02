open arithmeticTheory integerTheory
open primitivesBaseTacLib

val _ = new_theory "primitivesArith"

(* TODO: we need a better library of lemmas about arithmetic *)

val not_le_eq_gt = store_thm("not_le_eq_gt", “!(x y: int). ~(x <= y) <=> x > y”, cooper_tac)
val not_lt_eq_ge = store_thm("not_lt_eq_ge", “!(x y: int). ~(x < y) <=> x >= y”, cooper_tac)
(* TODO: add gsymed versions of those as rewriting theorems by default (we only want to
   manipulate ‘<’ and ‘≤’) *)
val not_ge_eq_lt = store_thm("not_ge_eq_lt", “!(x y: int). ~(x >= y) <=> x < y”, cooper_tac)
val not_gt_eq_le = store_thm("not_gt_eq_le", “!(x y: int). ~(x > y) <=> x <= y”, cooper_tac)

val ge_eq_le = store_thm("ge_eq_le", “!(x y : int). x >= y <=> y <= x”, cooper_tac)
val le_eq_ge = store_thm("le_eq_ge", “!(x y : int). x <= y <=> y >= x”, cooper_tac)
val gt_eq_lt = store_thm("gt_eq_lt", “!(x y : int). x > y <=> y < x”, cooper_tac)
val lt_eq_gt = store_thm("lt_eq_gt", “!(x y : int). x < y <=> y > x”, cooper_tac)

(* Miscelleanous *)
Theorem int_add_minus_same_eq:
  ∀ (i j : int). i + j - j = i
Proof
  int_tac
QED

(*
 * We generate and save an induction theorem for positive integers
 *)

(* This is the induction theorem we want.

   Unfortunately, it often can't be applied by [Induct_on].
 *)
Theorem int_induction_ideal:
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

(* THIS INDUCTION theorem works well with [Induct_on] *)
Theorem int_induction:
  !(P : int -> bool). (∀i. i < 0 ⇒ P i) ∧ P 0 /\ (!i. P i ==> P (i+1)) ==> !i. P i
Proof
  rw [] >>
  qspec_assume ‘P’ int_induction_ideal >>
  gvs [] >>
  Cases_on ‘0 ≤ i’ >> gvs [] >>
  last_x_assum irule >> int_tac
QED

val _ = TypeBase.update_induction int_induction

Theorem int_of_num_id:
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

(* TODO: use as rewriting theorem by default? *)
Theorem add_sub_same_eq:
  ∀(i j : int). i + j - j = i
Proof
  cooper_tac
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
  cooper_tac
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

Theorem pos_div_pos_ge:
  !(x y d : int). 0 <= x ==> 0 <= y ==> 0 < d ==> x >= y ==> x / d >= y / d
Proof
  metis_tac [pos_div_pos_le, ge_eq_le]
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

Theorem pos_mod_pos_lt:
  ∀ x y. 0 ≤ x ⇒ 0 < y ⇒ x % y < y
Proof
  rw [] >>
  qspecl_assume [‘x’, ‘y’] integerTheory.INT_MOD_BOUNDS >>
  sg ‘y ≠ 0 ∧ ~(y < 0)’ >- int_tac >> fs []
QED

Theorem pos_mod_pos_ineqs:
  ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ x % y ∧ x % y < y
Proof
  metis_tac [pos_mod_pos_is_pos, pos_mod_pos_lt]
QED

Theorem mul_pos_left_le:
  ∀ (a x y : int). 0 ≤ a ⇒ x ≤ y ⇒ a * x ≤ a * y
Proof
  rw [] >> Cases_on ‘a = 0’ >> fs [] >>
  sg ‘0 < a’ >- cooper_tac >>
  metis_tac [integerTheory.INT_LE_MONO]
QED

Theorem mul_pos_right_le:
  ∀ (a x y : int). 0 ≤ a ⇒ x ≤ y ⇒ x * a ≤ y * a
Proof
  rw [mul_pos_left_le, integerTheory.INT_MUL_COMM]
QED

Theorem mul_pos_left_lt:
  ∀ (a x y : int). 0 < a ⇒ x < y ⇒ a * x < a * y
Proof
  metis_tac [integerTheory.INT_LT_MONO]
QED

Theorem mul_pos_right_lt:
  ∀ (a x y : int). 0 < a ⇒ x < y ⇒ x * a < y * a
Proof
  metis_tac [mul_pos_left_lt, integerTheory.INT_MUL_COMM]
QED

Theorem pos_mul_left_pos_le:
  ∀ a x. 0 < a ⇒ 0 ≤ x ⇒ x ≤ a * x
Proof
  rw [] >>
  Cases_on ‘a = 1’ >> fs [] >>
  sg ‘0 ≤ (a - 1) * x’ >- (irule pos_mul_pos_is_pos >> int_tac) >>
  sg ‘x ≤ x + (a - 1) * x’ >- fs [] >>
  sg ‘a * x = 1 * x + (a - 1) * x’ >- fs [GSYM integerTheory.INT_RDISTRIB] >>
  fs []
QED

Theorem pos_mul_right_pos_le:
  ∀ a x. 0 < a ⇒ 0 ≤ x ⇒ x ≤ x * a
Proof
  metis_tac [pos_mul_left_pos_le, integerTheory.INT_MUL_COMM]
QED

Theorem pos_mul_left_pos_lt:
  ∀ a x. 1 < a ⇒ 0 < x ⇒ x < a * x
Proof
  rw [] >>
  sg ‘a * x = 1 * x + (a - 1) * x’
  >- (fs [GSYM integerTheory.INT_RDISTRIB]) >>
  fs [] >>
  sg ‘(a − 1) * x = 1 * x + (a - 2) * x’
  >- (
    fs [GSYM integerTheory.INT_RDISTRIB] >>
    sg ‘1 + (a − 2) = a - 1’ >- int_tac >>
    fs []
    ) >>
  fs [] >>
  sg ‘0 ≤ (a − 2) * x’ >- (irule pos_mul_pos_is_pos >> int_tac) >>
  int_tac
QED

Theorem pos_mul_right_pos_lt:
  ∀ a x. 1 < a ⇒ 0 < x ⇒ x < x * a
Proof
  metis_tac [pos_mul_left_pos_lt, integerTheory.INT_MUL_COMM]
QED

Theorem pos_div_pos_mul_le:
  ∀ x y. 0 ≤ x ⇒ 0 < y ⇒ (x / y) * y ≤ x
Proof
  rw [] >>
  qspec_assume ‘y’ integerTheory.INT_DIVISION >>
  sg ‘y ≠ 0 ∧ ~(y < 0)’ >- int_tac >> fs [] >>
  first_x_assum (qspec_assume ‘x’) >>
  fs [] >>
  (* TODO: int_tac loops here *)
  cooper_tac
QED

Theorem pos_mul_pos_div_pos_decompose:
  ∀ x y z. 0 ≤ x ⇒ 0 ≤ y ⇒ 0 < z ⇒ x / z + y / z ≤ (x + y) / z
Proof
  rw [] >>
  sg ‘z ≠ 0’ >- int_tac >>
  sg ‘(x / z * z + x % z) + (y / z * z + y % z) = (x + y) / z * z + (x + y) % z’ >- metis_tac [integerTheory.INT_DIVISION] >>
  sg ‘(x + y) % z = ((x % z) + (y % z)) % z’ >- metis_tac [integerTheory.INT_MOD_PLUS] >>
  sg ‘0 ≤ (x % z) ∧ 0 ≤ (y % z)’ >- metis_tac [pos_mod_pos_is_pos] >>
  sg ‘0 ≤ (x % z) + (y % z)’ >- int_tac >>
  sg ‘((x % z) + (y % z)) % z ≤ (x % z) + (y % z)’ >- metis_tac [pos_mod_pos_le_init] >>
  sg ‘x / z * z + y / z * z ≤ (x + y) / z * z’ >- int_tac >>
  sg ‘x / z * z + y / z * z = (x / z + y / z) * z’ >- fs [integerTheory.INT_RDISTRIB] >> fs [] >>
  sg ‘0 ≤ x / z’ >- (irule pos_div_pos_is_pos >> fs []) >>
  sg ‘0 ≤ y / z’ >- (irule pos_div_pos_is_pos >> fs []) >>
  sg ‘0 ≤ (x + y) / z’ >- (irule pos_div_pos_is_pos >> fs []) >>
  sg ‘(x / z + y / z) * z / z ≤ (x + y) / z * z / z’
  >- ( 
    irule pos_div_pos_le >> fs [] >>
    rw [] >> irule pos_mul_pos_is_pos >> fs []) >>
  imp_res_tac integerTheory.INT_DIV_RMUL >>
  metis_tac []
QED

Theorem pos_mul_2_div_pos_decompose:
  ∀ x y. 0 ≤ x ⇒ 0 < y ⇒ x / y + x / y ≤ x * 2 / y
Proof
  rw [] >>
  qspecl_assume [‘x’, ‘x’, ‘y’] pos_mul_pos_div_pos_decompose >> gvs [] >>
  sg ‘x * 2 = (x * 1) + (x * 1)’
  >- (pure_rewrite_tac [GSYM integerTheory.INT_LDISTRIB] >> fs []) >>
  fs []  
QED

val _ = export_theory ()
