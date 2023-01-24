open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory
open primitivesBaseTacLib

val _ = new_theory "primitivesArith"

(* TODO: we need a better library of lemmas about arithmetic *)

(* TODO: add those as rewriting theorems by default *)
val NOT_LE_EQ_GT = store_thm("NOT_LE_EQ_GT", “!(x y: int). ~(x <= y) <=> x > y”, COOPER_TAC)
val NOT_LT_EQ_GE = store_thm("NOT_LT_EQ_GE", “!(x y: int). ~(x < y) <=> x >= y”, COOPER_TAC)
val NOT_GE_EQ_LT = store_thm("NOT_GE_EQ_LT", “!(x y: int). ~(x >= y) <=> x < y”, COOPER_TAC)
val NOT_GT_EQ_LE = store_thm("NOT_GT_EQ_LE", “!(x y: int). ~(x > y) <=> x <= y”, COOPER_TAC)

val GE_EQ_LE = store_thm("GE_EQ_LE", “!(x y : int). x >= y <=> y <= x”, COOPER_TAC)
val LE_EQ_GE = store_thm("LE_EQ_GE", “!(x y : int). x <= y <=> y >= x”, COOPER_TAC)
val GT_EQ_LT = store_thm("GT_EQ_LT", “!(x y : int). x > y <=> y < x”, COOPER_TAC)
val LT_EQ_GT = store_thm("LT_EQ_GT", “!(x y : int). x < y <=> y > x”, COOPER_TAC)

Theorem INT_OF_NUM_INJ:
  !n m. &n = &m ==> n = m
Proof
  rpt strip_tac >>
  fs [Num]
QED

Theorem NUM_SUB_EQ:
  !(x y z : int). x = y - z ==> 0 <= x ==> 0 <= z ==> Num y = Num z + Num x
Proof
  rpt strip_tac >>
  sg ‘0 <= y’ >- COOPER_TAC >>
  rfs [] >>
  (* Convert to integers *)
  irule INT_OF_NUM_INJ >>
  imp_res_tac (GSYM INT_OF_NUM) >>
  (* Associativity of & *)
  PURE_REWRITE_TAC [GSYM INT_ADD] >>
  fs []
QED

Theorem NUM_SUB_1_EQ:
  !(x y : int). x = y - 1 ==> 0 <= x ==> Num y = SUC (Num x)
Proof
  rpt strip_tac >>
  (* Get rid of the SUC *)
  sg ‘SUC (Num x) = 1 + Num x’ >-(rw [ADD]) >> rw [] >>
  (* Massage a bit the goal *)
  qsuff_tac ‘Num y = Num (y − 1) + Num 1’ >- COOPER_TAC >>
  (* Apply the general theorem *)
  irule NUM_SUB_EQ >>
  COOPER_TAC
QED

Theorem POS_MUL_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 <= y ==> 0 <= x * y
Proof
  rpt strip_tac >>
  sg ‘0 <= &(Num x) * &(Num y)’ >- (rw [INT_MUL_CALCULATE] >> COOPER_TAC) >>
  sg ‘&(Num x) = x’ >- (irule EQ_SYM >> rw [INT_OF_NUM] >> COOPER_TAC) >>
  sg ‘&(Num y) = y’ >- (irule EQ_SYM >> rw [INT_OF_NUM] >> COOPER_TAC) >>
  metis_tac[]
QED

Theorem POS_DIV_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x / y
Proof
  rpt strip_tac >>
  rw [LE_EQ_GE] >>  
  sg ‘y <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\x. x >= 0’, ‘x’, ‘y’] ASSUME_TAC INT_DIV_FORALL_P >>
  fs [] >> POP_IGNORE_TAC >> rw [] >- COOPER_TAC >>
  fs [NOT_LT_EQ_GE] >>
  (* Proof by contradiction: assume k < 0 *)
  spose_not_then ASSUME_TAC >>
  fs [NOT_GE_EQ_LT] >>
  sg ‘k * y = (k + 1) * y + - y’ >- (fs [INT_RDISTRIB] >> COOPER_TAC) >>
  sg ‘0 <= (-(k + 1)) * y’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

Theorem POS_DIV_POS_LE:
  !(x y d : int). 0 <= x ==> 0 <= y ==> 0 < d ==> x <= y ==> x / d <= y / d
Proof
  rpt strip_tac >>
  sg ‘d <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\k. k = x / d’, ‘x’, ‘d’] ASSUME_TAC INT_DIV_P >>
  qspecl_then [‘\k. k = y / d’, ‘y’, ‘d’] ASSUME_TAC INT_DIV_P >>
  rfs [NOT_LT_EQ_GE] >> TRY COOPER_TAC >>
  sg ‘y = (x / d) * d + (r' + y - x)’ >- COOPER_TAC >>
  qspecl_then [‘(x / d) * d’, ‘r' + y - x’, ‘d’] ASSUME_TAC INT_ADD_DIV >>
  rfs [] >>
  Cases_on ‘x = y’ >- fs [] >>
  sg ‘r' + y ≠ x’ >- COOPER_TAC >> fs [] >>
  sg ‘((x / d) * d) / d = x / d’ >- (irule INT_DIV_RMUL >> COOPER_TAC) >>
  fs [] >>
  sg ‘0 <= (r' + y − x) / d’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  metis_tac [INT_LE_ADDR]
QED

Theorem POS_DIV_POS_LE_INIT:
  !(x y : int). 0 <= x ==> 0 < y ==> x / y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\k. k = x / y’, ‘x’, ‘y’] ASSUME_TAC INT_DIV_P >>
  rfs [NOT_LT_EQ_GE] >- COOPER_TAC >>
  sg ‘y = (y - 1) + 1’ >- rw [] >>
  sg ‘x = x / y + ((x / y) * (y - 1) + r)’ >-(
    qspecl_then [‘1’, ‘y-1’, ‘x / y’] ASSUME_TAC INT_LDISTRIB >>
    rfs [] >>
    COOPER_TAC
  ) >>
  sg ‘!a b c. 0 <= c ==> a = b + c ==> b <= a’ >- (COOPER_TAC) >>
  pop_assum irule >>
  exists_tac “x / y * (y − 1) + r” >>
  sg ‘0 <= x / y’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= (x / y) * (y - 1)’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

Theorem POS_MOD_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x % y
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- COOPER_TAC >> fs []
QED

Theorem POS_MOD_POS_LE_INIT:
  !(x y : int). 0 <= x ==> 0 < y ==> x % y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- COOPER_TAC >> fs [] >>
  sg ‘0 <= x % y’ >- (irule POS_MOD_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= x / y’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= (x / y) * y’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

val _ = export_theory ()
