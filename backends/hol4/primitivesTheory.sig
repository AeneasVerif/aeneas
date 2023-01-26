signature primitivesTheory =
sig
  type thm = Thm.thm
  
  (*  Axioms  *)
    val i128_to_int_bounds : thm
    val i128_to_int_int_to_i128 : thm
    val i16_to_int_bounds : thm
    val i16_to_int_int_to_i16 : thm
    val i32_to_int_bounds : thm
    val i32_to_int_int_to_i32 : thm
    val i64_to_int_bounds : thm
    val i64_to_int_int_to_i64 : thm
    val i8_to_int_bounds : thm
    val i8_to_int_int_to_i8 : thm
    val int_to_i128_i128_to_int : thm
    val int_to_i16_i16_to_int : thm
    val int_to_i32_i32_to_int : thm
    val int_to_i64_i64_to_int : thm
    val int_to_i8_i8_to_int : thm
    val int_to_isize_isize_to_int : thm
    val int_to_u128_u128_to_int : thm
    val int_to_u16_u16_to_int : thm
    val int_to_u32_u32_to_int : thm
    val int_to_u64_u64_to_int : thm
    val int_to_u8_u8_to_int : thm
    val int_to_usize_usize_to_int : thm
    val isize_bounds : thm
    val isize_to_int_bounds : thm
    val isize_to_int_int_to_isize : thm
    val mk_vec_spec : thm
    val u128_to_int_bounds : thm
    val u128_to_int_int_to_u128 : thm
    val u16_to_int_bounds : thm
    val u16_to_int_int_to_u16 : thm
    val u32_to_int_bounds : thm
    val u32_to_int_int_to_u32 : thm
    val u64_to_int_bounds : thm
    val u64_to_int_int_to_u64 : thm
    val u8_to_int_bounds : thm
    val u8_to_int_int_to_u8 : thm
    val usize_bounds : thm
    val usize_to_int_bounds : thm
    val usize_to_int_int_to_usize : thm
    val vec_to_list_num_bounds : thm
  
  (*  Definitions  *)
    val bind_def : thm
    val error_BIJ : thm
    val error_CASE : thm
    val error_TY_DEF : thm
    val error_size_def : thm
    val i128_add_def : thm
    val i128_div_def : thm
    val i128_max_def : thm
    val i128_min_def : thm
    val i128_mul_def : thm
    val i128_rem_def : thm
    val i128_sub_def : thm
    val i16_add_def : thm
    val i16_div_def : thm
    val i16_max_def : thm
    val i16_min_def : thm
    val i16_mul_def : thm
    val i16_rem_def : thm
    val i16_sub_def : thm
    val i32_add_def : thm
    val i32_div_def : thm
    val i32_max_def : thm
    val i32_min_def : thm
    val i32_mul_def : thm
    val i32_rem_def : thm
    val i32_sub_def : thm
    val i64_add_def : thm
    val i64_div_def : thm
    val i64_max_def : thm
    val i64_min_def : thm
    val i64_mul_def : thm
    val i64_rem_def : thm
    val i64_sub_def : thm
    val i8_add_def : thm
    val i8_div_def : thm
    val i8_max_def : thm
    val i8_min_def : thm
    val i8_mul_def : thm
    val i8_rem_def : thm
    val i8_sub_def : thm
    val index_def : thm
    val int_rem_def : thm
    val isize_add_def : thm
    val isize_div_def : thm
    val isize_mul_def : thm
    val isize_rem_def : thm
    val isize_sub_def : thm
    val len_def : thm
    val massert_def : thm
    val mem_replace_back_def : thm
    val mem_replace_fwd_def : thm
    val mk_i128_def : thm
    val mk_i16_def : thm
    val mk_i32_def : thm
    val mk_i64_def : thm
    val mk_i8_def : thm
    val mk_isize_def : thm
    val mk_u128_def : thm
    val mk_u16_def : thm
    val mk_u32_def : thm
    val mk_u64_def : thm
    val mk_u8_def : thm
    val mk_usize_def : thm
    val result_TY_DEF : thm
    val result_case_def : thm
    val result_size_def : thm
    val return_def : thm
    val u128_add_def : thm
    val u128_div_def : thm
    val u128_max_def : thm
    val u128_mul_def : thm
    val u128_rem_def : thm
    val u128_sub_def : thm
    val u16_add_def : thm
    val u16_div_def : thm
    val u16_max_def : thm
    val u16_mul_def : thm
    val u16_rem_def : thm
    val u16_sub_def : thm
    val u32_add_def : thm
    val u32_div_def : thm
    val u32_max_def : thm
    val u32_mul_def : thm
    val u32_rem_def : thm
    val u32_sub_def : thm
    val u64_add_def : thm
    val u64_div_def : thm
    val u64_max_def : thm
    val u64_mul_def : thm
    val u64_rem_def : thm
    val u64_sub_def : thm
    val u8_add_def : thm
    val u8_div_def : thm
    val u8_max_def : thm
    val u8_mul_def : thm
    val u8_rem_def : thm
    val u8_sub_def : thm
    val update_def : thm
    val usize_add_def : thm
    val usize_div_def : thm
    val usize_mul_def : thm
    val usize_rem_def : thm
    val usize_sub_def : thm
    val vec_index_def : thm
    val vec_insert_back_def : thm
    val vec_len_def : thm
    val vec_new_def : thm
    val vec_push_back_def : thm
  
  (*  Theorems  *)
    val datatype_error : thm
    val datatype_result : thm
    val error2num_11 : thm
    val error2num_ONTO : thm
    val error2num_num2error : thm
    val error2num_thm : thm
    val error_Axiom : thm
    val error_EQ_error : thm
    val error_case_cong : thm
    val error_case_def : thm
    val error_case_eq : thm
    val error_induction : thm
    val error_nchotomy : thm
    val i128_add_eq : thm
    val i128_div_eq : thm
    val i128_mul_eq : thm
    val i128_rem_eq : thm
    val i128_sub_eq : thm
    val i16_add_eq : thm
    val i16_div_eq : thm
    val i16_mul_eq : thm
    val i16_rem_eq : thm
    val i16_sub_eq : thm
    val i32_add_eq : thm
    val i32_div_eq : thm
    val i32_mul_eq : thm
    val i32_rem_eq : thm
    val i32_sub_eq : thm
    val i64_add_eq : thm
    val i64_div_eq : thm
    val i64_mul_eq : thm
    val i64_rem_eq : thm
    val i64_sub_eq : thm
    val i8_add_eq : thm
    val i8_div_eq : thm
    val i8_mul_eq : thm
    val i8_rem_eq : thm
    val i8_sub_eq : thm
    val index_update_diff : thm
    val index_update_same : thm
    val int_of_num_neq_inj : thm
    val isize_add_eq : thm
    val isize_div_eq : thm
    val isize_mul_eq : thm
    val isize_rem_eq : thm
    val isize_sub_eq : thm
    val num2error_11 : thm
    val num2error_ONTO : thm
    val num2error_error2num : thm
    val num2error_thm : thm
    val result_11 : thm
    val result_Axiom : thm
    val result_case_cong : thm
    val result_case_eq : thm
    val result_distinct : thm
    val result_induction : thm
    val result_nchotomy : thm
    val u128_add_eq : thm
    val u128_div_eq : thm
    val u128_mul_eq : thm
    val u128_rem_eq : thm
    val u128_sub_eq : thm
    val u16_add_eq : thm
    val u16_div_eq : thm
    val u16_mul_eq : thm
    val u16_rem_eq : thm
    val u16_sub_eq : thm
    val u32_add_eq : thm
    val u32_div_eq : thm
    val u32_mul_eq : thm
    val u32_rem_eq : thm
    val u32_sub_eq : thm
    val u64_add_eq : thm
    val u64_div_eq : thm
    val u64_mul_eq : thm
    val u64_rem_eq : thm
    val u64_sub_eq : thm
    val u8_add_eq : thm
    val u8_div_eq : thm
    val u8_mul_eq : thm
    val u8_rem_eq : thm
    val u8_sub_eq : thm
    val update_ind : thm
    val update_len : thm
    val update_spec : thm
    val usize_add_eq : thm
    val usize_div_eq : thm
    val usize_mul_eq : thm
    val usize_rem_eq : thm
    val usize_sub_eq : thm
    val vec_insert_back_spec : thm
    val vec_len_spec : thm
    val vec_to_list_int_bounds : thm
  
  val primitives_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitivesArith] Parent theory of "primitives"
   
   [string] Parent theory of "primitives"
   
   [mk_vec_spec]  Axiom
      
      [oracles: ] [axioms: mk_vec_spec] []
      ⊢ ∀l. len l ≤ usize_max ⇒ ∃v. mk_vec l = Return v ∧ vec_to_list v = l
   
   [vec_to_list_num_bounds]  Axiom
      
      [oracles: ] [axioms: vec_to_list_num_bounds] []
      ⊢ ∀v. (let l = LENGTH (vec_to_list v) in 0 ≤ l ∧ l ≤ Num usize_max)
   
   [int_to_usize_usize_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_usize_usize_to_int] []
      ⊢ ∀i. int_to_usize (usize_to_int i) = i
   
   [int_to_u128_u128_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u128_u128_to_int] []
      ⊢ ∀i. int_to_u128 (u128_to_int i) = i
   
   [int_to_u64_u64_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u64_u64_to_int] []
      ⊢ ∀i. int_to_u64 (u64_to_int i) = i
   
   [int_to_u32_u32_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u32_u32_to_int] []
      ⊢ ∀i. int_to_u32 (u32_to_int i) = i
   
   [int_to_u16_u16_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u16_u16_to_int] []
      ⊢ ∀i. int_to_u16 (u16_to_int i) = i
   
   [int_to_u8_u8_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u8_u8_to_int] []
      ⊢ ∀i. int_to_u8 (u8_to_int i) = i
   
   [int_to_isize_isize_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_isize_isize_to_int] []
      ⊢ ∀i. int_to_isize (isize_to_int i) = i
   
   [int_to_i128_i128_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i128_i128_to_int] []
      ⊢ ∀i. int_to_i128 (i128_to_int i) = i
   
   [int_to_i64_i64_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i64_i64_to_int] []
      ⊢ ∀i. int_to_i64 (i64_to_int i) = i
   
   [int_to_i32_i32_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i32_i32_to_int] []
      ⊢ ∀i. int_to_i32 (i32_to_int i) = i
   
   [int_to_i16_i16_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i16_i16_to_int] []
      ⊢ ∀i. int_to_i16 (i16_to_int i) = i
   
   [int_to_i8_i8_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i8_i8_to_int] []
      ⊢ ∀i. int_to_i8 (i8_to_int i) = i
   
   [u128_to_int_int_to_u128]  Axiom
      
      [oracles: ] [axioms: u128_to_int_int_to_u128] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u128_max ⇒ u128_to_int (int_to_u128 n) = n
   
   [u64_to_int_int_to_u64]  Axiom
      
      [oracles: ] [axioms: u64_to_int_int_to_u64] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u64_max ⇒ u64_to_int (int_to_u64 n) = n
   
   [u32_to_int_int_to_u32]  Axiom
      
      [oracles: ] [axioms: u32_to_int_int_to_u32] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u32_max ⇒ u32_to_int (int_to_u32 n) = n
   
   [u16_to_int_int_to_u16]  Axiom
      
      [oracles: ] [axioms: u16_to_int_int_to_u16] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u16_max ⇒ u16_to_int (int_to_u16 n) = n
   
   [u8_to_int_int_to_u8]  Axiom
      
      [oracles: ] [axioms: u8_to_int_int_to_u8] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u8_max ⇒ u8_to_int (int_to_u8 n) = n
   
   [usize_to_int_int_to_usize]  Axiom
      
      [oracles: ] [axioms: usize_to_int_int_to_usize] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ usize_max ⇒ usize_to_int (int_to_usize n) = n
   
   [i128_to_int_int_to_i128]  Axiom
      
      [oracles: ] [axioms: i128_to_int_int_to_i128] []
      ⊢ ∀n. i128_min ≤ n ∧ n ≤ i128_max ⇒ i128_to_int (int_to_i128 n) = n
   
   [i64_to_int_int_to_i64]  Axiom
      
      [oracles: ] [axioms: i64_to_int_int_to_i64] []
      ⊢ ∀n. i64_min ≤ n ∧ n ≤ i64_max ⇒ i64_to_int (int_to_i64 n) = n
   
   [i32_to_int_int_to_i32]  Axiom
      
      [oracles: ] [axioms: i32_to_int_int_to_i32] []
      ⊢ ∀n. i32_min ≤ n ∧ n ≤ i32_max ⇒ i32_to_int (int_to_i32 n) = n
   
   [i16_to_int_int_to_i16]  Axiom
      
      [oracles: ] [axioms: i16_to_int_int_to_i16] []
      ⊢ ∀n. i16_min ≤ n ∧ n ≤ i16_max ⇒ i16_to_int (int_to_i16 n) = n
   
   [i8_to_int_int_to_i8]  Axiom
      
      [oracles: ] [axioms: i8_to_int_int_to_i8] []
      ⊢ ∀n. i8_min ≤ n ∧ n ≤ i8_max ⇒ i8_to_int (int_to_i8 n) = n
   
   [isize_to_int_int_to_isize]  Axiom
      
      [oracles: ] [axioms: isize_to_int_int_to_isize] []
      ⊢ ∀n. isize_min ≤ n ∧ n ≤ isize_max ⇒
            isize_to_int (int_to_isize n) = n
   
   [u128_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u128_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u128_to_int n ∧ u128_to_int n ≤ u128_max
   
   [u64_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u64_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u64_to_int n ∧ u64_to_int n ≤ u64_max
   
   [u32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u32_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u32_to_int n ∧ u32_to_int n ≤ u32_max
   
   [u16_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u16_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u16_to_int n ∧ u16_to_int n ≤ u16_max
   
   [u8_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u8_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u8_to_int n ∧ u8_to_int n ≤ u8_max
   
   [usize_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: usize_to_int_bounds] []
      ⊢ ∀n. 0 ≤ usize_to_int n ∧ usize_to_int n ≤ usize_max
   
   [i128_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i128_to_int_bounds] []
      ⊢ ∀n. i128_min ≤ i128_to_int n ∧ i128_to_int n ≤ i128_max
   
   [i64_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i64_to_int_bounds] []
      ⊢ ∀n. i64_min ≤ i64_to_int n ∧ i64_to_int n ≤ i64_max
   
   [i32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i32_to_int_bounds] []
      ⊢ ∀n. i32_min ≤ i32_to_int n ∧ i32_to_int n ≤ i32_max
   
   [i16_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i16_to_int_bounds] []
      ⊢ ∀n. i16_min ≤ i16_to_int n ∧ i16_to_int n ≤ i16_max
   
   [i8_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i8_to_int_bounds] []
      ⊢ ∀n. i8_min ≤ i8_to_int n ∧ i8_to_int n ≤ i8_max
   
   [isize_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: isize_to_int_bounds] []
      ⊢ ∀n. isize_min ≤ isize_to_int n ∧ isize_to_int n ≤ isize_max
   
   [usize_bounds]  Axiom
      
      [oracles: ] [axioms: usize_bounds] [] ⊢ usize_max ≥ u16_max
   
   [isize_bounds]  Axiom
      
      [oracles: ] [axioms: isize_bounds] []
      ⊢ isize_min ≤ i16_min ∧ isize_max ≥ i16_max
   
   [bind_def]  Definition
      
      ⊢ ∀x f.
          monad_bind x f =
          case x of Return y => f y | Fail e => Fail e | Loop => Loop
   
   [error_BIJ]  Definition
      
      ⊢ (∀a. num2error (error2num a) = a) ∧
        ∀r. (λn. n < 1) r ⇔ error2num (num2error r) = r
   
   [error_CASE]  Definition
      
      ⊢ ∀x v0. (case x of Failure => v0) = (λm. v0) (error2num x)
   
   [error_TY_DEF]  Definition
      
      ⊢ ∃rep. TYPE_DEFINITION (λn. n < 1) rep
   
   [error_size_def]  Definition
      
      ⊢ ∀x. error_size x = 0
   
   [i128_add_def]  Definition
      
      ⊢ ∀x y. i128_add x y = mk_i128 (i128_to_int x + i128_to_int y)
   
   [i128_div_def]  Definition
      
      ⊢ ∀x y.
          i128_div x y =
          if i128_to_int y = 0 then Fail Failure
          else mk_i128 (i128_to_int x / i128_to_int y)
   
   [i128_max_def]  Definition
      
      ⊢ i128_max = 170141183460469231731687303715884105727
   
   [i128_min_def]  Definition
      
      ⊢ i128_min = -170141183460469231731687303715884105728
   
   [i128_mul_def]  Definition
      
      ⊢ ∀x y. i128_mul x y = mk_i128 (i128_to_int x * i128_to_int y)
   
   [i128_rem_def]  Definition
      
      ⊢ ∀x y.
          i128_rem x y =
          if i128_to_int y = 0 then Fail Failure
          else mk_i128 (int_rem (i128_to_int x) (i128_to_int y))
   
   [i128_sub_def]  Definition
      
      ⊢ ∀x y. i128_sub x y = mk_i128 (i128_to_int x − i128_to_int y)
   
   [i16_add_def]  Definition
      
      ⊢ ∀x y. i16_add x y = mk_i16 (i16_to_int x + i16_to_int y)
   
   [i16_div_def]  Definition
      
      ⊢ ∀x y.
          i16_div x y =
          if i16_to_int y = 0 then Fail Failure
          else mk_i16 (i16_to_int x / i16_to_int y)
   
   [i16_max_def]  Definition
      
      ⊢ i16_max = 32767
   
   [i16_min_def]  Definition
      
      ⊢ i16_min = -32768
   
   [i16_mul_def]  Definition
      
      ⊢ ∀x y. i16_mul x y = mk_i16 (i16_to_int x * i16_to_int y)
   
   [i16_rem_def]  Definition
      
      ⊢ ∀x y.
          i16_rem x y =
          if i16_to_int y = 0 then Fail Failure
          else mk_i16 (int_rem (i16_to_int x) (i16_to_int y))
   
   [i16_sub_def]  Definition
      
      ⊢ ∀x y. i16_sub x y = mk_i16 (i16_to_int x − i16_to_int y)
   
   [i32_add_def]  Definition
      
      ⊢ ∀x y. i32_add x y = mk_i32 (i32_to_int x + i32_to_int y)
   
   [i32_div_def]  Definition
      
      ⊢ ∀x y.
          i32_div x y =
          if i32_to_int y = 0 then Fail Failure
          else mk_i32 (i32_to_int x / i32_to_int y)
   
   [i32_max_def]  Definition
      
      ⊢ i32_max = 2147483647
   
   [i32_min_def]  Definition
      
      ⊢ i32_min = -2147483648
   
   [i32_mul_def]  Definition
      
      ⊢ ∀x y. i32_mul x y = mk_i32 (i32_to_int x * i32_to_int y)
   
   [i32_rem_def]  Definition
      
      ⊢ ∀x y.
          i32_rem x y =
          if i32_to_int y = 0 then Fail Failure
          else mk_i32 (int_rem (i32_to_int x) (i32_to_int y))
   
   [i32_sub_def]  Definition
      
      ⊢ ∀x y. i32_sub x y = mk_i32 (i32_to_int x − i32_to_int y)
   
   [i64_add_def]  Definition
      
      ⊢ ∀x y. i64_add x y = mk_i64 (i64_to_int x + i64_to_int y)
   
   [i64_div_def]  Definition
      
      ⊢ ∀x y.
          i64_div x y =
          if i64_to_int y = 0 then Fail Failure
          else mk_i64 (i64_to_int x / i64_to_int y)
   
   [i64_max_def]  Definition
      
      ⊢ i64_max = 9223372036854775807
   
   [i64_min_def]  Definition
      
      ⊢ i64_min = -9223372036854775808
   
   [i64_mul_def]  Definition
      
      ⊢ ∀x y. i64_mul x y = mk_i64 (i64_to_int x * i64_to_int y)
   
   [i64_rem_def]  Definition
      
      ⊢ ∀x y.
          i64_rem x y =
          if i64_to_int y = 0 then Fail Failure
          else mk_i64 (int_rem (i64_to_int x) (i64_to_int y))
   
   [i64_sub_def]  Definition
      
      ⊢ ∀x y. i64_sub x y = mk_i64 (i64_to_int x − i64_to_int y)
   
   [i8_add_def]  Definition
      
      ⊢ ∀x y. i8_add x y = mk_i8 (i8_to_int x + i8_to_int y)
   
   [i8_div_def]  Definition
      
      ⊢ ∀x y.
          i8_div x y =
          if i8_to_int y = 0 then Fail Failure
          else mk_i8 (i8_to_int x / i8_to_int y)
   
   [i8_max_def]  Definition
      
      ⊢ i8_max = 127
   
   [i8_min_def]  Definition
      
      ⊢ i8_min = -128
   
   [i8_mul_def]  Definition
      
      ⊢ ∀x y. i8_mul x y = mk_i8 (i8_to_int x * i8_to_int y)
   
   [i8_rem_def]  Definition
      
      ⊢ ∀x y.
          i8_rem x y =
          if i8_to_int y = 0 then Fail Failure
          else mk_i8 (int_rem (i8_to_int x) (i8_to_int y))
   
   [i8_sub_def]  Definition
      
      ⊢ ∀x y. i8_sub x y = mk_i8 (i8_to_int x − i8_to_int y)
   
   [index_def]  Definition
      
      ⊢ ∀i x ls.
          index i (x::ls) =
          if i = 0 then x else if 0 < i then index (i − 1) ls else ARB
   
   [int_rem_def]  Definition
      
      ⊢ ∀x y.
          int_rem x y =
          if x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0 then x % y else -(x % y)
   
   [isize_add_def]  Definition
      
      ⊢ ∀x y. isize_add x y = mk_isize (isize_to_int x + isize_to_int y)
   
   [isize_div_def]  Definition
      
      ⊢ ∀x y.
          isize_div x y =
          if isize_to_int y = 0 then Fail Failure
          else mk_isize (isize_to_int x / isize_to_int y)
   
   [isize_mul_def]  Definition
      
      ⊢ ∀x y. isize_mul x y = mk_isize (isize_to_int x * isize_to_int y)
   
   [isize_rem_def]  Definition
      
      ⊢ ∀x y.
          isize_rem x y =
          if isize_to_int y = 0 then Fail Failure
          else mk_isize (int_rem (isize_to_int x) (isize_to_int y))
   
   [isize_sub_def]  Definition
      
      ⊢ ∀x y. isize_sub x y = mk_isize (isize_to_int x − isize_to_int y)
   
   [len_def]  Definition
      
      ⊢ len [] = 0 ∧ ∀x ls. len (x::ls) = 1 + len ls
   
   [massert_def]  Definition
      
      ⊢ ∀b. massert b = if b then Return () else Fail Failure
   
   [mem_replace_back_def]  Definition
      
      ⊢ ∀x y. mem_replace_back x y = y
   
   [mem_replace_fwd_def]  Definition
      
      ⊢ ∀x y. mem_replace_fwd x y = x
   
   [mk_i128_def]  Definition
      
      ⊢ ∀n. mk_i128 n =
            if i128_min ≤ n ∧ n ≤ i128_max then Return (int_to_i128 n)
            else Fail Failure
   
   [mk_i16_def]  Definition
      
      ⊢ ∀n. mk_i16 n =
            if i16_min ≤ n ∧ n ≤ i16_max then Return (int_to_i16 n)
            else Fail Failure
   
   [mk_i32_def]  Definition
      
      ⊢ ∀n. mk_i32 n =
            if i32_min ≤ n ∧ n ≤ i32_max then Return (int_to_i32 n)
            else Fail Failure
   
   [mk_i64_def]  Definition
      
      ⊢ ∀n. mk_i64 n =
            if i64_min ≤ n ∧ n ≤ i64_max then Return (int_to_i64 n)
            else Fail Failure
   
   [mk_i8_def]  Definition
      
      ⊢ ∀n. mk_i8 n =
            if i8_min ≤ n ∧ n ≤ i8_max then Return (int_to_i8 n)
            else Fail Failure
   
   [mk_isize_def]  Definition
      
      ⊢ ∀n. mk_isize n =
            if isize_min ≤ n ∧ n ≤ isize_max then Return (int_to_isize n)
            else Fail Failure
   
   [mk_u128_def]  Definition
      
      ⊢ ∀n. mk_u128 n =
            if 0 ≤ n ∧ n ≤ u128_max then Return (int_to_u128 n)
            else Fail Failure
   
   [mk_u16_def]  Definition
      
      ⊢ ∀n. mk_u16 n =
            if 0 ≤ n ∧ n ≤ u16_max then Return (int_to_u16 n)
            else Fail Failure
   
   [mk_u32_def]  Definition
      
      ⊢ ∀n. mk_u32 n =
            if 0 ≤ n ∧ n ≤ u32_max then Return (int_to_u32 n)
            else Fail Failure
   
   [mk_u64_def]  Definition
      
      ⊢ ∀n. mk_u64 n =
            if 0 ≤ n ∧ n ≤ u64_max then Return (int_to_u64 n)
            else Fail Failure
   
   [mk_u8_def]  Definition
      
      ⊢ ∀n. mk_u8 n =
            if 0 ≤ n ∧ n ≤ u8_max then Return (int_to_u8 n)
            else Fail Failure
   
   [mk_usize_def]  Definition
      
      ⊢ ∀n. mk_usize n =
            if 0 ≤ n ∧ n ≤ usize_max then Return (int_to_usize n)
            else Fail Failure
   
   [result_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('result').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      a0 =
                      ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('result') a0) ⇒
                   $var$('result') a0) rep
   
   [result_case_def]  Definition
      
      ⊢ (∀a f f1 v. result_CASE (Return a) f f1 v = f a) ∧
        (∀a f f1 v. result_CASE (Fail a) f f1 v = f1 a) ∧
        ∀f f1 v. result_CASE Loop f f1 v = v
   
   [result_size_def]  Definition
      
      ⊢ (∀f a. result_size f (Return a) = 1 + f a) ∧
        (∀f a. result_size f (Fail a) = 1 + error_size a) ∧
        ∀f. result_size f Loop = 0
   
   [return_def]  Definition
      
      ⊢ ∀x. return x = Return x
   
   [u128_add_def]  Definition
      
      ⊢ ∀x y. u128_add x y = mk_u128 (u128_to_int x + u128_to_int y)
   
   [u128_div_def]  Definition
      
      ⊢ ∀x y.
          u128_div x y =
          if u128_to_int y = 0 then Fail Failure
          else mk_u128 (u128_to_int x / u128_to_int y)
   
   [u128_max_def]  Definition
      
      ⊢ u128_max = 340282366920938463463374607431768211455
   
   [u128_mul_def]  Definition
      
      ⊢ ∀x y. u128_mul x y = mk_u128 (u128_to_int x * u128_to_int y)
   
   [u128_rem_def]  Definition
      
      ⊢ ∀x y.
          u128_rem x y =
          if u128_to_int y = 0 then Fail Failure
          else mk_u128 (int_rem (u128_to_int x) (u128_to_int y))
   
   [u128_sub_def]  Definition
      
      ⊢ ∀x y. u128_sub x y = mk_u128 (u128_to_int x − u128_to_int y)
   
   [u16_add_def]  Definition
      
      ⊢ ∀x y. u16_add x y = mk_u16 (u16_to_int x + u16_to_int y)
   
   [u16_div_def]  Definition
      
      ⊢ ∀x y.
          u16_div x y =
          if u16_to_int y = 0 then Fail Failure
          else mk_u16 (u16_to_int x / u16_to_int y)
   
   [u16_max_def]  Definition
      
      ⊢ u16_max = 65535
   
   [u16_mul_def]  Definition
      
      ⊢ ∀x y. u16_mul x y = mk_u16 (u16_to_int x * u16_to_int y)
   
   [u16_rem_def]  Definition
      
      ⊢ ∀x y.
          u16_rem x y =
          if u16_to_int y = 0 then Fail Failure
          else mk_u16 (int_rem (u16_to_int x) (u16_to_int y))
   
   [u16_sub_def]  Definition
      
      ⊢ ∀x y. u16_sub x y = mk_u16 (u16_to_int x − u16_to_int y)
   
   [u32_add_def]  Definition
      
      ⊢ ∀x y. u32_add x y = mk_u32 (u32_to_int x + u32_to_int y)
   
   [u32_div_def]  Definition
      
      ⊢ ∀x y.
          u32_div x y =
          if u32_to_int y = 0 then Fail Failure
          else mk_u32 (u32_to_int x / u32_to_int y)
   
   [u32_max_def]  Definition
      
      ⊢ u32_max = 4294967295
   
   [u32_mul_def]  Definition
      
      ⊢ ∀x y. u32_mul x y = mk_u32 (u32_to_int x * u32_to_int y)
   
   [u32_rem_def]  Definition
      
      ⊢ ∀x y.
          u32_rem x y =
          if u32_to_int y = 0 then Fail Failure
          else mk_u32 (int_rem (u32_to_int x) (u32_to_int y))
   
   [u32_sub_def]  Definition
      
      ⊢ ∀x y. u32_sub x y = mk_u32 (u32_to_int x − u32_to_int y)
   
   [u64_add_def]  Definition
      
      ⊢ ∀x y. u64_add x y = mk_u64 (u64_to_int x + u64_to_int y)
   
   [u64_div_def]  Definition
      
      ⊢ ∀x y.
          u64_div x y =
          if u64_to_int y = 0 then Fail Failure
          else mk_u64 (u64_to_int x / u64_to_int y)
   
   [u64_max_def]  Definition
      
      ⊢ u64_max = 18446744073709551615
   
   [u64_mul_def]  Definition
      
      ⊢ ∀x y. u64_mul x y = mk_u64 (u64_to_int x * u64_to_int y)
   
   [u64_rem_def]  Definition
      
      ⊢ ∀x y.
          u64_rem x y =
          if u64_to_int y = 0 then Fail Failure
          else mk_u64 (int_rem (u64_to_int x) (u64_to_int y))
   
   [u64_sub_def]  Definition
      
      ⊢ ∀x y. u64_sub x y = mk_u64 (u64_to_int x − u64_to_int y)
   
   [u8_add_def]  Definition
      
      ⊢ ∀x y. u8_add x y = mk_u8 (u8_to_int x + u8_to_int y)
   
   [u8_div_def]  Definition
      
      ⊢ ∀x y.
          u8_div x y =
          if u8_to_int y = 0 then Fail Failure
          else mk_u8 (u8_to_int x / u8_to_int y)
   
   [u8_max_def]  Definition
      
      ⊢ u8_max = 255
   
   [u8_mul_def]  Definition
      
      ⊢ ∀x y. u8_mul x y = mk_u8 (u8_to_int x * u8_to_int y)
   
   [u8_rem_def]  Definition
      
      ⊢ ∀x y.
          u8_rem x y =
          if u8_to_int y = 0 then Fail Failure
          else mk_u8 (int_rem (u8_to_int x) (u8_to_int y))
   
   [u8_sub_def]  Definition
      
      ⊢ ∀x y. u8_sub x y = mk_u8 (u8_to_int x − u8_to_int y)
   
   [update_def]  Definition
      
      ⊢ (∀i y. update [] i y = []) ∧
        ∀x ls i y.
          update (x::ls) i y =
          if i = 0 then y::ls
          else if 0 < i then x::update ls (i − 1) y
          else x::ls
   
   [usize_add_def]  Definition
      
      ⊢ ∀x y. usize_add x y = mk_usize (usize_to_int x + usize_to_int y)
   
   [usize_div_def]  Definition
      
      ⊢ ∀x y.
          usize_div x y =
          if usize_to_int y = 0 then Fail Failure
          else mk_usize (usize_to_int x / usize_to_int y)
   
   [usize_mul_def]  Definition
      
      ⊢ ∀x y. usize_mul x y = mk_usize (usize_to_int x * usize_to_int y)
   
   [usize_rem_def]  Definition
      
      ⊢ ∀x y.
          usize_rem x y =
          if usize_to_int y = 0 then Fail Failure
          else mk_usize (int_rem (usize_to_int x) (usize_to_int y))
   
   [usize_sub_def]  Definition
      
      ⊢ ∀x y. usize_sub x y = mk_usize (usize_to_int x − usize_to_int y)
   
   [vec_index_def]  Definition
      
      ⊢ ∀i v.
          vec_index i v =
          if usize_to_int i ≤ usize_to_int (vec_len v) then
            Return (index (usize_to_int i) (vec_to_list v))
          else Fail Failure
   
   [vec_insert_back_def]  Definition
      
      ⊢ ∀v i x.
          vec_insert_back v i x =
          mk_vec (update (vec_to_list v) (usize_to_int i) x)
   
   [vec_len_def]  Definition
      
      ⊢ ∀v. vec_len v = int_to_usize (len (vec_to_list v))
   
   [vec_new_def]  Definition
      
      ⊢ vec_new =
        case mk_vec [] of Return v => v | Fail v2 => ARB | Loop => ARB
   
   [vec_push_back_def]  Definition
      
      ⊢ ∀v x. vec_push_back v x = mk_vec (vec_to_list v ⧺ [x])
   
   [datatype_error]  Theorem
      
      ⊢ DATATYPE (error Failure)
   
   [datatype_result]  Theorem
      
      ⊢ DATATYPE (result Return Fail Loop)
   
   [error2num_11]  Theorem
      
      ⊢ ∀a a'. error2num a = error2num a' ⇔ a = a'
   
   [error2num_ONTO]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ ∃a. r = error2num a
   
   [error2num_num2error]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ error2num (num2error r) = r
   
   [error2num_thm]  Theorem
      
      ⊢ error2num Failure = 0
   
   [error_Axiom]  Theorem
      
      ⊢ ∀x0. ∃f. f Failure = x0
   
   [error_EQ_error]  Theorem
      
      ⊢ ∀a a'. a = a' ⇔ error2num a = error2num a'
   
   [error_case_cong]  Theorem
      
      ⊢ ∀M M' v0.
          M = M' ∧ (M' = Failure ⇒ v0 = v0') ⇒
          (case M of Failure => v0) = case M' of Failure => v0'
   
   [error_case_def]  Theorem
      
      ⊢ ∀v0. (case Failure of Failure => v0) = v0
   
   [error_case_eq]  Theorem
      
      ⊢ (case x of Failure => v0) = v ⇔ x = Failure ∧ v0 = v
   
   [error_induction]  Theorem
      
      ⊢ ∀P. P Failure ⇒ ∀a. P a
   
   [error_nchotomy]  Theorem
      
      ⊢ ∀a. a = Failure
   
   [i128_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, usize_bounds] []
      ⊢ ∀x y.
          i128_min ≤ i128_to_int x + i128_to_int y ⇒
          i128_to_int x + i128_to_int y ≤ i128_max ⇒
          ∃z. i128_add x y = Return z ∧
              i128_to_int z = i128_to_int x + i128_to_int y
   
   [i128_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, usize_bounds] []
      ⊢ ∀x y.
          i128_to_int y ≠ 0 ⇒
          i128_min ≤ i128_to_int x / i128_to_int y ⇒
          i128_to_int x / i128_to_int y ≤ i128_max ⇒
          ∃z. i128_div x y = Return z ∧
              i128_to_int z = i128_to_int x / i128_to_int y
   
   [i128_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, usize_bounds] []
      ⊢ ∀x y.
          i128_min ≤ i128_to_int x * i128_to_int y ⇒
          i128_to_int x * i128_to_int y ≤ i128_max ⇒
          ∃z. i128_mul x y = Return z ∧
              i128_to_int z = i128_to_int x * i128_to_int y
   
   [i128_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, i128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          i128_to_int y ≠ 0 ⇒
          i128_min ≤ int_rem (i128_to_int x) (i128_to_int y) ⇒
          int_rem (i128_to_int x) (i128_to_int y) ≤ i128_max ⇒
          ∃z. i128_rem x y = Return z ∧
              i128_to_int z = int_rem (i128_to_int x) (i128_to_int y)
   
   [i128_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, usize_bounds] []
      ⊢ ∀x y.
          i128_min ≤ i128_to_int x − i128_to_int y ⇒
          i128_to_int x − i128_to_int y ≤ i128_max ⇒
          ∃z. i128_sub x y = Return z ∧
              i128_to_int z = i128_to_int x − i128_to_int y
   
   [i16_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ i16_to_int x + i16_to_int y ⇒
          i16_to_int x + i16_to_int y ≤ i16_max ⇒
          ∃z. i16_add x y = Return z ∧
              i16_to_int z = i16_to_int x + i16_to_int y
   
   [i16_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, usize_bounds] []
      ⊢ ∀x y.
          i16_to_int y ≠ 0 ⇒
          i16_min ≤ i16_to_int x / i16_to_int y ⇒
          i16_to_int x / i16_to_int y ≤ i16_max ⇒
          ∃z. i16_div x y = Return z ∧
              i16_to_int z = i16_to_int x / i16_to_int y
   
   [i16_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ i16_to_int x * i16_to_int y ⇒
          i16_to_int x * i16_to_int y ≤ i16_max ⇒
          ∃z. i16_mul x y = Return z ∧
              i16_to_int z = i16_to_int x * i16_to_int y
   
   [i16_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, i16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          i16_to_int y ≠ 0 ⇒
          i16_min ≤ int_rem (i16_to_int x) (i16_to_int y) ⇒
          int_rem (i16_to_int x) (i16_to_int y) ≤ i16_max ⇒
          ∃z. i16_rem x y = Return z ∧
              i16_to_int z = int_rem (i16_to_int x) (i16_to_int y)
   
   [i16_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ i16_to_int x − i16_to_int y ⇒
          i16_to_int x − i16_to_int y ≤ i16_max ⇒
          ∃z. i16_sub x y = Return z ∧
              i16_to_int z = i16_to_int x − i16_to_int y
   
   [i32_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, usize_bounds] []
      ⊢ ∀x y.
          i32_min ≤ i32_to_int x + i32_to_int y ⇒
          i32_to_int x + i32_to_int y ≤ i32_max ⇒
          ∃z. i32_add x y = Return z ∧
              i32_to_int z = i32_to_int x + i32_to_int y
   
   [i32_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, usize_bounds] []
      ⊢ ∀x y.
          i32_to_int y ≠ 0 ⇒
          i32_min ≤ i32_to_int x / i32_to_int y ⇒
          i32_to_int x / i32_to_int y ≤ i32_max ⇒
          ∃z. i32_div x y = Return z ∧
              i32_to_int z = i32_to_int x / i32_to_int y
   
   [i32_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, usize_bounds] []
      ⊢ ∀x y.
          i32_min ≤ i32_to_int x * i32_to_int y ⇒
          i32_to_int x * i32_to_int y ≤ i32_max ⇒
          ∃z. i32_mul x y = Return z ∧
              i32_to_int z = i32_to_int x * i32_to_int y
   
   [i32_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, i32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          i32_to_int y ≠ 0 ⇒
          i32_min ≤ int_rem (i32_to_int x) (i32_to_int y) ⇒
          int_rem (i32_to_int x) (i32_to_int y) ≤ i32_max ⇒
          ∃z. i32_rem x y = Return z ∧
              i32_to_int z = int_rem (i32_to_int x) (i32_to_int y)
   
   [i32_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, usize_bounds] []
      ⊢ ∀x y.
          i32_min ≤ i32_to_int x − i32_to_int y ⇒
          i32_to_int x − i32_to_int y ≤ i32_max ⇒
          ∃z. i32_sub x y = Return z ∧
              i32_to_int z = i32_to_int x − i32_to_int y
   
   [i64_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, usize_bounds] []
      ⊢ ∀x y.
          i64_min ≤ i64_to_int x + i64_to_int y ⇒
          i64_to_int x + i64_to_int y ≤ i64_max ⇒
          ∃z. i64_add x y = Return z ∧
              i64_to_int z = i64_to_int x + i64_to_int y
   
   [i64_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, usize_bounds] []
      ⊢ ∀x y.
          i64_to_int y ≠ 0 ⇒
          i64_min ≤ i64_to_int x / i64_to_int y ⇒
          i64_to_int x / i64_to_int y ≤ i64_max ⇒
          ∃z. i64_div x y = Return z ∧
              i64_to_int z = i64_to_int x / i64_to_int y
   
   [i64_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, usize_bounds] []
      ⊢ ∀x y.
          i64_min ≤ i64_to_int x * i64_to_int y ⇒
          i64_to_int x * i64_to_int y ≤ i64_max ⇒
          ∃z. i64_mul x y = Return z ∧
              i64_to_int z = i64_to_int x * i64_to_int y
   
   [i64_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, i64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          i64_to_int y ≠ 0 ⇒
          i64_min ≤ int_rem (i64_to_int x) (i64_to_int y) ⇒
          int_rem (i64_to_int x) (i64_to_int y) ≤ i64_max ⇒
          ∃z. i64_rem x y = Return z ∧
              i64_to_int z = int_rem (i64_to_int x) (i64_to_int y)
   
   [i64_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, usize_bounds] []
      ⊢ ∀x y.
          i64_min ≤ i64_to_int x − i64_to_int y ⇒
          i64_to_int x − i64_to_int y ≤ i64_max ⇒
          ∃z. i64_sub x y = Return z ∧
              i64_to_int z = i64_to_int x − i64_to_int y
   
   [i8_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, usize_bounds] []
      ⊢ ∀x y.
          i8_min ≤ i8_to_int x + i8_to_int y ⇒
          i8_to_int x + i8_to_int y ≤ i8_max ⇒
          ∃z. i8_add x y = Return z ∧
              i8_to_int z = i8_to_int x + i8_to_int y
   
   [i8_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, usize_bounds] []
      ⊢ ∀x y.
          i8_to_int y ≠ 0 ⇒
          i8_min ≤ i8_to_int x / i8_to_int y ⇒
          i8_to_int x / i8_to_int y ≤ i8_max ⇒
          ∃z. i8_div x y = Return z ∧
              i8_to_int z = i8_to_int x / i8_to_int y
   
   [i8_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, usize_bounds] []
      ⊢ ∀x y.
          i8_min ≤ i8_to_int x * i8_to_int y ⇒
          i8_to_int x * i8_to_int y ≤ i8_max ⇒
          ∃z. i8_mul x y = Return z ∧
              i8_to_int z = i8_to_int x * i8_to_int y
   
   [i8_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, i8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          i8_to_int y ≠ 0 ⇒
          i8_min ≤ int_rem (i8_to_int x) (i8_to_int y) ⇒
          int_rem (i8_to_int x) (i8_to_int y) ≤ i8_max ⇒
          ∃z. i8_rem x y = Return z ∧
              i8_to_int z = int_rem (i8_to_int x) (i8_to_int y)
   
   [i8_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, usize_bounds] []
      ⊢ ∀x y.
          i8_min ≤ i8_to_int x − i8_to_int y ⇒
          i8_to_int x − i8_to_int y ≤ i8_max ⇒
          ∃z. i8_sub x y = Return z ∧
              i8_to_int z = i8_to_int x − i8_to_int y
   
   [index_update_diff]  Theorem
      
      ⊢ ∀ls i j y. 0 ≤ i ⇒ i < len ls ⇒ index i (update ls i y) = y
   
   [index_update_same]  Theorem
      
      ⊢ ∀ls i j y.
          0 ≤ i ⇒
          i < len ls ⇒
          j < len ls ⇒
          j ≠ i ⇒
          index j (update ls i y) = index j ls
   
   [int_of_num_neq_inj]  Theorem
      
      ⊢ ∀n m. &n ≠ &m ⇒ n ≠ m
   
   [isize_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, isize_to_int_int_to_isize,
       isize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ isize_to_int x + isize_to_int y ∨
          isize_min ≤ isize_to_int x + isize_to_int y ⇒
          isize_to_int x + isize_to_int y ≤ i16_max ∨
          isize_to_int x + isize_to_int y ≤ isize_max ⇒
          ∃z. isize_add x y = Return z ∧
              isize_to_int z = isize_to_int x + isize_to_int y
   
   [isize_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, isize_to_int_int_to_isize,
       isize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          isize_to_int y ≠ 0 ⇒
          i16_min ≤ isize_to_int x / isize_to_int y ∨
          isize_min ≤ isize_to_int x / isize_to_int y ⇒
          isize_to_int x / isize_to_int y ≤ i16_max ∨
          isize_to_int x / isize_to_int y ≤ isize_max ⇒
          ∃z. isize_div x y = Return z ∧
              isize_to_int z = isize_to_int x / isize_to_int y
   
   [isize_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, isize_to_int_int_to_isize,
       isize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ isize_to_int x * isize_to_int y ∨
          isize_min ≤ isize_to_int x * isize_to_int y ⇒
          isize_to_int x * isize_to_int y ≤ i16_max ∨
          isize_to_int x * isize_to_int y ≤ isize_max ⇒
          ∃z. isize_mul x y = Return z ∧
              isize_to_int z = isize_to_int x * isize_to_int y
   
   [isize_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, isize_to_int_int_to_isize,
       isize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          isize_to_int y ≠ 0 ⇒
          i16_min ≤ int_rem (isize_to_int x) (isize_to_int y) ∨
          isize_min ≤ int_rem (isize_to_int x) (isize_to_int y) ⇒
          int_rem (isize_to_int x) (isize_to_int y) ≤ i16_max ∨
          int_rem (isize_to_int x) (isize_to_int y) ≤ isize_max ⇒
          ∃z. isize_rem x y = Return z ∧
              isize_to_int z = int_rem (isize_to_int x) (isize_to_int y)
   
   [isize_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, isize_to_int_int_to_isize,
       isize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ isize_to_int x − isize_to_int y ∨
          isize_min ≤ isize_to_int x − isize_to_int y ⇒
          isize_to_int x − isize_to_int y ≤ i16_max ∨
          isize_to_int x − isize_to_int y ≤ isize_max ⇒
          ∃z. isize_sub x y = Return z ∧
              isize_to_int z = isize_to_int x − isize_to_int y
   
   [num2error_11]  Theorem
      
      ⊢ ∀r r'. r < 1 ⇒ r' < 1 ⇒ (num2error r = num2error r' ⇔ r = r')
   
   [num2error_ONTO]  Theorem
      
      ⊢ ∀a. ∃r. a = num2error r ∧ r < 1
   
   [num2error_error2num]  Theorem
      
      ⊢ ∀a. num2error (error2num a) = a
   
   [num2error_thm]  Theorem
      
      ⊢ num2error 0 = Failure
   
   [result_11]  Theorem
      
      ⊢ (∀a a'. Return a = Return a' ⇔ a = a') ∧
        ∀a a'. Fail a = Fail a' ⇔ a = a'
   
   [result_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn.
          (∀a. fn (Return a) = f0 a) ∧ (∀a. fn (Fail a) = f1 a) ∧
          fn Loop = f2
   
   [result_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 v.
          M = M' ∧ (∀a. M' = Return a ⇒ f a = f' a) ∧
          (∀a. M' = Fail a ⇒ f1 a = f1' a) ∧ (M' = Loop ⇒ v = v') ⇒
          result_CASE M f f1 v = result_CASE M' f' f1' v'
   
   [result_case_eq]  Theorem
      
      ⊢ result_CASE x f f1 v = v' ⇔
        (∃a. x = Return a ∧ f a = v') ∨ (∃e. x = Fail e ∧ f1 e = v') ∨
        x = Loop ∧ v = v'
   
   [result_distinct]  Theorem
      
      ⊢ (∀a' a. Return a ≠ Fail a') ∧ (∀a. Return a ≠ Loop) ∧
        ∀a. Fail a ≠ Loop
   
   [result_induction]  Theorem
      
      ⊢ ∀P. (∀a. P (Return a)) ∧ (∀e. P (Fail e)) ∧ P Loop ⇒ ∀r. P r
   
   [result_nchotomy]  Theorem
      
      ⊢ ∀rr. (∃a. rr = Return a) ∨ (∃e. rr = Fail e) ∨ rr = Loop
   
   [u128_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u128_to_int_int_to_u128, u128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u128_to_int x + u128_to_int y ≤ u128_max ⇒
          ∃z. u128_add x y = Return z ∧
              u128_to_int z = u128_to_int x + u128_to_int y
   
   [u128_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u128_to_int_int_to_u128, u128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u128_to_int y ≠ 0 ⇒
          ∃z. u128_div x y = Return z ∧
              u128_to_int z = u128_to_int x / u128_to_int y
   
   [u128_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u128_to_int_int_to_u128, u128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u128_to_int x * u128_to_int y ≤ u128_max ⇒
          ∃z. u128_mul x y = Return z ∧
              u128_to_int z = u128_to_int x * u128_to_int y
   
   [u128_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u128_to_int_int_to_u128, u128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u128_to_int y ≠ 0 ⇒
          ∃z. u128_rem x y = Return z ∧
              u128_to_int z = int_rem (u128_to_int x) (u128_to_int y)
   
   [u128_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u128_to_int_int_to_u128, u128_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          0 ≤ u128_to_int x − u128_to_int y ⇒
          ∃z. u128_sub x y = Return z ∧
              u128_to_int z = u128_to_int x − u128_to_int y
   
   [u16_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u16_to_int_int_to_u16, u16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u16_to_int x + u16_to_int y ≤ u16_max ⇒
          ∃z. u16_add x y = Return z ∧
              u16_to_int z = u16_to_int x + u16_to_int y
   
   [u16_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u16_to_int_int_to_u16, u16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u16_to_int y ≠ 0 ⇒
          ∃z. u16_div x y = Return z ∧
              u16_to_int z = u16_to_int x / u16_to_int y
   
   [u16_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u16_to_int_int_to_u16, u16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u16_to_int x * u16_to_int y ≤ u16_max ⇒
          ∃z. u16_mul x y = Return z ∧
              u16_to_int z = u16_to_int x * u16_to_int y
   
   [u16_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u16_to_int_int_to_u16, u16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u16_to_int y ≠ 0 ⇒
          ∃z. u16_rem x y = Return z ∧
              u16_to_int z = int_rem (u16_to_int x) (u16_to_int y)
   
   [u16_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u16_to_int_int_to_u16, u16_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          0 ≤ u16_to_int x − u16_to_int y ⇒
          ∃z. u16_sub x y = Return z ∧
              u16_to_int z = u16_to_int x − u16_to_int y
   
   [u32_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u32_to_int_int_to_u32, u32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u32_to_int x + u32_to_int y ≤ u32_max ⇒
          ∃z. u32_add x y = Return z ∧
              u32_to_int z = u32_to_int x + u32_to_int y
   
   [u32_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u32_to_int_int_to_u32, u32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u32_to_int y ≠ 0 ⇒
          ∃z. u32_div x y = Return z ∧
              u32_to_int z = u32_to_int x / u32_to_int y
   
   [u32_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u32_to_int_int_to_u32, u32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u32_to_int x * u32_to_int y ≤ u32_max ⇒
          ∃z. u32_mul x y = Return z ∧
              u32_to_int z = u32_to_int x * u32_to_int y
   
   [u32_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u32_to_int_int_to_u32, u32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u32_to_int y ≠ 0 ⇒
          ∃z. u32_rem x y = Return z ∧
              u32_to_int z = int_rem (u32_to_int x) (u32_to_int y)
   
   [u32_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u32_to_int_int_to_u32, u32_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          0 ≤ u32_to_int x − u32_to_int y ⇒
          ∃z. u32_sub x y = Return z ∧
              u32_to_int z = u32_to_int x − u32_to_int y
   
   [u64_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u64_to_int_int_to_u64, u64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u64_to_int x + u64_to_int y ≤ u64_max ⇒
          ∃z. u64_add x y = Return z ∧
              u64_to_int z = u64_to_int x + u64_to_int y
   
   [u64_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u64_to_int_int_to_u64, u64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u64_to_int y ≠ 0 ⇒
          ∃z. u64_div x y = Return z ∧
              u64_to_int z = u64_to_int x / u64_to_int y
   
   [u64_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u64_to_int_int_to_u64, u64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u64_to_int x * u64_to_int y ≤ u64_max ⇒
          ∃z. u64_mul x y = Return z ∧
              u64_to_int z = u64_to_int x * u64_to_int y
   
   [u64_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u64_to_int_int_to_u64, u64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u64_to_int y ≠ 0 ⇒
          ∃z. u64_rem x y = Return z ∧
              u64_to_int z = int_rem (u64_to_int x) (u64_to_int y)
   
   [u64_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u64_to_int_int_to_u64, u64_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          0 ≤ u64_to_int x − u64_to_int y ⇒
          ∃z. u64_sub x y = Return z ∧
              u64_to_int z = u64_to_int x − u64_to_int y
   
   [u8_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u8_to_int_int_to_u8, u8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u8_to_int x + u8_to_int y ≤ u8_max ⇒
          ∃z. u8_add x y = Return z ∧
              u8_to_int z = u8_to_int x + u8_to_int y
   
   [u8_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u8_to_int_int_to_u8, u8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u8_to_int y ≠ 0 ⇒
          ∃z. u8_div x y = Return z ∧
              u8_to_int z = u8_to_int x / u8_to_int y
   
   [u8_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u8_to_int_int_to_u8, u8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u8_to_int x * u8_to_int y ≤ u8_max ⇒
          ∃z. u8_mul x y = Return z ∧
              u8_to_int z = u8_to_int x * u8_to_int y
   
   [u8_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u8_to_int_int_to_u8, u8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          u8_to_int y ≠ 0 ⇒
          ∃z. u8_rem x y = Return z ∧
              u8_to_int z = int_rem (u8_to_int x) (u8_to_int y)
   
   [u8_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, u8_to_int_int_to_u8, u8_to_int_bounds,
       usize_bounds] []
      ⊢ ∀x y.
          0 ≤ u8_to_int x − u8_to_int y ⇒
          ∃z. u8_sub x y = Return z ∧
              u8_to_int z = u8_to_int x − u8_to_int y
   
   [update_ind]  Theorem
      
      ⊢ ∀P. (∀i y. P [] i y) ∧ (∀v0 ls y. P (v0::ls) 0 y) ∧
            (∀x ls i y. P ls i y ⇒ P (x::ls) (SUC i) y) ⇒
            ∀v v1 v2. P v v1 v2
   
   [update_len]  Theorem
      
      ⊢ ∀ls i y. len (update ls i y) = len ls
   
   [update_spec]  Theorem
      
      ⊢ ∀ls i y.
          0 ≤ i ⇒
          i < len ls ⇒
          len (update ls i y) = len ls ∧ index i (update ls i y) = y ∧
          ∀j. j < len ls ⇒ j ≠ i ⇒ index j (update ls i y) = index j ls
   
   [usize_add_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, usize_to_int_int_to_usize,
       usize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          usize_to_int x + usize_to_int y ≤ u16_max ∨
          usize_to_int x + usize_to_int y ≤ usize_max ⇒
          ∃z. usize_add x y = Return z ∧
              usize_to_int z = usize_to_int x + usize_to_int y
   
   [usize_div_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, usize_to_int_int_to_usize,
       usize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          usize_to_int y ≠ 0 ⇒
          ∃z. usize_div x y = Return z ∧
              usize_to_int z = usize_to_int x / usize_to_int y
   
   [usize_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, usize_to_int_int_to_usize,
       usize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          usize_to_int x * usize_to_int y ≤ u16_max ∨
          usize_to_int x * usize_to_int y ≤ usize_max ⇒
          ∃z. usize_mul x y = Return z ∧
              usize_to_int z = usize_to_int x * usize_to_int y
   
   [usize_rem_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, usize_to_int_int_to_usize,
       usize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          usize_to_int y ≠ 0 ⇒
          ∃z. usize_rem x y = Return z ∧
              usize_to_int z = int_rem (usize_to_int x) (usize_to_int y)
   
   [usize_sub_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, usize_to_int_int_to_usize,
       usize_to_int_bounds, usize_bounds] []
      ⊢ ∀x y.
          0 ≤ usize_to_int x − usize_to_int y ⇒
          ∃z. usize_sub x y = Return z ∧
              usize_to_int z = usize_to_int x − usize_to_int y
   
   [vec_insert_back_spec]  Theorem
      
      [oracles: DISK_THM, cheat]
      [axioms: usize_to_int_bounds, usize_to_int_int_to_usize, mk_vec_spec]
      []
      ⊢ ∀v i x.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          ∃nv.
            vec_insert_back v i x = Return nv ∧ vec_len v = vec_len nv ∧
            vec_index i nv = Return x ∧
            ∀j. usize_to_int j < usize_to_int (vec_len nv) ⇒
                usize_to_int j ≠ usize_to_int i ⇒
                vec_index j nv = vec_index j v
   
   [vec_len_spec]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀v. vec_len v = int_to_usize (len (vec_to_list v)) ∧
            0 ≤ len (vec_to_list v) ∧ len (vec_to_list v) ≤ usize_max
   
   [vec_to_list_int_bounds]  Theorem
      
      [oracles: cheat] [axioms: ] []
      ⊢ ∀v. 0 ≤ len (vec_to_list v) ∧ len (vec_to_list v) ≤ usize_max
   
   
*)
end
