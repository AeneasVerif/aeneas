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
    val mk_vec_axiom : thm
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
    val core_i128_max_def : thm
    val core_i128_min_def : thm
    val core_i16_max_def : thm
    val core_i16_min_def : thm
    val core_i32_max_def : thm
    val core_i32_min_def : thm
    val core_i64_max_def : thm
    val core_i64_min_def : thm
    val core_i8_max_def : thm
    val core_i8_min_def : thm
    val core_isize_max_def : thm
    val core_isize_min_def : thm
    val core_u128_max_def : thm
    val core_u128_min_def : thm
    val core_u16_max_def : thm
    val core_u16_min_def : thm
    val core_u32_max_def : thm
    val core_u32_min_def : thm
    val core_u64_max_def : thm
    val core_u64_min_def : thm
    val core_u8_max_def : thm
    val core_u8_min_def : thm
    val core_usize_max_def : thm
    val core_usize_min_def : thm
    val error_BIJ : thm
    val error_CASE : thm
    val error_TY_DEF : thm
    val error_size_def : thm
    val get_return_value_def : thm
    val i128_add_def : thm
    val i128_div_def : thm
    val i128_ge_def : thm
    val i128_gt_def : thm
    val i128_le_def : thm
    val i128_lt_def : thm
    val i128_max_def : thm
    val i128_min_def : thm
    val i128_mul_def : thm
    val i128_neg_def : thm
    val i128_rem_def : thm
    val i128_sub_def : thm
    val i16_add_def : thm
    val i16_div_def : thm
    val i16_ge_def : thm
    val i16_gt_def : thm
    val i16_le_def : thm
    val i16_lt_def : thm
    val i16_max_def : thm
    val i16_min_def : thm
    val i16_mul_def : thm
    val i16_neg_def : thm
    val i16_rem_def : thm
    val i16_sub_def : thm
    val i32_add_def : thm
    val i32_div_def : thm
    val i32_ge_def : thm
    val i32_gt_def : thm
    val i32_le_def : thm
    val i32_lt_def : thm
    val i32_max_def : thm
    val i32_min_def : thm
    val i32_mul_def : thm
    val i32_neg_def : thm
    val i32_rem_def : thm
    val i32_sub_def : thm
    val i64_add_def : thm
    val i64_div_def : thm
    val i64_ge_def : thm
    val i64_gt_def : thm
    val i64_le_def : thm
    val i64_lt_def : thm
    val i64_max_def : thm
    val i64_min_def : thm
    val i64_mul_def : thm
    val i64_neg_def : thm
    val i64_rem_def : thm
    val i64_sub_def : thm
    val i8_add_def : thm
    val i8_div_def : thm
    val i8_ge_def : thm
    val i8_gt_def : thm
    val i8_le_def : thm
    val i8_lt_def : thm
    val i8_max_def : thm
    val i8_min_def : thm
    val i8_mul_def : thm
    val i8_neg_def : thm
    val i8_rem_def : thm
    val i8_sub_def : thm
    val int_rem_def : thm
    val is_diverge_def : thm
    val isize_add_def : thm
    val isize_div_def : thm
    val isize_ge_def : thm
    val isize_gt_def : thm
    val isize_le_def : thm
    val isize_lt_def : thm
    val isize_mul_def : thm
    val isize_neg_def : thm
    val isize_rem_def : thm
    val isize_sub_def : thm
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
    val u128_ge_def : thm
    val u128_gt_def : thm
    val u128_le_def : thm
    val u128_lt_def : thm
    val u128_max_def : thm
    val u128_mul_def : thm
    val u128_rem_def : thm
    val u128_sub_def : thm
    val u16_add_def : thm
    val u16_div_def : thm
    val u16_ge_def : thm
    val u16_gt_def : thm
    val u16_le_def : thm
    val u16_lt_def : thm
    val u16_max_def : thm
    val u16_mul_def : thm
    val u16_rem_def : thm
    val u16_sub_def : thm
    val u32_add_def : thm
    val u32_div_def : thm
    val u32_ge_def : thm
    val u32_gt_def : thm
    val u32_le_def : thm
    val u32_lt_def : thm
    val u32_max_def : thm
    val u32_mul_def : thm
    val u32_rem_def : thm
    val u32_sub_def : thm
    val u64_add_def : thm
    val u64_div_def : thm
    val u64_ge_def : thm
    val u64_gt_def : thm
    val u64_le_def : thm
    val u64_lt_def : thm
    val u64_max_def : thm
    val u64_mul_def : thm
    val u64_rem_def : thm
    val u64_sub_def : thm
    val u8_add_def : thm
    val u8_div_def : thm
    val u8_ge_def : thm
    val u8_gt_def : thm
    val u8_le_def : thm
    val u8_lt_def : thm
    val u8_max_def : thm
    val u8_mul_def : thm
    val u8_rem_def : thm
    val u8_sub_def : thm
    val usize_add_def : thm
    val usize_div_def : thm
    val usize_ge_def : thm
    val usize_gt_def : thm
    val usize_le_def : thm
    val usize_lt_def : thm
    val usize_mul_def : thm
    val usize_rem_def : thm
    val usize_sub_def : thm
    val vec_index_back_def : thm
    val vec_index_def : thm
    val vec_index_fwd_def : thm
    val vec_index_mut_back_def : thm
    val vec_index_mut_fwd_def : thm
    val vec_insert_back_def : thm
    val vec_len_def : thm
    val vec_new_def : thm
    val vec_push_back_def : thm
    val vec_update_def : thm
  
  (*  Theorems  *)
    val bind_return_fail_div_eq : thm
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
    val i128_eq_equiv : thm
    val i128_mul_eq : thm
    val i128_neg_eq : thm
    val i128_rem_eq : thm
    val i128_sub_eq : thm
    val i128_to_int_int_to_i128_unfold : thm
    val i16_add_eq : thm
    val i16_div_eq : thm
    val i16_eq_equiv : thm
    val i16_mul_eq : thm
    val i16_neg_eq : thm
    val i16_rem_eq : thm
    val i16_sub_eq : thm
    val i16_to_int_int_to_i16_unfold : thm
    val i32_add_eq : thm
    val i32_div_eq : thm
    val i32_eq_equiv : thm
    val i32_mul_eq : thm
    val i32_neg_eq : thm
    val i32_rem_eq : thm
    val i32_sub_eq : thm
    val i32_to_int_int_to_i32_unfold : thm
    val i64_add_eq : thm
    val i64_div_eq : thm
    val i64_eq_equiv : thm
    val i64_mul_eq : thm
    val i64_neg_eq : thm
    val i64_rem_eq : thm
    val i64_sub_eq : thm
    val i64_to_int_int_to_i64_unfold : thm
    val i8_add_eq : thm
    val i8_div_eq : thm
    val i8_eq_equiv : thm
    val i8_mul_eq : thm
    val i8_neg_eq : thm
    val i8_rem_eq : thm
    val i8_sub_eq : thm
    val i8_to_int_int_to_i8_unfold : thm
    val index_update_diff : thm
    val index_update_same : thm
    val isize_add_eq : thm
    val isize_div_eq : thm
    val isize_eq_equiv : thm
    val isize_mul_eq : thm
    val isize_neg_eq : thm
    val isize_rem_eq : thm
    val isize_sub_eq : thm
    val isize_to_int_int_to_isize_i16_bounds : thm
    val isize_to_int_int_to_isize_unfold : thm
    val len_update : thm
    val mk_isize_unfold : thm
    val mk_usize_unfold : thm
    val mk_vec_unfold : thm
    val num2error_11 : thm
    val num2error_ONTO : thm
    val num2error_error2num : thm
    val num2error_thm : thm
    val pos_rem_pos_ineqs : thm
    val result_11 : thm
    val result_Axiom : thm
    val result_case_cong : thm
    val result_case_eq : thm
    val result_distinct : thm
    val result_induction : thm
    val result_nchotomy : thm
    val u128_add_eq : thm
    val u128_div_eq : thm
    val u128_eq_equiv : thm
    val u128_mul_eq : thm
    val u128_rem_eq : thm
    val u128_sub_eq : thm
    val u128_to_int_int_to_u128_unfold : thm
    val u16_add_eq : thm
    val u16_div_eq : thm
    val u16_eq_equiv : thm
    val u16_mul_eq : thm
    val u16_rem_eq : thm
    val u16_sub_eq : thm
    val u16_to_int_int_to_u16_unfold : thm
    val u32_add_eq : thm
    val u32_div_eq : thm
    val u32_eq_equiv : thm
    val u32_mul_eq : thm
    val u32_rem_eq : thm
    val u32_sub_eq : thm
    val u32_to_int_int_to_u32_unfold : thm
    val u64_add_eq : thm
    val u64_div_eq : thm
    val u64_eq_equiv : thm
    val u64_mul_eq : thm
    val u64_rem_eq : thm
    val u64_sub_eq : thm
    val u64_to_int_int_to_u64_unfold : thm
    val u8_add_eq : thm
    val u8_div_eq : thm
    val u8_eq_equiv : thm
    val u8_mul_eq : thm
    val u8_rem_eq : thm
    val u8_sub_eq : thm
    val u8_to_int_int_to_u8_unfold : thm
    val update_len : thm
    val update_spec : thm
    val usize_add_eq : thm
    val usize_div_eq : thm
    val usize_eq_equiv : thm
    val usize_mul_eq : thm
    val usize_rem_eq : thm
    val usize_sub_eq : thm
    val usize_to_int_int_to_usize_u16_bounds : thm
    val usize_to_int_int_to_usize_unfold : thm
    val vec_index_back_spec : thm
    val vec_index_fwd_spec : thm
    val vec_index_mut_back_spec : thm
    val vec_index_mut_fwd_spec : thm
    val vec_insert_back_spec : thm
    val vec_len_spec : thm
    val vec_len_vec_new : thm
    val vec_push_back_spec : thm
    val vec_push_back_unfold : thm
    val vec_to_list_int_bounds : thm
    val vec_to_list_vec_new : thm
    val vec_to_list_vec_update : thm
    val vec_update_eq : thm
  
  val primitives_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ilist] Parent theory of "primitives"
   
   [string] Parent theory of "primitives"
   
   [i128_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i128_to_int_bounds] []
      ⊢ ∀n. i128_min ≤ i128_to_int n ∧ i128_to_int n ≤ i128_max
   
   [i128_to_int_int_to_i128]  Axiom
      
      [oracles: ] [axioms: i128_to_int_int_to_i128] []
      ⊢ ∀n. i128_min ≤ n ∧ n ≤ i128_max ⇒ i128_to_int (int_to_i128 n) = n
   
   [i16_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i16_to_int_bounds] []
      ⊢ ∀n. i16_min ≤ i16_to_int n ∧ i16_to_int n ≤ i16_max
   
   [i16_to_int_int_to_i16]  Axiom
      
      [oracles: ] [axioms: i16_to_int_int_to_i16] []
      ⊢ ∀n. i16_min ≤ n ∧ n ≤ i16_max ⇒ i16_to_int (int_to_i16 n) = n
   
   [i32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i32_to_int_bounds] []
      ⊢ ∀n. i32_min ≤ i32_to_int n ∧ i32_to_int n ≤ i32_max
   
   [i32_to_int_int_to_i32]  Axiom
      
      [oracles: ] [axioms: i32_to_int_int_to_i32] []
      ⊢ ∀n. i32_min ≤ n ∧ n ≤ i32_max ⇒ i32_to_int (int_to_i32 n) = n
   
   [i64_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i64_to_int_bounds] []
      ⊢ ∀n. i64_min ≤ i64_to_int n ∧ i64_to_int n ≤ i64_max
   
   [i64_to_int_int_to_i64]  Axiom
      
      [oracles: ] [axioms: i64_to_int_int_to_i64] []
      ⊢ ∀n. i64_min ≤ n ∧ n ≤ i64_max ⇒ i64_to_int (int_to_i64 n) = n
   
   [i8_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i8_to_int_bounds] []
      ⊢ ∀n. i8_min ≤ i8_to_int n ∧ i8_to_int n ≤ i8_max
   
   [i8_to_int_int_to_i8]  Axiom
      
      [oracles: ] [axioms: i8_to_int_int_to_i8] []
      ⊢ ∀n. i8_min ≤ n ∧ n ≤ i8_max ⇒ i8_to_int (int_to_i8 n) = n
   
   [int_to_i128_i128_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i128_i128_to_int] []
      ⊢ ∀i. int_to_i128 (i128_to_int i) = i
   
   [int_to_i16_i16_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i16_i16_to_int] []
      ⊢ ∀i. int_to_i16 (i16_to_int i) = i
   
   [int_to_i32_i32_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i32_i32_to_int] []
      ⊢ ∀i. int_to_i32 (i32_to_int i) = i
   
   [int_to_i64_i64_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i64_i64_to_int] []
      ⊢ ∀i. int_to_i64 (i64_to_int i) = i
   
   [int_to_i8_i8_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_i8_i8_to_int] []
      ⊢ ∀i. int_to_i8 (i8_to_int i) = i
   
   [int_to_isize_isize_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_isize_isize_to_int] []
      ⊢ ∀i. int_to_isize (isize_to_int i) = i
   
   [int_to_u128_u128_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u128_u128_to_int] []
      ⊢ ∀i. int_to_u128 (u128_to_int i) = i
   
   [int_to_u16_u16_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u16_u16_to_int] []
      ⊢ ∀i. int_to_u16 (u16_to_int i) = i
   
   [int_to_u32_u32_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u32_u32_to_int] []
      ⊢ ∀i. int_to_u32 (u32_to_int i) = i
   
   [int_to_u64_u64_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u64_u64_to_int] []
      ⊢ ∀i. int_to_u64 (u64_to_int i) = i
   
   [int_to_u8_u8_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_u8_u8_to_int] []
      ⊢ ∀i. int_to_u8 (u8_to_int i) = i
   
   [int_to_usize_usize_to_int]  Axiom
      
      [oracles: ] [axioms: int_to_usize_usize_to_int] []
      ⊢ ∀i. int_to_usize (usize_to_int i) = i
   
   [isize_bounds]  Axiom
      
      [oracles: ] [axioms: isize_bounds] []
      ⊢ isize_min ≤ i16_min ∧ i16_max ≤ isize_max
   
   [isize_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: isize_to_int_bounds] []
      ⊢ ∀n. isize_min ≤ isize_to_int n ∧ isize_to_int n ≤ isize_max
   
   [isize_to_int_int_to_isize]  Axiom
      
      [oracles: ] [axioms: isize_to_int_int_to_isize] []
      ⊢ ∀n. isize_min ≤ n ∧ n ≤ isize_max ⇒
            isize_to_int (int_to_isize n) = n
   
   [mk_vec_axiom]  Axiom
      
      [oracles: ] [axioms: mk_vec_axiom] []
      ⊢ ∀l. len l ≤ usize_max ⇒ vec_to_list (mk_vec l) = l
   
   [u128_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u128_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u128_to_int n ∧ u128_to_int n ≤ u128_max
   
   [u128_to_int_int_to_u128]  Axiom
      
      [oracles: ] [axioms: u128_to_int_int_to_u128] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u128_max ⇒ u128_to_int (int_to_u128 n) = n
   
   [u16_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u16_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u16_to_int n ∧ u16_to_int n ≤ u16_max
   
   [u16_to_int_int_to_u16]  Axiom
      
      [oracles: ] [axioms: u16_to_int_int_to_u16] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u16_max ⇒ u16_to_int (int_to_u16 n) = n
   
   [u32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u32_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u32_to_int n ∧ u32_to_int n ≤ u32_max
   
   [u32_to_int_int_to_u32]  Axiom
      
      [oracles: ] [axioms: u32_to_int_int_to_u32] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u32_max ⇒ u32_to_int (int_to_u32 n) = n
   
   [u64_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u64_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u64_to_int n ∧ u64_to_int n ≤ u64_max
   
   [u64_to_int_int_to_u64]  Axiom
      
      [oracles: ] [axioms: u64_to_int_int_to_u64] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u64_max ⇒ u64_to_int (int_to_u64 n) = n
   
   [u8_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u8_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u8_to_int n ∧ u8_to_int n ≤ u8_max
   
   [u8_to_int_int_to_u8]  Axiom
      
      [oracles: ] [axioms: u8_to_int_int_to_u8] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u8_max ⇒ u8_to_int (int_to_u8 n) = n
   
   [usize_bounds]  Axiom
      
      [oracles: ] [axioms: usize_bounds] [] ⊢ u16_max ≤ usize_max
   
   [usize_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: usize_to_int_bounds] []
      ⊢ ∀n. 0 ≤ usize_to_int n ∧ usize_to_int n ≤ usize_max
   
   [usize_to_int_int_to_usize]  Axiom
      
      [oracles: ] [axioms: usize_to_int_int_to_usize] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ usize_max ⇒ usize_to_int (int_to_usize n) = n
   
   [vec_to_list_num_bounds]  Axiom
      
      [oracles: ] [axioms: vec_to_list_num_bounds] []
      ⊢ ∀v. 0 ≤ LENGTH (vec_to_list v) ∧
            LENGTH (vec_to_list v) ≤ Num usize_max
   
   [bind_def]  Definition
      
      ⊢ ∀x f.
          monad_bind x f =
          case x of Return y => f y | Fail e => Fail e | Diverge => Diverge
   
   [core_i128_max_def]  Definition
      
      ⊢ core_i128_max = int_to_i128 i128_max
   
   [core_i128_min_def]  Definition
      
      ⊢ core_i128_min = int_to_i128 i128_min
   
   [core_i16_max_def]  Definition
      
      ⊢ core_i16_max = int_to_i16 i16_max
   
   [core_i16_min_def]  Definition
      
      ⊢ core_i16_min = int_to_i16 i16_min
   
   [core_i32_max_def]  Definition
      
      ⊢ core_i32_max = int_to_i32 i32_max
   
   [core_i32_min_def]  Definition
      
      ⊢ core_i32_min = int_to_i32 i32_min
   
   [core_i64_max_def]  Definition
      
      ⊢ core_i64_max = int_to_i64 i64_max
   
   [core_i64_min_def]  Definition
      
      ⊢ core_i64_min = int_to_i64 i64_min
   
   [core_i8_max_def]  Definition
      
      ⊢ core_i8_max = int_to_i8 i8_max
   
   [core_i8_min_def]  Definition
      
      ⊢ core_i8_min = int_to_i8 i8_min
   
   [core_isize_max_def]  Definition
      
      ⊢ core_isize_max = int_to_isize isize_max
   
   [core_isize_min_def]  Definition
      
      ⊢ core_isize_min = int_to_isize isize_min
   
   [core_u128_max_def]  Definition
      
      ⊢ core_u128_max = int_to_u128 u128_max
   
   [core_u128_min_def]  Definition
      
      ⊢ core_u128_min = int_to_u128 0
   
   [core_u16_max_def]  Definition
      
      ⊢ core_u16_max = int_to_u16 u16_max
   
   [core_u16_min_def]  Definition
      
      ⊢ core_u16_min = int_to_u16 0
   
   [core_u32_max_def]  Definition
      
      ⊢ core_u32_max = int_to_u32 u32_max
   
   [core_u32_min_def]  Definition
      
      ⊢ core_u32_min = int_to_u32 0
   
   [core_u64_max_def]  Definition
      
      ⊢ core_u64_max = int_to_u64 u64_max
   
   [core_u64_min_def]  Definition
      
      ⊢ core_u64_min = int_to_u64 0
   
   [core_u8_max_def]  Definition
      
      ⊢ core_u8_max = int_to_u8 u8_max
   
   [core_u8_min_def]  Definition
      
      ⊢ core_u8_min = int_to_u8 0
   
   [core_usize_max_def]  Definition
      
      ⊢ core_usize_max = int_to_usize usize_max
   
   [core_usize_min_def]  Definition
      
      ⊢ core_usize_min = int_to_usize 0
   
   [error_BIJ]  Definition
      
      ⊢ (∀a. num2error (error2num a) = a) ∧
        ∀r. (λn. n < 1) r ⇔ error2num (num2error r) = r
   
   [error_CASE]  Definition
      
      ⊢ ∀x v0. (case x of Failure => v0) = (λm. v0) (error2num x)
   
   [error_TY_DEF]  Definition
      
      ⊢ ∃rep. TYPE_DEFINITION (λn. n < 1) rep
   
   [error_size_def]  Definition
      
      ⊢ ∀x. error_size x = 0
   
   [get_return_value_def]  Definition
      
      ⊢ ∀x. get_return_value (Return x) = x
   
   [i128_add_def]  Definition
      
      ⊢ ∀x y. i128_add x y = mk_i128 (i128_to_int x + i128_to_int y)
   
   [i128_div_def]  Definition
      
      ⊢ ∀x y.
          i128_div x y =
          if i128_to_int y = 0 then Fail Failure
          else mk_i128 (i128_to_int x / i128_to_int y)
   
   [i128_ge_def]  Definition
      
      ⊢ ∀x y. i128_ge x y ⇔ i128_to_int x ≥ i128_to_int y
   
   [i128_gt_def]  Definition
      
      ⊢ ∀x y. i128_gt x y ⇔ i128_to_int x > i128_to_int y
   
   [i128_le_def]  Definition
      
      ⊢ ∀x y. i128_le x y ⇔ i128_to_int x ≤ i128_to_int y
   
   [i128_lt_def]  Definition
      
      ⊢ ∀x y. i128_lt x y ⇔ i128_to_int x < i128_to_int y
   
   [i128_max_def]  Definition
      
      ⊢ i128_max = 170141183460469231731687303715884105727
   
   [i128_min_def]  Definition
      
      ⊢ i128_min = -170141183460469231731687303715884105728
   
   [i128_mul_def]  Definition
      
      ⊢ ∀x y. i128_mul x y = mk_i128 (i128_to_int x * i128_to_int y)
   
   [i128_neg_def]  Definition
      
      ⊢ ∀x. i128_neg x = mk_i128 (-i128_to_int x)
   
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
   
   [i16_ge_def]  Definition
      
      ⊢ ∀x y. i16_ge x y ⇔ i16_to_int x ≥ i16_to_int y
   
   [i16_gt_def]  Definition
      
      ⊢ ∀x y. i16_gt x y ⇔ i16_to_int x > i16_to_int y
   
   [i16_le_def]  Definition
      
      ⊢ ∀x y. i16_le x y ⇔ i16_to_int x ≤ i16_to_int y
   
   [i16_lt_def]  Definition
      
      ⊢ ∀x y. i16_lt x y ⇔ i16_to_int x < i16_to_int y
   
   [i16_max_def]  Definition
      
      ⊢ i16_max = 32767
   
   [i16_min_def]  Definition
      
      ⊢ i16_min = -32768
   
   [i16_mul_def]  Definition
      
      ⊢ ∀x y. i16_mul x y = mk_i16 (i16_to_int x * i16_to_int y)
   
   [i16_neg_def]  Definition
      
      ⊢ ∀x. i16_neg x = mk_i16 (-i16_to_int x)
   
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
   
   [i32_ge_def]  Definition
      
      ⊢ ∀x y. i32_ge x y ⇔ i32_to_int x ≥ i32_to_int y
   
   [i32_gt_def]  Definition
      
      ⊢ ∀x y. i32_gt x y ⇔ i32_to_int x > i32_to_int y
   
   [i32_le_def]  Definition
      
      ⊢ ∀x y. i32_le x y ⇔ i32_to_int x ≤ i32_to_int y
   
   [i32_lt_def]  Definition
      
      ⊢ ∀x y. i32_lt x y ⇔ i32_to_int x < i32_to_int y
   
   [i32_max_def]  Definition
      
      ⊢ i32_max = 2147483647
   
   [i32_min_def]  Definition
      
      ⊢ i32_min = -2147483648
   
   [i32_mul_def]  Definition
      
      ⊢ ∀x y. i32_mul x y = mk_i32 (i32_to_int x * i32_to_int y)
   
   [i32_neg_def]  Definition
      
      ⊢ ∀x. i32_neg x = mk_i32 (-i32_to_int x)
   
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
   
   [i64_ge_def]  Definition
      
      ⊢ ∀x y. i64_ge x y ⇔ i64_to_int x ≥ i64_to_int y
   
   [i64_gt_def]  Definition
      
      ⊢ ∀x y. i64_gt x y ⇔ i64_to_int x > i64_to_int y
   
   [i64_le_def]  Definition
      
      ⊢ ∀x y. i64_le x y ⇔ i64_to_int x ≤ i64_to_int y
   
   [i64_lt_def]  Definition
      
      ⊢ ∀x y. i64_lt x y ⇔ i64_to_int x < i64_to_int y
   
   [i64_max_def]  Definition
      
      ⊢ i64_max = 9223372036854775807
   
   [i64_min_def]  Definition
      
      ⊢ i64_min = -9223372036854775808
   
   [i64_mul_def]  Definition
      
      ⊢ ∀x y. i64_mul x y = mk_i64 (i64_to_int x * i64_to_int y)
   
   [i64_neg_def]  Definition
      
      ⊢ ∀x. i64_neg x = mk_i64 (-i64_to_int x)
   
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
   
   [i8_ge_def]  Definition
      
      ⊢ ∀x y. i8_ge x y ⇔ i8_to_int x ≥ i8_to_int y
   
   [i8_gt_def]  Definition
      
      ⊢ ∀x y. i8_gt x y ⇔ i8_to_int x > i8_to_int y
   
   [i8_le_def]  Definition
      
      ⊢ ∀x y. i8_le x y ⇔ i8_to_int x ≤ i8_to_int y
   
   [i8_lt_def]  Definition
      
      ⊢ ∀x y. i8_lt x y ⇔ i8_to_int x < i8_to_int y
   
   [i8_max_def]  Definition
      
      ⊢ i8_max = 127
   
   [i8_min_def]  Definition
      
      ⊢ i8_min = -128
   
   [i8_mul_def]  Definition
      
      ⊢ ∀x y. i8_mul x y = mk_i8 (i8_to_int x * i8_to_int y)
   
   [i8_neg_def]  Definition
      
      ⊢ ∀x. i8_neg x = mk_i8 (-i8_to_int x)
   
   [i8_rem_def]  Definition
      
      ⊢ ∀x y.
          i8_rem x y =
          if i8_to_int y = 0 then Fail Failure
          else mk_i8 (int_rem (i8_to_int x) (i8_to_int y))
   
   [i8_sub_def]  Definition
      
      ⊢ ∀x y. i8_sub x y = mk_i8 (i8_to_int x − i8_to_int y)
   
   [int_rem_def]  Definition
      
      ⊢ ∀x y.
          int_rem x y =
          if 0 ≤ x ∧ 0 ≤ y ∨ x < 0 ∧ y < 0 then x % y else -(x % y)
   
   [is_diverge_def]  Definition
      
      ⊢ ∀r. is_diverge r ⇔
            case r of Return v2 => F | Fail v3 => F | Diverge => T
   
   [isize_add_def]  Definition
      
      ⊢ ∀x y. isize_add x y = mk_isize (isize_to_int x + isize_to_int y)
   
   [isize_div_def]  Definition
      
      ⊢ ∀x y.
          isize_div x y =
          if isize_to_int y = 0 then Fail Failure
          else mk_isize (isize_to_int x / isize_to_int y)
   
   [isize_ge_def]  Definition
      
      ⊢ ∀x y. isize_ge x y ⇔ isize_to_int x ≥ isize_to_int y
   
   [isize_gt_def]  Definition
      
      ⊢ ∀x y. isize_gt x y ⇔ isize_to_int x > isize_to_int y
   
   [isize_le_def]  Definition
      
      ⊢ ∀x y. isize_le x y ⇔ isize_to_int x ≤ isize_to_int y
   
   [isize_lt_def]  Definition
      
      ⊢ ∀x y. isize_lt x y ⇔ isize_to_int x < isize_to_int y
   
   [isize_mul_def]  Definition
      
      ⊢ ∀x y. isize_mul x y = mk_isize (isize_to_int x * isize_to_int y)
   
   [isize_neg_def]  Definition
      
      ⊢ ∀x. isize_neg x = mk_isize (-isize_to_int x)
   
   [isize_rem_def]  Definition
      
      ⊢ ∀x y.
          isize_rem x y =
          if isize_to_int y = 0 then Fail Failure
          else mk_isize (int_rem (isize_to_int x) (isize_to_int y))
   
   [isize_sub_def]  Definition
      
      ⊢ ∀x y. isize_sub x y = mk_isize (isize_to_int x − isize_to_int y)
   
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
        ∀f f1 v. result_CASE Diverge f f1 v = v
   
   [result_size_def]  Definition
      
      ⊢ (∀f a. result_size f (Return a) = 1 + f a) ∧
        (∀f a. result_size f (Fail a) = 1 + error_size a) ∧
        ∀f. result_size f Diverge = 0
   
   [return_def]  Definition
      
      ⊢ ∀x. return x = Return x
   
   [u128_add_def]  Definition
      
      ⊢ ∀x y. u128_add x y = mk_u128 (u128_to_int x + u128_to_int y)
   
   [u128_div_def]  Definition
      
      ⊢ ∀x y.
          u128_div x y =
          if u128_to_int y = 0 then Fail Failure
          else mk_u128 (u128_to_int x / u128_to_int y)
   
   [u128_ge_def]  Definition
      
      ⊢ ∀x y. u128_ge x y ⇔ u128_to_int x ≥ u128_to_int y
   
   [u128_gt_def]  Definition
      
      ⊢ ∀x y. u128_gt x y ⇔ u128_to_int x > u128_to_int y
   
   [u128_le_def]  Definition
      
      ⊢ ∀x y. u128_le x y ⇔ u128_to_int x ≤ u128_to_int y
   
   [u128_lt_def]  Definition
      
      ⊢ ∀x y. u128_lt x y ⇔ u128_to_int x < u128_to_int y
   
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
   
   [u16_ge_def]  Definition
      
      ⊢ ∀x y. u16_ge x y ⇔ u16_to_int x ≥ u16_to_int y
   
   [u16_gt_def]  Definition
      
      ⊢ ∀x y. u16_gt x y ⇔ u16_to_int x > u16_to_int y
   
   [u16_le_def]  Definition
      
      ⊢ ∀x y. u16_le x y ⇔ u16_to_int x ≤ u16_to_int y
   
   [u16_lt_def]  Definition
      
      ⊢ ∀x y. u16_lt x y ⇔ u16_to_int x < u16_to_int y
   
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
   
   [u32_ge_def]  Definition
      
      ⊢ ∀x y. u32_ge x y ⇔ u32_to_int x ≥ u32_to_int y
   
   [u32_gt_def]  Definition
      
      ⊢ ∀x y. u32_gt x y ⇔ u32_to_int x > u32_to_int y
   
   [u32_le_def]  Definition
      
      ⊢ ∀x y. u32_le x y ⇔ u32_to_int x ≤ u32_to_int y
   
   [u32_lt_def]  Definition
      
      ⊢ ∀x y. u32_lt x y ⇔ u32_to_int x < u32_to_int y
   
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
   
   [u64_ge_def]  Definition
      
      ⊢ ∀x y. u64_ge x y ⇔ u64_to_int x ≥ u64_to_int y
   
   [u64_gt_def]  Definition
      
      ⊢ ∀x y. u64_gt x y ⇔ u64_to_int x > u64_to_int y
   
   [u64_le_def]  Definition
      
      ⊢ ∀x y. u64_le x y ⇔ u64_to_int x ≤ u64_to_int y
   
   [u64_lt_def]  Definition
      
      ⊢ ∀x y. u64_lt x y ⇔ u64_to_int x < u64_to_int y
   
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
   
   [u8_ge_def]  Definition
      
      ⊢ ∀x y. u8_ge x y ⇔ u8_to_int x ≥ u8_to_int y
   
   [u8_gt_def]  Definition
      
      ⊢ ∀x y. u8_gt x y ⇔ u8_to_int x > u8_to_int y
   
   [u8_le_def]  Definition
      
      ⊢ ∀x y. u8_le x y ⇔ u8_to_int x ≤ u8_to_int y
   
   [u8_lt_def]  Definition
      
      ⊢ ∀x y. u8_lt x y ⇔ u8_to_int x < u8_to_int y
   
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
   
   [usize_add_def]  Definition
      
      ⊢ ∀x y. usize_add x y = mk_usize (usize_to_int x + usize_to_int y)
   
   [usize_div_def]  Definition
      
      ⊢ ∀x y.
          usize_div x y =
          if usize_to_int y = 0 then Fail Failure
          else mk_usize (usize_to_int x / usize_to_int y)
   
   [usize_ge_def]  Definition
      
      ⊢ ∀x y. usize_ge x y ⇔ usize_to_int x ≥ usize_to_int y
   
   [usize_gt_def]  Definition
      
      ⊢ ∀x y. usize_gt x y ⇔ usize_to_int x > usize_to_int y
   
   [usize_le_def]  Definition
      
      ⊢ ∀x y. usize_le x y ⇔ usize_to_int x ≤ usize_to_int y
   
   [usize_lt_def]  Definition
      
      ⊢ ∀x y. usize_lt x y ⇔ usize_to_int x < usize_to_int y
   
   [usize_mul_def]  Definition
      
      ⊢ ∀x y. usize_mul x y = mk_usize (usize_to_int x * usize_to_int y)
   
   [usize_rem_def]  Definition
      
      ⊢ ∀x y.
          usize_rem x y =
          if usize_to_int y = 0 then Fail Failure
          else mk_usize (int_rem (usize_to_int x) (usize_to_int y))
   
   [usize_sub_def]  Definition
      
      ⊢ ∀x y. usize_sub x y = mk_usize (usize_to_int x − usize_to_int y)
   
   [vec_index_back_def]  Definition
      
      ⊢ ∀v i.
          vec_index_back v i =
          if usize_to_int i < usize_to_int (vec_len v) then Return ()
          else Fail Failure
   
   [vec_index_def]  Definition
      
      ⊢ ∀v i. vec_index v i = index (usize_to_int i) (vec_to_list v)
   
   [vec_index_fwd_def]  Definition
      
      ⊢ ∀v i.
          vec_index_fwd v i =
          if usize_to_int i ≤ usize_to_int (vec_len v) then
            Return (vec_index v i)
          else Fail Failure
   
   [vec_index_mut_back_def]  Definition
      
      ⊢ ∀v i x.
          vec_index_mut_back v i x =
          if usize_to_int i ≤ usize_to_int (vec_len v) then
            Return (vec_update v i x)
          else Fail Failure
   
   [vec_index_mut_fwd_def]  Definition
      
      ⊢ ∀v i.
          vec_index_mut_fwd v i =
          if usize_to_int i ≤ usize_to_int (vec_len v) then
            Return (vec_index v i)
          else Fail Failure
   
   [vec_insert_back_def]  Definition
      
      ⊢ ∀v i x.
          vec_insert_back v i x =
          if usize_to_int i < usize_to_int (vec_len v) then
            Return (vec_update v i x)
          else Fail Failure
   
   [vec_len_def]  Definition
      
      ⊢ ∀v. vec_len v = int_to_usize (len (vec_to_list v))
   
   [vec_new_def]  Definition
      
      ⊢ vec_new = mk_vec []
   
   [vec_push_back_def]  Definition
      
      ⊢ ∀v x.
          vec_push_back v x =
          if usize_to_int (vec_len v) < usize_max then
            Return (mk_vec (vec_to_list v ⧺ [x]))
          else Fail Failure
   
   [vec_update_def]  Definition
      
      ⊢ ∀v i x.
          vec_update v i x =
          mk_vec (update (vec_to_list v) (usize_to_int i) x)
   
   [bind_return_fail_div_eq]  Theorem
      
      ⊢ monad_bind (Return x) f = f x ∧ monad_bind (Fail e) f = Fail e ∧
        monad_bind Diverge f = Diverge
   
   [datatype_error]  Theorem
      
      ⊢ DATATYPE (error Failure)
   
   [datatype_result]  Theorem
      
      ⊢ DATATYPE (result Return Fail Diverge)
   
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
   
   [i128_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i128_i128_to_int] []
      ⊢ ∀x y. x = y ⇔ i128_to_int x = i128_to_int y
   
   [i128_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i128_to_int_int_to_i128, usize_bounds] []
      ⊢ ∀x y.
          i128_min ≤ i128_to_int x * i128_to_int y ⇒
          i128_to_int x * i128_to_int y ≤ i128_max ⇒
          ∃z. i128_mul x y = Return z ∧
              i128_to_int z = i128_to_int x * i128_to_int y
   
   [i128_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: i128_to_int_int_to_i128, isize_bounds]
      []
      ⊢ ∀x y.
          i128_min ≤ -i128_to_int x ⇒
          -i128_to_int x ≤ i128_max ⇒
          ∃y. i128_neg x = Return y ∧ i128_to_int y = -i128_to_int x
   
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
   
   [i128_to_int_int_to_i128_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, i128_to_int_int_to_i128, isize_bounds] []
      ⊢ ∀n. i128_to_int (int_to_i128 n) =
            if i128_min ≤ n ∧ n ≤ i128_max then n
            else i128_to_int (int_to_i128 n)
   
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
   
   [i16_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i16_i16_to_int] []
      ⊢ ∀x y. x = y ⇔ i16_to_int x = i16_to_int y
   
   [i16_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i16_to_int_int_to_i16, usize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ i16_to_int x * i16_to_int y ⇒
          i16_to_int x * i16_to_int y ≤ i16_max ⇒
          ∃z. i16_mul x y = Return z ∧
              i16_to_int z = i16_to_int x * i16_to_int y
   
   [i16_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: i16_to_int_int_to_i16, isize_bounds] []
      ⊢ ∀x y.
          i16_min ≤ -i16_to_int x ⇒
          -i16_to_int x ≤ i16_max ⇒
          ∃y. i16_neg x = Return y ∧ i16_to_int y = -i16_to_int x
   
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
   
   [i16_to_int_int_to_i16_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, i16_to_int_int_to_i16, isize_bounds] []
      ⊢ ∀n. i16_to_int (int_to_i16 n) =
            if i16_min ≤ n ∧ n ≤ i16_max then n
            else i16_to_int (int_to_i16 n)
   
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
   
   [i32_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i32_i32_to_int] []
      ⊢ ∀x y. x = y ⇔ i32_to_int x = i32_to_int y
   
   [i32_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i32_to_int_int_to_i32, usize_bounds] []
      ⊢ ∀x y.
          i32_min ≤ i32_to_int x * i32_to_int y ⇒
          i32_to_int x * i32_to_int y ≤ i32_max ⇒
          ∃z. i32_mul x y = Return z ∧
              i32_to_int z = i32_to_int x * i32_to_int y
   
   [i32_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: i32_to_int_int_to_i32, isize_bounds] []
      ⊢ ∀x y.
          i32_min ≤ -i32_to_int x ⇒
          -i32_to_int x ≤ i32_max ⇒
          ∃y. i32_neg x = Return y ∧ i32_to_int y = -i32_to_int x
   
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
   
   [i32_to_int_int_to_i32_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, i32_to_int_int_to_i32, isize_bounds] []
      ⊢ ∀n. i32_to_int (int_to_i32 n) =
            if i32_min ≤ n ∧ n ≤ i32_max then n
            else i32_to_int (int_to_i32 n)
   
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
   
   [i64_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i64_i64_to_int] []
      ⊢ ∀x y. x = y ⇔ i64_to_int x = i64_to_int y
   
   [i64_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i64_to_int_int_to_i64, usize_bounds] []
      ⊢ ∀x y.
          i64_min ≤ i64_to_int x * i64_to_int y ⇒
          i64_to_int x * i64_to_int y ≤ i64_max ⇒
          ∃z. i64_mul x y = Return z ∧
              i64_to_int z = i64_to_int x * i64_to_int y
   
   [i64_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: i64_to_int_int_to_i64, isize_bounds] []
      ⊢ ∀x y.
          i64_min ≤ -i64_to_int x ⇒
          -i64_to_int x ≤ i64_max ⇒
          ∃y. i64_neg x = Return y ∧ i64_to_int y = -i64_to_int x
   
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
   
   [i64_to_int_int_to_i64_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, i64_to_int_int_to_i64, isize_bounds] []
      ⊢ ∀n. i64_to_int (int_to_i64 n) =
            if i64_min ≤ n ∧ n ≤ i64_max then n
            else i64_to_int (int_to_i64 n)
   
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
   
   [i8_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i8_i8_to_int] []
      ⊢ ∀x y. x = y ⇔ i8_to_int x = i8_to_int y
   
   [i8_mul_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: isize_bounds, i8_to_int_int_to_i8, usize_bounds] []
      ⊢ ∀x y.
          i8_min ≤ i8_to_int x * i8_to_int y ⇒
          i8_to_int x * i8_to_int y ≤ i8_max ⇒
          ∃z. i8_mul x y = Return z ∧
              i8_to_int z = i8_to_int x * i8_to_int y
   
   [i8_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: i8_to_int_int_to_i8, isize_bounds] []
      ⊢ ∀x y.
          i8_min ≤ -i8_to_int x ⇒
          -i8_to_int x ≤ i8_max ⇒
          ∃y. i8_neg x = Return y ∧ i8_to_int y = -i8_to_int x
   
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
   
   [i8_to_int_int_to_i8_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, i8_to_int_int_to_i8, isize_bounds] []
      ⊢ ∀n. i8_to_int (int_to_i8 n) =
            if i8_min ≤ n ∧ n ≤ i8_max then n else i8_to_int (int_to_i8 n)
   
   [index_update_diff]  Theorem
      
      ⊢ ∀ls i j y. 0 ≤ i ⇒ i < len ls ⇒ index i (update ls i y) = y
   
   [index_update_same]  Theorem
      
      ⊢ ∀ls i j y.
          0 ≤ i ⇒
          i < len ls ⇒
          j < len ls ⇒
          j ≠ i ⇒
          index j (update ls i y) = index j ls
   
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
   
   [isize_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_isize_isize_to_int] []
      ⊢ ∀x y. x = y ⇔ isize_to_int x = isize_to_int y
   
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
   
   [isize_neg_eq]  Theorem
      
      [oracles: DISK_THM] [axioms: isize_to_int_int_to_isize, isize_bounds]
      []
      ⊢ ∀x y.
          isize_min ≤ -isize_to_int x ⇒
          -isize_to_int x ≤ isize_max ⇒
          ∃y. isize_neg x = Return y ∧ isize_to_int y = -isize_to_int x
   
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
   
   [isize_to_int_int_to_isize_i16_bounds]  Theorem
      
      [oracles: DISK_THM] [axioms: isize_to_int_int_to_isize, isize_bounds]
      []
      ⊢ ∀n. i16_min ≤ n ∧ n ≤ i16_max ⇒ isize_to_int (int_to_isize n) = n
   
   [isize_to_int_int_to_isize_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, isize_to_int_int_to_isize, isize_bounds] []
      ⊢ ∀n. isize_to_int (int_to_isize n) =
            if i16_min ≤ n ∧ n ≤ i16_max then n
            else isize_to_int (int_to_isize n)
   
   [len_update]  Theorem
      
      ⊢ ∀ls i y. len (update ls i y) = len ls
   
   [mk_isize_unfold]  Theorem
      
      [oracles: DISK_THM] [axioms: isize_bounds] []
      ⊢ ∀n. mk_isize n =
            if
              (i16_min ≤ n ∨ isize_min ≤ n) ∧ (n ≤ i16_max ∨ n ≤ isize_max)
            then
              Return (int_to_isize n)
            else Fail Failure
   
   [mk_usize_unfold]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_bounds] []
      ⊢ ∀n. mk_usize n =
            if 0 ≤ n ∧ (n ≤ u16_max ∨ n ≤ usize_max) then
              Return (int_to_usize n)
            else Fail Failure
   
   [mk_vec_unfold]  Theorem
      
      [oracles: DISK_THM] [axioms: mk_vec_axiom, usize_bounds] []
      ⊢ ∀l. vec_to_list (mk_vec l) =
            if len l ≤ u16_max then l else vec_to_list (mk_vec l)
   
   [num2error_11]  Theorem
      
      ⊢ ∀r r'. r < 1 ⇒ r' < 1 ⇒ (num2error r = num2error r' ⇔ r = r')
   
   [num2error_ONTO]  Theorem
      
      ⊢ ∀a. ∃r. a = num2error r ∧ r < 1
   
   [num2error_error2num]  Theorem
      
      ⊢ ∀a. num2error (error2num a) = a
   
   [num2error_thm]  Theorem
      
      ⊢ num2error 0 = Failure
   
   [pos_rem_pos_ineqs]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ int_rem x y ∧ int_rem x y < y
   
   [result_11]  Theorem
      
      ⊢ (∀a a'. Return a = Return a' ⇔ a = a') ∧
        ∀a a'. Fail a = Fail a' ⇔ a = a'
   
   [result_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn.
          (∀a. fn (Return a) = f0 a) ∧ (∀a. fn (Fail a) = f1 a) ∧
          fn Diverge = f2
   
   [result_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 v.
          M = M' ∧ (∀a. M' = Return a ⇒ f a = f' a) ∧
          (∀a. M' = Fail a ⇒ f1 a = f1' a) ∧ (M' = Diverge ⇒ v = v') ⇒
          result_CASE M f f1 v = result_CASE M' f' f1' v'
   
   [result_case_eq]  Theorem
      
      ⊢ result_CASE x f f1 v = v' ⇔
        (∃a. x = Return a ∧ f a = v') ∨ (∃e. x = Fail e ∧ f1 e = v') ∨
        x = Diverge ∧ v = v'
   
   [result_distinct]  Theorem
      
      ⊢ (∀a' a. Return a ≠ Fail a') ∧ (∀a. Return a ≠ Diverge) ∧
        ∀a. Fail a ≠ Diverge
   
   [result_induction]  Theorem
      
      ⊢ ∀P. (∀a. P (Return a)) ∧ (∀e. P (Fail e)) ∧ P Diverge ⇒ ∀r. P r
   
   [result_nchotomy]  Theorem
      
      ⊢ ∀rr. (∃a. rr = Return a) ∨ (∃e. rr = Fail e) ∨ rr = Diverge
   
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
   
   [u128_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u128_u128_to_int] []
      ⊢ ∀x y. x = y ⇔ u128_to_int x = u128_to_int y
   
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
   
   [u128_to_int_int_to_u128_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, u128_to_int_int_to_u128, isize_bounds] []
      ⊢ ∀n. u128_to_int (int_to_u128 n) =
            if 0 ≤ n ∧ n ≤ u128_max then n else u128_to_int (int_to_u128 n)
   
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
   
   [u16_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u16_u16_to_int] []
      ⊢ ∀x y. x = y ⇔ u16_to_int x = u16_to_int y
   
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
   
   [u16_to_int_int_to_u16_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, u16_to_int_int_to_u16, isize_bounds] []
      ⊢ ∀n. u16_to_int (int_to_u16 n) =
            if 0 ≤ n ∧ n ≤ u16_max then n else u16_to_int (int_to_u16 n)
   
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
   
   [u32_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u32_u32_to_int] []
      ⊢ ∀x y. x = y ⇔ u32_to_int x = u32_to_int y
   
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
   
   [u32_to_int_int_to_u32_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, u32_to_int_int_to_u32, isize_bounds] []
      ⊢ ∀n. u32_to_int (int_to_u32 n) =
            if 0 ≤ n ∧ n ≤ u32_max then n else u32_to_int (int_to_u32 n)
   
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
   
   [u64_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u64_u64_to_int] []
      ⊢ ∀x y. x = y ⇔ u64_to_int x = u64_to_int y
   
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
   
   [u64_to_int_int_to_u64_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, u64_to_int_int_to_u64, isize_bounds] []
      ⊢ ∀n. u64_to_int (int_to_u64 n) =
            if 0 ≤ n ∧ n ≤ u64_max then n else u64_to_int (int_to_u64 n)
   
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
   
   [u8_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u8_u8_to_int] []
      ⊢ ∀x y. x = y ⇔ u8_to_int x = u8_to_int y
   
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
   
   [u8_to_int_int_to_u8_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, u8_to_int_int_to_u8, isize_bounds] []
      ⊢ ∀n. u8_to_int (int_to_u8 n) =
            if 0 ≤ n ∧ n ≤ u8_max then n else u8_to_int (int_to_u8 n)
   
   [update_len]  Theorem
      
      ⊢ ∀ls i y. len (update ls i y) = len ls
   
   [update_spec]  Theorem
      
      ⊢ ∀ls i y.
          len (update ls i y) = len ls ∧
          (0 ≤ i ⇒
           i < len ls ⇒
           index i (update ls i y) = y ∧
           ∀j. j < len ls ⇒ j ≠ i ⇒ index j (update ls i y) = index j ls)
   
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
   
   [usize_eq_equiv]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_usize_usize_to_int] []
      ⊢ ∀x y. x = y ⇔ usize_to_int x = usize_to_int y
   
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
   
   [usize_to_int_int_to_usize_u16_bounds]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_to_int_int_to_usize, usize_bounds]
      [] ⊢ ∀n. 0 ≤ n ∧ n ≤ u16_max ⇒ usize_to_int (int_to_usize n) = n
   
   [usize_to_int_int_to_usize_unfold]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_bounds, usize_to_int_int_to_usize, isize_bounds] []
      ⊢ ∀n. usize_to_int (int_to_usize n) =
            if 0 ≤ n ∧ n ≤ u16_max then n
            else usize_to_int (int_to_usize n)
   
   [vec_index_back_spec]  Theorem
      
      ⊢ ∀v i.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          vec_index_back v i = Return ()
   
   [vec_index_fwd_spec]  Theorem
      
      ⊢ ∀v i.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          vec_index_fwd v i = Return (vec_index v i)
   
   [vec_index_mut_back_spec]  Theorem
      
      ⊢ ∀v i x.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          vec_index_mut_back v i x = Return (vec_update v i x)
   
   [vec_index_mut_fwd_spec]  Theorem
      
      ⊢ ∀v i.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          vec_index_mut_fwd v i = Return (vec_index v i)
   
   [vec_insert_back_spec]  Theorem
      
      ⊢ ∀v i x.
          usize_to_int i < usize_to_int (vec_len v) ⇒
          vec_insert_back v i x = Return (vec_update v i x)
   
   [vec_len_spec]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_bounds, vec_to_list_num_bounds] []
      ⊢ ∀v. vec_len v = int_to_usize (len (vec_to_list v)) ∧
            0 ≤ len (vec_to_list v) ∧ len (vec_to_list v) ≤ usize_max
   
   [vec_len_vec_new]  Theorem
      
      [oracles: DISK_THM] [axioms: mk_vec_axiom, usize_bounds] []
      ⊢ vec_len vec_new = int_to_usize 0
   
   [vec_push_back_spec]  Theorem
      
      [oracles: DISK_THM]
      [axioms: usize_to_int_int_to_usize, mk_vec_axiom, usize_bounds,
       vec_to_list_num_bounds] []
      ⊢ ∀v x.
          usize_to_int (vec_len v) < usize_max ⇒
          ∃nv.
            vec_push_back v x = Return nv ∧
            vec_to_list nv = vec_to_list v ⧺ [x]
   
   [vec_push_back_unfold]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_bounds] []
      ⊢ ∀v x.
          vec_push_back v x =
          if
            usize_to_int (vec_len v) < u16_max ∨
            usize_to_int (vec_len v) < usize_max
          then
            Return (mk_vec (vec_to_list v ⧺ [x]))
          else Fail Failure
   
   [vec_to_list_int_bounds]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_bounds, vec_to_list_num_bounds] []
      ⊢ ∀v. 0 ≤ len (vec_to_list v) ∧ len (vec_to_list v) ≤ usize_max
   
   [vec_to_list_vec_new]  Theorem
      
      [oracles: DISK_THM] [axioms: mk_vec_axiom, usize_bounds] []
      ⊢ vec_to_list vec_new = []
   
   [vec_to_list_vec_update]  Theorem
      
      [oracles: DISK_THM]
      [axioms: mk_vec_axiom, usize_to_int_bounds,
       usize_to_int_int_to_usize, usize_bounds, vec_to_list_num_bounds] []
      ⊢ ∀v i x.
          vec_to_list (vec_update v i x) =
          update (vec_to_list v) (usize_to_int i) x
   
   [vec_update_eq]  Theorem
      
      [oracles: DISK_THM]
      [axioms: vec_to_list_num_bounds, usize_bounds,
       usize_to_int_int_to_usize, usize_to_int_bounds, mk_vec_axiom] []
      ⊢ ∀v i x.
          (let
             nv = vec_update v i x
           in
             len (vec_to_list nv) = len (vec_to_list v) ∧
             len (update (vec_to_list v) (usize_to_int i) x) =
             len (vec_to_list v) ∧
             (usize_to_int i < len (vec_to_list v) ⇒
              vec_index nv i = x ∧
              ∀j. usize_to_int j < usize_to_int (vec_len nv) ⇒
                  usize_to_int j ≠ usize_to_int i ⇒
                  vec_index nv j = vec_index v j))
   
   
*)
end
