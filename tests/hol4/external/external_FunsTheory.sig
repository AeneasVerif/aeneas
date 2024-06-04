signature external_FunsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val custom_swap_back_def : thm
    val custom_swap_fwd_def : thm
    val swap_back_def : thm
    val swap_fwd_def : thm
    val test_custom_swap_back_def : thm
    val test_custom_swap_fwd_def : thm
    val test_new_non_zero_u32_fwd_def : thm
    val test_swap_non_zero_fwd_def : thm
    val test_vec_fwd_def : thm
  
  val external_Funs_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [external_Opaque] Parent theory of "external_Funs"
   
   [custom_swap_back_def]  Definition
      
      ⊢ ∀x y st ret st0.
          custom_swap_back x y st ret st0 =
          do
            (st1,_) <- core_mem_swap_fwd x y st;
            (st2,_) <- core_mem_swap_back0 x y st st1;
            (_,y0) <- core_mem_swap_back1 x y st st2;
            Return (st0,ret,y0)
          od
   
   [custom_swap_fwd_def]  Definition
      
      ⊢ ∀x y st.
          custom_swap_fwd x y st =
          do
            (st0,_) <- core_mem_swap_fwd x y st;
            (st1,x0) <- core_mem_swap_back0 x y st st0;
            (st2,_) <- core_mem_swap_back1 x y st st1;
            Return (st2,x0)
          od
   
   [swap_back_def]  Definition
      
      ⊢ ∀x y st st0.
          swap_back x y st st0 =
          do
            (st1,_) <- core_mem_swap_fwd x y st;
            (st2,x0) <- core_mem_swap_back0 x y st st1;
            (_,y0) <- core_mem_swap_back1 x y st st2;
            Return (st0,x0,y0)
          od
   
   [swap_fwd_def]  Definition
      
      ⊢ ∀x y st.
          swap_fwd x y st =
          do
            (st0,_) <- core_mem_swap_fwd x y st;
            (st1,_) <- core_mem_swap_back0 x y st st0;
            (st2,_) <- core_mem_swap_back1 x y st st1;
            Return (st2,())
          od
   
   [test_custom_swap_back_def]  Definition
      
      ⊢ ∀x y st st0.
          test_custom_swap_back x y st st0 =
          custom_swap_back x y st (int_to_u32 1) st0
   
   [test_custom_swap_fwd_def]  Definition
      
      ⊢ ∀x y st.
          test_custom_swap_fwd x y st =
          do (st0,_) <- custom_swap_fwd x y st; Return (st0,()) od
   
   [test_new_non_zero_u32_fwd_def]  Definition
      
      ⊢ ∀x st.
          test_new_non_zero_u32_fwd x st =
          do
            (st0,opt) <- core_num_nonzero_non_zero_u32_new_fwd x st;
            core_option_option_unwrap_fwd opt st0
          od
   
   [test_swap_non_zero_fwd_def]  Definition
      
      ⊢ ∀x st.
          test_swap_non_zero_fwd x st =
          do
            (st0,_) <- swap_fwd x (int_to_u32 0) st;
            (st1,x0,_) <- swap_back x (int_to_u32 0) st st0;
            if x0 = int_to_u32 0 then Fail Failure else Return (st1,x0)
          od
   
   [test_vec_fwd_def]  Definition
      
      ⊢ test_vec_fwd =
        (let
           v = vec_new
         in
           monad_ignore_bind (vec_push_back v (int_to_u32 0)) (Return ()))
   
   
*)
end
