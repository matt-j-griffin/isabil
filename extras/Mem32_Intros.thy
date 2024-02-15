theory Mem16_Intros
  imports "../ExpressionSemantics/Expressions_Intros"
begin



text \<open>Memory extension\<close>

(* TODO *)
lemma step_concat_extractI: \<open>\<Delta> \<turnstile> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) @ ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2) \<leadsto> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) \<cdot> ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2)\<close>
  unfolding xtract.simps by (rule step_concatI)

lemma step_exps_concat_extractI: \<open>\<Delta> \<turnstile> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) @ ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2) \<leadsto>* ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) \<cdot> ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2)\<close>
  unfolding xtract.simps by (rule step_exps_concatI)



lemma concat_2_bytes: \<open>\<lbrakk>0 < n; 0 < m\<rbrakk> \<Longrightarrow> ((ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + m + n - 1) \<sim> lo : (sz\<^sub>l\<^sub>o\<^sub>1 + n)) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + n - 1) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) = ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + m + n - 1) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1\<close>
  unfolding bv_concat.simps xtract.simps apply simp
  unfolding concat_bit_eq take_bit_of_nat push_bit_of_nat nat_int_add take_bit_take_bit apply simp
  unfolding push_bit_take_bit
  unfolding add.commute[of \<open>take_bit n _\<close>]
  apply (subst take_bit_plus_push_bit_drop_bit[of m n \<open>drop_bit sz\<^sub>l\<^sub>o\<^sub>1 num\<^sub>v\<close>])
  unfolding drop_bit_drop_bit add.commute[of sz\<^sub>l\<^sub>o\<^sub>1] add.commute[of m]
  by simp

lemma concat_2_8bytes: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 15) \<sim> lo : (sz\<^sub>l\<^sub>o\<^sub>1 + 8)) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 7) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) = ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 15) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1\<close>
  using concat_2_bytes[of 8 8 num\<^sub>v sz sz\<^sub>l\<^sub>o\<^sub>1] apply simp
  unfolding add.commute[of _ sz\<^sub>l\<^sub>o\<^sub>1] by simp

lemma concat_32_16: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 16\<close>
  using concat_2_8bytes[of num\<^sub>v sz 16] by simp

lemma concat_32_8: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 16) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 8\<close>
  using concat_2_bytes[of 8 16 num\<^sub>v sz 8] by simp

lemma concat_32_0: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 8) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 7 \<sim> lo : 0) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 0\<close>
  using concat_2_bytes[of 8 24 num\<^sub>v sz 0] by simp







lemma step_exps_concat_32elI:
  \<open>\<Delta> \<turnstile> ((((ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0) \<leadsto>* (num\<^sub>v \<Colon> 32)\<close>
  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_16

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_8

  unfolding concat_32_0[symmetric]



lemma step_exps_load_word32_elI: \<open>\<Delta> \<turnstile> (storage32 v num\<^sub>a 64 num\<^sub>v)[num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* (num\<^sub>v \<Colon> 32)\<close>
  unfolding succ.simps bv_plus.simps
  apply (rule step_exps_load_word_el.storageI, linarith)
  apply (rule step_exps_concat_rhsI)
  apply solve_expI
  apply (rule step_exps_concat_rhsI)
  apply solve_expI
  apply (rule step_exps_concat_rhsI)
  apply solve_expI
  apply (rule step_exps_concat_rhsI)
  apply solve_expI
  apply (rule step_exps_concat_lhs.extractI)

  unfolding succ.simps bv_plus.simps
  apply (rule step_load_word_el.storageI, linarith)
  unfolding succ.simps bv_plus.simps
  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_rhsI)
  apply solve_expI
  apply simp

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_rhsI)
  apply solve_expI

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_rhsI)
  apply solve_expI

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_load_word_el.storageI, linarith)
  unfolding succ.simps bv_plus.simps
  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_rhsI)
  apply solve_expI
  apply simp

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_rhsI)
  apply solve_expI

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply solve_expI

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_16

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_8

  using step_exps_concat_extractI

  apply (rule step_exps_concat_extractI)

   apply solve_expI

   
   apply solve_expI


  apply (rule step_exps_reflI[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule step_exps_reflI[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule step_exps_reflI[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps by simp
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule step_exps_reflI[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule step_exps_reflI[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    by (rule LOAD_BYTE_WORD)
  apply (rule step_exps_reflI[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule step_exps_reflI[of _ _ \<open>((nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4)) \<Colon> 8 + 8) \<cdot> (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule step_exps_reflI[of _ _ \<open>(nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4))))) \<Colon> 8 + 8 + 8) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps by (rule REFL_WORD)

lemma word8_refl_load_rev_ext_concat_word32: 
  assumes \<open>num < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* (num \<Colon> 32)\<close>
  apply (subgoal_tac \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* ((((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) \<cdot>
      ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
     ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8) \<cdot>
    ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0)\<close>)
  apply (metis assms extract_concat32)
  unfolding xtract.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  using word8_refl_load_rev_word32I by blast


end