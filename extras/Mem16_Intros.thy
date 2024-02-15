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
  sorry


lemma step_exps_load_word16_elI: \<open>\<Delta> \<turnstile> (storage16 v num\<^sub>a 64 num\<^sub>v)[num\<^sub>a \<Colon> 64, el]:u16 \<leadsto>* (num\<^sub>v \<Colon> 16)\<close>
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

end