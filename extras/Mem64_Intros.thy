theory Mem64_Intros
  imports "../ExpressionSemantics/Expressions_Intros"
begin



text \<open>Memory extension\<close>

lemma xtract_concat_consecutive:
  assumes \<open>x2 > x3\<close> \<open>x3 > x4\<close>
    shows \<open>(ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x3) \<cdot> (ext num \<Colon> x1 \<sim> hi : x3 - 1 \<sim> lo : x4) = (ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x4)\<close>
unfolding xtract.simps bv_concat.simps proof auto
  have sz_simp1: \<open>(Suc (x2 - x3) + Suc (x3 - Suc x4)) = (Suc (x2 - x4))\<close>
    using assms by fastforce
  have sz_simp2: \<open>Suc (x3 - Suc x4) + x4 = x3\<close>
    using assms by fastforce
  show \<open>nat (concat_bit (Suc (x3 - Suc x4)) (int (take_bit (Suc (x3 - Suc x4)) (drop_bit x4 num)))
          (int (take_bit (Suc (x2 - x3)) (drop_bit x3 num)))) = take_bit (Suc (x2 - x4)) (drop_bit x4 num)\<close>
    using nat_concat_bit_take_bit_drop_bit2[of \<open>Suc (x3 - Suc x4)\<close> x4 num \<open>Suc (x2 - x3)\<close>, unfolded sz_simp1 sz_simp2]    
    by blast
next
  show \<open>Suc (x2 - x3 + (x3 - Suc x4)) = x2 - x4\<close>
    using assms by fastforce
qed

lemmas xtract64_48_el[simp] = xtract_concat_consecutive[of 56 63 48, simplified]
lemmas xtract64_40_el[simp] = xtract_concat_consecutive[of 48 63 40, simplified]
lemmas xtract64_32_el[simp] = xtract_concat_consecutive[of 40 63 32, simplified]
lemmas xtract64_24_el[simp] = xtract_concat_consecutive[of 32 63 24, simplified]
lemmas xtract64_16_el[simp] = xtract_concat_consecutive[of 24 63 16, simplified]
lemmas xtract64_8_el[simp]  = xtract_concat_consecutive[of 16 63 8, simplified]
lemmas xtract64_0_el[simp]  = xtract_concat_consecutive[of 8 63 0, simplified]
lemmas xtract64_15_0[simp]  = xtract_concat_consecutive[of 8 15 0, simplified]
lemmas xtract64_23_0[simp]  = xtract_concat_consecutive[of 16 23 0, simplified]
lemmas xtract64_31_0[simp]  = xtract_concat_consecutive[of 24 31 0, simplified]
lemmas xtract64_39_0[simp]  = xtract_concat_consecutive[of 32 39 0, simplified]
lemmas xtract64_47_0[simp]  = xtract_concat_consecutive[of 40 47 0, simplified]
lemmas xtract64_55_0[simp]  = xtract_concat_consecutive[of 48 55 0, simplified]
lemmas xtract64_63_0[simp]  = xtract_concat_consecutive[of 56 63 0, simplified]

lemmas xtract64_els = xtract64_48_el xtract64_40_el xtract64_32_el xtract64_24_el xtract64_16_el
                      xtract64_8_el  xtract64_0_el

lemma step_exps_concat_word64_elI: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) @ ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) @
  ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) @ ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) @
  ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) @ ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) @
  ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) @ ext num \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>  
  apply (solve_expsI simp: xtract64_els)
  by (unfold xtract64_els, unfold xtract64_0_el[symmetric], rule step_exps_concatI.xtract.xtract)

lemma step_exps_load_word64_elI: \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> 64) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  apply (solve_exps_intI \<open>rule step_exps_concat_word64_elI\<close>)
  apply simp
  by (solve_exps_intI \<open>rule step_exps_concat_word64_elI\<close>)

lemma step_exps_load_word64_beI: \<open>\<Delta> \<turnstile> (storage_be64 v (num\<^sub>a \<Colon> 64) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> 64, be]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  apply (solve_expsI, simp)+
  unfolding xtract64_63_0[symmetric] by solve_expsI

lemma nested_extract_within': 
  assumes  \<open>sz\<^sub>l\<^sub>o' \<le> sz\<^sub>h\<^sub>i'\<close> and \<open>sz\<^sub>h\<^sub>i' + sz\<^sub>l\<^sub>o \<le> sz\<^sub>h\<^sub>i\<close>
    shows \<open>(ext (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) \<sim> hi : sz\<^sub>h\<^sub>i' \<sim> lo : sz\<^sub>l\<^sub>o') = (ext num \<Colon> sz \<sim> hi : (sz\<^sub>h\<^sub>i' + sz\<^sub>l\<^sub>o) \<sim> lo : (sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o))\<close>
  using assms unfolding xtract.simps take_bit_drop_bit by auto

lemma nested_extract_within: 
  assumes \<open>sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o \<le> sz\<^sub>h\<^sub>i\<close>
    shows \<open>(ext (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) \<sim> hi : (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o) \<sim> lo : sz\<^sub>l\<^sub>o') = (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : (sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o))\<close>
  using assms using nested_extract_within'[where sz\<^sub>h\<^sub>i'= \<open>sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<close> and sz\<^sub>l\<^sub>o = sz\<^sub>l\<^sub>o and sz\<^sub>l\<^sub>o' = sz\<^sub>l\<^sub>o' and sz\<^sub>h\<^sub>i = sz\<^sub>h\<^sub>i and num = num and sz = sz]
  apply auto
  using add_le_imp_le_diff by blast



lemmas xtract_nested_63_8_55_8[simp]  = nested_extract_within [of  8  8 63, simplified]
lemmas xtract_nested_63_16_47_8[simp] = nested_extract_within [of  8 16 63, simplified]
lemmas xtract_nested_63_24_39_8[simp] = nested_extract_within [of  8 24 63, simplified]
lemmas xtract_nested_63_32_31_8[simp] = nested_extract_within [of  8 32 63, simplified]
lemmas xtract_nested_63_40_23_8[simp] = nested_extract_within [of  8 40 63, simplified]
lemmas xtract_nested_63_48_15_8[simp] = nested_extract_within [of  8 48 63, simplified]
lemmas xtract_nested_55_0_47_0[simp]  = nested_extract_within'[of  0 47  0 55, simplified]
lemmas xtract_nested_47_0_39_0[simp]  = nested_extract_within'[of  0 39  0 47, simplified]
lemmas xtract_nested_39_0_31_0[simp]  = nested_extract_within'[of  0 31  0 39, simplified]
lemmas xtract_nested_31_0_23_0[simp]  = nested_extract_within'[of  0 23  0 31, simplified]
lemmas xtract_nested_23_0_15_0[simp]  = nested_extract_within'[of  0 15  0 23, simplified]
lemmas xtract_nested_15_0_7_0[simp]   = nested_extract_within'[of  0  7  0 15, simplified]
lemmas xtract_nested_63_8_7_0[simp]   = nested_extract_within'[of  0  7  8 63,  simplified]
lemmas xtract_nested_63_16_7_0[simp]  = nested_extract_within'[of  0  7 16 63, simplified]
lemmas xtract_nested_63_24_7_0[simp]  = nested_extract_within'[of  0  7 24 63, simplified]
lemmas xtract_nested_63_32_7_0[simp]  = nested_extract_within'[of  0  7 32 63, simplified]
lemmas xtract_nested_63_40_7_0[simp]  = nested_extract_within'[of  0  7 40 63, simplified]
lemmas xtract_nested_63_48_7_0[simp]  = nested_extract_within'[of  0  7 48 63, simplified]
lemmas xtract_nested_55_0_55_48[simp] = nested_extract_within'[of 48 55  0 55, simplified]
lemmas xtract_nested_47_0_47_40[simp] = nested_extract_within'[of 40 47  0 47, simplified]
lemmas xtract_nested_39_0_39_32[simp] = nested_extract_within'[of 32 39  0 39, simplified]
lemmas xtract_nested_31_0_31_24[simp] = nested_extract_within'[of 24 31  0 31, simplified]
lemmas xtract_nested_23_0_23_16[simp] = nested_extract_within'[of 16 23  0 23, simplified]
lemmas xtract_nested_15_0_15_8[simp]  = nested_extract_within'[of  8 15  0 15, simplified]

lemma step_exps_store_word64_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_el64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  using assms apply -
  apply (solve_expsI, simp)+
  by solve_expsI

interpretation step_exps_store_word64_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  by (standard, rule step_exps_store_word64_elI)

lemma step_exps_store_word64_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_be64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  using assms apply -
  apply (solve_expsI, simp)+
  by solve_expsI

interpretation step_exps_store_word64_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  by (standard, rule step_exps_store_word64_beI)

text \<open>The 64bit solver\<close>

method solve_exps_64I = (
  rule step_exps_concat_word64_elI |

  (rule step_exps_store_word64_elI, solve_typeI) |
  (rule step_exps_store_word64_beI, solve_typeI) |

  (rule step_exps_load_word64_elI) |
  (rule step_exps_load_word64_beI)
)

method inv methods FF = (
  FF
)



end
