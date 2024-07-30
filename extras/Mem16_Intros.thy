theory Mem16_Intros
  imports Mem16
          "../OperationalSemantics/Program_Intros"
begin
(* prelims *)

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



\<comment> \<open>Little Endian\<close>

lemmas xtract16_8_0[simp] = xtract_concat_consecutive[of 8 15 0, simplified]

lemma step_exps_concat_word16_elI: \<open>\<Delta> \<turnstile> ((
            ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8) @
            ext num\<^sub>v \<Colon> 16 \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* (ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 0)\<close>  
  apply (unfold xtract16_8_0[symmetric])
  by (solve_expsI)

method solve_exps_mem16I_scaffold methods recurs solve_exp solve_type = (
  rule step_exps_concat_word16_elI |
  solve_expsI_scaffold recurs solve_exp solve_type
)

method solve_exps_mem16I = solve_exps_mem16I_scaffold solve_exps_mem16I solve_expI solve_typeI

lemma step_exps_load_word16_elI: 
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leadsto>* (ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 0)\<close>
  using assms apply -
  by solve_exps_mem16I

lemmas step_exps_load_word16_el16I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_load_word16_el32I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word16_el64I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]


lemma step_exps_store_word16_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (storage_el16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))\<close>
  using assms apply -
  apply (solve_expsI, simp)+
  by solve_expsI


interpretation step_exps_store_word16_el16I: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el16 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 16
  apply standard
  using step_exps_store_word16_elI by blast


lemmas step_exps_store_word16_el16I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_store_word16_el32I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word16_el64I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word16_beI: 
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u16 \<leadsto>* (ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_expsI, simp)+
  unfolding xtract16_8_0[symmetric] by solve_expsI


lemma step_exps_store_word16_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (storage_be16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))\<close>
  using assms apply -
  apply (solve_expsI, simp)+
  by solve_expsI

interpretation step_exps_store_word16_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be16 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 16
  apply standard
  using step_exps_store_word16_beI by blast

end
