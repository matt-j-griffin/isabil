theory Mem16_Intros
  imports Mem16
          "../OperationalSemantics/Program_Intros"
begin

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word16_elI: \<open>\<Delta> \<turnstile> ((
            ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8) \<copyright>
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
