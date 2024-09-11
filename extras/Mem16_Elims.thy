theory Mem16_Elims
  imports Mem16
          "../OperationalSemantics/Program_Elims"
begin

lemma step_exps_concat_word16_elE:
  assumes major: \<open>\<Delta> \<turnstile> ((ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num\<^sub>v \<Colon> 16 \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* Val v\<close>
      and minor: \<open>v = (ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 0) \<Longrightarrow> P\<close>
    shows P
  apply (rule minor)
  unfolding xtract16_8_0[symmetric]
  using major apply -
  by solve_expsE
  

method solve_exps_mem16E_scaffold methods recurs solve_exp solve_type = (
  erulel rules: step_exps_concat_word16_elE |
  solve_expsE_scaffold recurs solve_exp
)

method solve_exps_mem16E = solve_exps_mem16E_scaffold solve_exps_mem16E solve_expE solve_typeI


lemma step_exps_load_word16_elE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leadsto>* (Val v)\<close>
      and sz: \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and minor: \<open>v = ext num\<^sub>v \<Colon> 16 \<sim> hi : 15 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  apply (rule minor)
  using major sz apply -
  by solve_exps_mem16E

lemmas step_exps_load_word16_el16E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_load_word16_el32E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word16_el64E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word16_elE:
  assumes major: \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (Val v)\<close> 
      and caveat: \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and minor: \<open>v = (storage_el16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16)) \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (intro minor)
  apply solve_expsE
  by (simp add: storage_constructor_exp_def)

interpretation step_exps_store_word16_el16E: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3.
    (\<And>\<Delta> v P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (Val v); 
       v = (storage_el16 v\<^sub>1 w\<^sub>2 v\<^sub>3) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> 16
  apply standard
  using step_exps_store_word16_elE by blast

lemmas step_exps_store_word16_el16I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_store_word16_el32I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word16_el64I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]
(*
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
*)
end
