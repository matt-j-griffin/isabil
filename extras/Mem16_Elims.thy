theory Mem16_Elims
  imports Mem16
          IsaBIL.Program_Elims
begin

lemma step_exps_concat_word16_elE:
  assumes major: \<open>\<Delta> \<turnstile> ((ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num\<^sub>v \<Colon> sz \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* Val v\<close>
  obtains (minor) \<open>v = (ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 0)\<close>
  apply (rule minor)
  unfolding xtract16_8_0[symmetric]
  using major apply -
  by solve_expsE

interpretation step_exps_concat_word16_elE: exp_val_word_sz_syntax \<open>\<lambda>e v w sz.
    (\<And>\<Delta> v' P. \<lbrakk>\<Delta> \<turnstile> ((ext e \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* Val v'; 
       v' = (ext v \<sim> hi : 15 \<sim> lo : 0) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  apply standard
  using step_exps_concat_word16_elE by blast

lemma step_exps_load_word16_elE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leadsto>* (Val v')\<close>
      and sz: \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> (* this could be eliminated *)
    obtains (minor) \<open>v' = ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 0\<close>
  apply (rule minor)
  using major sz apply -
  unfolding storage_el16_def
  by (solve_expsE add: step_exps_concat_word16_elE)

interpretation step_exps_load_word16_elE: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v v' P. \<lbrakk>\<Delta> \<turnstile> (storage_el16 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u16 \<leadsto>* (Val v'); 
       0 < sz\<^sub>1; v' = ext v\<^sub>2 \<sim> hi : 15 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  apply standard
  using step_exps_load_word16_elE by blast

lemmas step_exps_load_word16_el16E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_load_word16_el32E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word16_el64E = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word16_elE:
  assumes major: \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (Val v)\<close> 
      and caveat: \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    obtains (minor) \<open>v = (storage_el16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))\<close>
  using major apply (intro minor)
  apply (solve_expsE add: caveat)
  by (simp add: storage_constructor_exp_def storage_el16_def)

interpretation step_exps_store_word16_el16E: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3.
    (\<And>\<Delta> v P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (Val v); 
       v = (storage_el16 v\<^sub>1 w\<^sub>2 v\<^sub>3) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> 16
  apply standard
  using step_exps_store_word16_elE by blast

lemmas step_exps_store_word16_el16I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_store_word16_el32I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word16_el64I = step_exps_load_word16_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

method solve_exp_mem16E uses add
  \<open>Method for deconstructing expression relations as premises (elimination rules)\<close> = (
  solve_expE_scaffold \<open>solve_exp_mem16E add: add\<close> \<open>solve_is_val16I add: add\<close> 
    \<open>solve_type16I add: add\<close> add: add
)

method solve_exps_mem16E_scaffold methods recurs solve_exp solve_is_val solve_type uses add = (
  (erule step_exps_concat_word16_elE.is_word[rotated], defer_tac, solve_is_wordI, prefer_last, 
    rewrite?) |
  (erule step_exps_load_word16_elE.is_word2[rotated 2], defer_tac, defer_tac, solve_is_wordI, 
    solve_is_wordI, prefer_last, (solves \<open>rule add\<close> | linarith), prefer_last, rewrite?) |
  (erule step_exps_store_word16_el16E.is_word_val2[rotated 4], defer_tac, defer_tac, solve_is_wordI,
    solve_is_wordI, solve_is_val, prefer_last, solve_type, prefer_last, rewrite?) |

  solve_expsE_scaffold recurs solve_exp solve_is_val add: add
)

method solve_exps_mem16E uses add = 
  solves \<open>rule add\<close> | erule add | 
  solve_exps_mem16E_scaffold \<open>solve_exps_mem16E add: add\<close> \<open>solve_exp_mem16E add: add\<close> 
    \<open>solve_is_val16I add: add\<close>  \<open>solve_type16I add: add\<close> add: add

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
