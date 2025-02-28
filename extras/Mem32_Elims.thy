theory Mem32_Elims
  imports Mem32
          Mem16_Elims
begin

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word32_elE: 
  assumes major: \<open>\<Delta> \<turnstile> ((((ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<copyright>
                   ext num \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) 
              \<leadsto>* (Val v)\<close>
    obtains (minor) \<open>v = ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0\<close>
  using major apply (intro minor)
  apply solve_exps_mem16E
  unfolding xtract32 .

lemma step_exps_cast64_concat32_elE:
  assumes major: \<open>\<Delta> \<turnstile> extend:64[
   (((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24)  \<copyright> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<copyright>
      ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8)  \<copyright> ext num \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0] \<leadsto>* (Val v)\<close>
      and caveat: \<open>num < 2 ^ 32\<close>
    obtains (minor) \<open>v = (num \<Colon> 64)\<close>
  using major apply (intro minor)
  apply (solve_exps_mem16E, unfold xtract32)+
  apply simp
  unfolding xtract_31_0_63_0[OF caveat] by solve_expsE

lemma step_exps_load_word32_elE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leadsto>* (Val v')\<close>
      and caveat: \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    obtains (minor) \<open>v' = (ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 0)\<close>
  using major caveat apply (intro minor)
  unfolding storage_el32_def storage_el16_def
  by (solve_exps_mem16E add: step_exps_concat_word32_elE)

lemmas step_exps_load_word32_el32I = step_exps_load_word32_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word32_el64I = step_exps_load_word32_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word32_elE:
  assumes major: \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (Val v)\<close>
      and caveat: \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    obtains (minor) \<open>v = storage_el32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32)\<close>
  using major apply (intro minor)
  apply (solve_exps_mem16E add: caveat)
  unfolding storage_el32_def storage_el16_def
  by simp

interpretation step_exps_store_word32_elE: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta> v P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (Val v);
          v = storage_el32 v\<^sub>1 w\<^sub>2 v\<^sub>3 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> 32
  apply standard
  using step_exps_store_word32_elE by blast
(*
lemmas step_exps_store_word32_el32I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word32_el64I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]
*)(*
\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word32_beI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leadsto>* (ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_exps_succ32E, simp)+
  unfolding xtract32_24_0[symmetric] by solve_exps_succ32I

lemma step_exps_store_word32_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (storage_be32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))\<close>
  using assms apply -
  apply (solve_exps_succ32I, simp)+
  by solve_exps_succ32I

interpretation step_exps_store_word32_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be32 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 32
  apply standard
  using step_exps_store_word32_beI by blast
*)
\<comment> \<open>The 64 bit solver scaffold\<close>


method solve_exp_mem32E uses add
  \<open>Method for deconstructing expression relations as premises (elimination rules)\<close> = (
  solve_expE_scaffold \<open>solve_exp_mem32E add: add\<close> \<open>solve_is_val32I add: add\<close> 
    \<open>solve_type32I add: add\<close> add: add
)

method solve_exps_mem32E_scaffold methods recurs solve_exp solve_is_val solve_type uses add = (
  (erule step_exps_concat_word32_elE) |

  (solve_exps_mem16E_scaffold recurs solve_exp solve_is_val solve_type add: add)
)

method solve_exps_mem32E uses add = (
  solves \<open>rule add\<close> | erule add | 
  solve_exps_mem32E_scaffold \<open>solve_exps_mem32E add: add\<close> \<open>solve_exp_mem32E add: add\<close>
    \<open>solve_is_val32I add: add\<close> \<open>solve_type32I add: add\<close>  add: add
)

method solve_bil_mem32E uses add = (
  solve_bilE_scaffold \<open>solve_bil_mem32E add: add\<close> \<open>solve_exps_mem32E add: add\<close>
)


context bil_syntax
begin

method solve_prog_mem32E uses add decoder = (
  solve_progE_scaffold \<open>solve_bil_mem32E add: add\<close> decoder: decoder
)

end

end
