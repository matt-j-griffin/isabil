theory Mem64_Elims
  imports Mem64
          Mem32_Elims
begin

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word64_elE: 
  assumes major: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<copyright> ext num \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<copyright>
  ext num \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<copyright> ext num \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<copyright>
  ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<copyright>
  ext num \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* Val v\<close>  
    obtains (minor) \<open>v = (ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  using major apply (intro minor)
  by (solve_expsE, unfold xtract64)+

lemma step_exps_concat_word64_el_num_ltE: 
  assumes major: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<copyright> ext num \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<copyright>
  ext num \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<copyright> ext num \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<copyright>
  ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<copyright>
  ext num \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (Val v)\<close>
      and num_lt: \<open>num < 2 ^ 64\<close>
    obtains (minor) \<open>v = (num \<Colon> 64)\<close>
  using major apply (intro minor)
  using step_exps_concat_word64_elE[where num = num and \<Delta> = \<Delta>]
  unfolding xtract_num_lt[OF num_lt] .

\<comment> \<open>The 64 bit solver scaffold\<close>


method solve_exp_mem64E uses add
  \<open>Method for deconstructing expression relations as premises (elimination rules)\<close> = (
  solve_expE_scaffold \<open>solve_exp_mem64E add: add\<close> \<open>solve_is_val64I add: add\<close> 
    \<open>solve_type64I add: add\<close> add: add
)

method solve_exps_succ64E_scaffold methods recurs solve_exp solve_is_val solve_type uses add = (
  (erule step_exps_concat_word64_el_num_ltE, (rule add | (((unfold power_numeral Num.pow.simps Num.sqr.simps)[1])?, linarith))) |
  (erule step_exps_concat_word64_elE) |

  (solve_exps_mem32E_scaffold recurs solve_exp solve_is_val solve_type add: add)
)

method solve_exps_succ64E uses add = (
  solve_exps_succ64E_scaffold \<open>solve_exps_succ64E add: add\<close> \<open>solve_exp_mem64E add: add\<close> 
    \<open>solve_is_val64I add: add\<close> \<open>solve_type64I add: add\<close> add: add
)

lemma step_exps_load_word64_elE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (Val v')\<close>
      and caveat: \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    obtains (minor) \<open>v' = (ext num\<^sub>v \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  using major caveat apply (intro minor)
  unfolding storage_el64_def storage_el32_def storage_el16_def
  by (solve_exps_mem32E add: step_exps_concat_word64_elE)

interpretation step_exps_load_word64_elE: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _.
    (\<And>\<Delta> v v' P. \<lbrakk>
      \<Delta> \<turnstile> (storage_el64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, el]:u64 \<leadsto>* (Val v'); 2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
      (v' = (ext v\<^sub>v \<sim> hi : 63 \<sim> lo : 0) \<Longrightarrow> P)
     \<rbrakk> \<Longrightarrow> P)\<close> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r 64
  apply standard
  using step_exps_load_word64_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] by blast

interpretation step_exps_load_word64_el64I: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _. 
    (\<And>\<Delta> v v' P. \<lbrakk>
      \<Delta> \<turnstile> (storage_el64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, el]:u64 \<leadsto>* (Val v'); 
      v' = (ext v\<^sub>v \<sim> hi : 63 \<sim> lo : 0) \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P)\<close> 64 64
  apply standard
  using step_exps_load_word64_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified] by blast
  
lemma step_exps_load_word64_el_num_ltE:
  assumes major: \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (Val v')\<close>
      and caveat: \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and num_lt: \<open>num\<^sub>v < 2 ^ 64\<close>
  obtains (minor) \<open>v' = (num\<^sub>v \<Colon> 64)\<close>
  using major caveat apply (intro minor)
  apply (erule step_exps_load_word64_elE[where num\<^sub>v=num\<^sub>v])
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_el_num_ltE: exp_val_word_fixed_sz_syntax \<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. 
  (\<And>\<Delta> v v' num\<^sub>v P. \<lbrakk>\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (Val v'); 
               2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; num\<^sub>v < 2 ^ 64; (v' = (num\<^sub>v \<Colon> 64) \<Longrightarrow> P)
  \<rbrakk> \<Longrightarrow> P)\<close> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
  apply standard
  using step_exps_load_word64_el_num_ltE by blast

lemma lt_2_64: \<open>2 < (64::nat)\<close> by simp

lemmas step_exps_load_word64_el64_num_ltE = step_exps_load_word64_el_num_ltE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, OF _ lt_2_64]

interpretation step_exps_load_word64_el64_num_ltE: exp_val_word_fixed_sz_syntax \<open>\<lambda>e\<^sub>a _ w\<^sub>a _. 
  (\<And>\<Delta> v v' P num\<^sub>v. \<lbrakk>\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (Val v'); num\<^sub>v < 2 ^ 64;
      (v' = (num\<^sub>v \<Colon> 64) \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close> 64
  apply (standard)
  using step_exps_load_word64_el64_num_ltE by blast
(*
lemma step_exps_load_word64_next_el64E: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (Val v')\<close>
      and neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close>
  obtains (minor) \<open>v' = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  using major addr_ok apply (intro minor)
  unfolding storage_el64_def storage_el32_def storage_el16_def
  by (solve_exps_succ64E add: addr_ok no_address_overlap_64_64[OF neq], clarify)

interpretation step_exps_load_word64_next_el64E: exp_val_word_fixed_sz_syntax_is_ok2 
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. 
  (\<And>\<Delta> v v' mem' num P. \<lbrakk>
    \<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v) [e\<^sub>1, el]:u64 \<leadsto>* (Val v'); 
    no_address_overlap_64_64 w\<^sub>2 w\<^sub>1;
    v' = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P)\<close> 64 64
  apply (standard)
  using step_exps_load_word64_next_el64E by blast


lemma step_exps_load_word64_next_el64_num_ltE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (Val v')\<close>
      and neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close>
      and num_lt: \<open>num < 2 ^ 64\<close>
      and minor: \<open>v' = (num \<Colon> 64) \<Longrightarrow> P\<close>
    shows P
  using major addr_ok apply (intro minor)
  using step_exps_load_word64_next_el64E[OF  _ neq addr_ok, where num=num]
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_next_el64_num_ltE: exp_val_word_fixed_sz_syntax_is_ok2 
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. 
  (\<And>\<Delta> v v' mem' num P. \<lbrakk>
    \<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v) [e\<^sub>1, el]:u64 \<leadsto>* (Val v'); 
    no_address_overlap_64_64 w\<^sub>2 w\<^sub>1; num < 2 ^ 64;
    v' = (num \<Colon> 64) \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P)\<close> 64 64
  apply (standard)
  using step_exps_load_word64_next_el64_num_ltE by blast
*)

lemma step_exps_store_word64_elE:
  assumes major: \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (Val v)\<close>
      and caveat: \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  obtains (minor) \<open>v = storage_el64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64)\<close>
proof (intro minor)
  show "v = storage_el64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64)"
    using major apply -

    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply simp
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply (erule step_exps_store_reduce_valE)
    apply (solve_exp_mem64E add: caveat)
    apply simp

    apply (solve_exps_mem32E add: caveat)
    unfolding storage_el64_def storage_el32_def storage_el16_def
    by simp
qed

interpretation step_exps_store_word64_elE: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta> v P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (Val v); v = storage_el64 v\<^sub>1 w\<^sub>2 v\<^sub>3 \<Longrightarrow> P
      \<rbrakk> \<Longrightarrow> P)\<close> 64
  apply (standard)
  using step_exps_store_word64_elE by blast
(*
\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word64_beI:
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_exps_succ64I, simp)+
  unfolding xtract64_56_0[symmetric] by solve_exps_succ64I

lemmas step_exps_load_word64_be64I = step_exps_load_word64_beI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word64_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_be64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  using assms apply -
  apply (solve_exps_succ64I, simp)+
  by solve_exps_succ64I

interpretation step_exps_store_word64_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  apply standard
  using step_exps_store_word64_beI by blast
*)
\<comment> \<open>The 64 bit solver scaffold\<close>
method solve_exps_mem64E_scaffold methods recurs solve_exp solve_is_val solve_type uses add = (
(*  (rule step_exps_load_word64_el64I.word.word step_exps_load_word64_el64I.succ.word
        step_exps_load_word64_el64I.plus.word) |

  (rule step_exps_load_word64_elI.word.word step_exps_load_word64_elI.succ.word 
        step_exps_load_word64_elI.plus.word 
        step_exps_load_word64_el64_num_ltI.word step_exps_load_word64_el64_num_ltI.succ
        step_exps_load_word64_el64_num_ltI.plus
        
        step_exps_load_word64_el_num_ltI.word step_exps_load_word64_el_num_ltI.succ
        step_exps_load_word64_el_num_ltI.plus; (rule add | linarith)) | 

  (rule step_exps_load_word64_next_el64_num_ltI.plus.plus; (rule add | linarith)) |

  (rule step_exps_load_word64_be64I) | (rule step_exps_load_word64_beI, linarith) |
  *)

  (erule step_exps_store_word64_elE.val.is_word2[rotated 3],
      prefer_last, solve_type,
      prefer_last, solve_is_wordI,
      prefer_last, solve_is_wordI,
      rewrite) |
   
  (solve_exps_succ64E_scaffold recurs solve_exp solve_is_val solve_type add: add)
)



method solve_exps_mem64E uses add = (
  solve_exps_mem64E_scaffold \<open>solve_exps_mem64E add: add\<close> \<open>solve_exp_mem64E add: add\<close>
    \<open>solve_is_val64I add: add\<close> \<open>solve_type64I add: add\<close> add: add
)

method solve_bil_mem64E uses add = (
  solve_bilE_scaffold \<open>solve_bil_mem64E add: add\<close> \<open>solve_exps_mem64E add: add\<close> add: add
)

context bil_syntax
begin

method solve_prog_mem64E uses add decoder = (
  solve_progE_scaffold \<open>solve_bil_mem64E add: add\<close> decoder: decoder
)

end

end
