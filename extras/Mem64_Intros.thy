theory Mem64_Intros
  imports Mem64
          Mem32_Intros
begin

(** TODO **)
lemma storage64_nat_simps[simp, exp_cast_simps]: 
    \<open>64 - 56 = (8::nat)\<close> \<open>56 - 48 = (8::nat)\<close> \<open>48 - 40 = (8::nat)\<close> \<open>40 - 32 = (8::nat)\<close>
    \<open>63 - 8 = (55::nat)\<close> \<open>55 - 8 = (47::nat)\<close> \<open>47 - 8 = (39::nat)\<close> \<open>39 - 8 = (31::nat)\<close>
    \<open>64 - 1 = (63::nat)\<close> \<open>56 - 1 = (55::nat)\<close> \<open>48 - 1 = (47::nat)\<close> \<open>40 - 1 = (39::nat)\<close>
    \<open>63 - 56 = (7::nat)\<close> \<open>55 - 48 = (7::nat)\<close> \<open>47 - 40 = (7::nat)\<close>  \<open>39 - 32 = (7::nat)\<close>
    \<open>Suc 63 = 64\<close> \<open>Suc 55 = 56\<close> \<open>Suc 47 = 48\<close> \<open>Suc 39 = 40\<close> \<open>Suc 31 = 32\<close>
  by auto (* after performing a store, attempt to unfold some nats *)

thm diff_zero[exp_cast_simps]

subsubsection \<open>Little Endian\<close>

lemma step_exps_concat_last_word64_elI: 
  \<open>\<Delta> \<turnstile> ((((((((ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<cdot> ext num \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<cdot> 
               ext num \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<cdot> ext num \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<cdot>
               ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot>
               ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num \<Colon> sz \<sim> hi : 7 \<sim> lo : 0) 
      \<leadsto>* (ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  unfolding xtract64_8_0[symmetric] xtract64[symmetric] by solve_exps_mem32I

interpretation step_exps_concat_last_word64_elI: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. \<Delta> \<turnstile> ((((((((ext e\<^sub>1 \<sim> hi : 63 \<sim> lo : 56) \<cdot> ext e\<^sub>1 \<sim> hi : 55 \<sim> lo : 48) \<cdot> 
               ext e\<^sub>1 \<sim> hi : 47 \<sim> lo : 40) \<cdot> ext e\<^sub>1 \<sim> hi : 39 \<sim> lo : 32) \<cdot>
               ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext e\<^sub>1 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
               ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e\<^sub>1 \<sim> hi : 7 \<sim> lo : 0) 
      \<leadsto>* (ext e\<^sub>1 \<sim> hi : 63 \<sim> lo : 0))\<close>
  apply unfold_locales
  using step_exps_concat_last_word64_elI by blast

lemma step_exps_concat_last_word64_el_lt_numI: 
  assumes num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> ((((((((ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<cdot> ext num \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<cdot> 
               ext num \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<cdot> ext num \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<cdot>
               ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot>
               ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num \<Colon> sz \<sim> hi : 7 \<sim> lo : 0) 
      \<leadsto>* (num \<Colon> 64)\<close>
  using step_exps_concat_last_word64_elI[where num = num]
  unfolding xtract_num_lt[OF num_lt] .

lemma step_exps_concat_word64_elI: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<copyright> ext num \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<copyright>
  ext num \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<copyright> ext num \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<copyright>
  ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<copyright>
  ext num \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  by (solve_exps_mem32I add: step_exps_concat_last_word64_elI)

interpretation step_exps_concat_word64_elI: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. \<Delta> \<turnstile> ((((((((
      ext e\<^sub>1 \<sim> hi : 63 \<sim> lo : 56) \<copyright> ext e\<^sub>1 \<sim> hi : 55 \<sim> lo : 48) \<copyright>
      ext e\<^sub>1 \<sim> hi : 47 \<sim> lo : 40) \<copyright> ext e\<^sub>1 \<sim> hi : 39 \<sim> lo : 32) \<copyright>
      ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext e\<^sub>1 \<sim> hi : 23 \<sim> lo : 16) \<copyright>
      ext e\<^sub>1 \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext e\<^sub>1 \<sim> hi :  7 \<sim> lo :  0) 
    \<leadsto>* (ext e\<^sub>1 \<sim> hi : 63 \<sim> lo : 0))\<close>
  apply unfold_locales
  using step_exps_concat_word64_elI by blast

lemma step_exps_concat_word64_el_num_ltI: 
  assumes num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) \<copyright> ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) \<copyright>
  ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) \<copyright> ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) \<copyright>
  ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) \<copyright>
  ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (num \<Colon> 64)\<close>  
  using step_exps_concat_word64_elI[where num = num and \<Delta> = \<Delta>]
  unfolding xtract_num_lt[OF num_lt] .

lemma step_exps_load_word64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  using assms apply -
  unfolding storage_el64_def
  by (solve_exps_mem32I add: step_exps_concat_last_word64_elI)


interpretation step_exps_load_word64_elI: exp_val_word_fixed_sz_syntax2 
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _. (\<And>\<Delta> v. 2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, el]:u64 \<leadsto>* (ext e\<^sub>v \<sim> hi : 63 \<sim> lo : 0))\<close>
  apply standard
  using step_exps_load_word64_elI by blast
  
lemma step_exps_load_word64_el_num_ltI: (* TODO might not be needed when the extract simplifier comes *)
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and num_lt: \<open>num\<^sub>v < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64)\<close>
  using step_exps_load_word64_elI[OF assms(1), where num\<^sub>v=num\<^sub>v]
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_el_num_ltI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>\<Delta> v num\<^sub>v. \<lbrakk>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; num\<^sub>v < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64))\<close> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
  apply standard
  using step_exps_load_word64_el_num_ltI by blast

lemma step_exps_load_word64_el64_num_ltI:
  assumes \<open>num\<^sub>v < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> 64) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64)\<close>
  apply (rule step_exps_load_word64_el_num_ltI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, OF _ assms])
  by linarith

lemma lt_2_64: \<open>2 < (64::nat)\<close> by simp

interpretation step_exps_load_word64_el64_num_ltI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>e\<^sub>a _ w\<^sub>a _. (\<And>\<Delta> v num\<^sub>v. \<lbrakk>num\<^sub>v < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64))\<close> 64
  apply standard
  using step_exps_load_word64_el_num_ltI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, OF lt_2_64] by blast


(*
lemma step_exps_load_word64_next_el64I: 
  assumes neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  unfolding xtract64[symmetric] xtract64_8_0[symmetric]
  apply (solve_exps_succ64I add: addr_ok no_address_overlap_64_64[OF neq])
  unfolding Val_simp_storage
  apply (solve_exps_succ64I add: addr_ok no_address_overlap_64_64[OF neq])

interpretation step_exps_load_word64_next_el64I: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta> v mem' num. \<lbrakk>no_address_overlap_64_64 w\<^sub>2 w\<^sub>1\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v)
             [e\<^sub>1, el]:u64 \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0))\<close> 64 64
  by (standard, rule step_exps_load_word64_next_el64I)

lemma step_exps_load_word64_next_el64_num_ltI: 
  assumes neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close> 
      and num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (num \<Colon> 64)\<close>
  using step_exps_load_word64_next_el64I[OF neq addr_ok, where num=num]
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_next_el64_num_ltI: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta> v mem' num. \<lbrakk>no_address_overlap_64_64 w\<^sub>2 w\<^sub>1; num < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v)
             [e\<^sub>1, el]:u64 \<leadsto>* (num \<Colon> 64))\<close> 64 64
  by (standard, rule step_exps_load_word64_next_el64_num_ltI)
*)

\<comment> \<open>Load Next\<close>

lemma step_exps_load_next_byte64_elI: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> 
               \<open>succ2 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ3 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
               \<open>succ4 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ5 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
               \<open>succ6 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ7 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: nxt neq)

interpretation step_exps_load_next_byte64_elI: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; succ4 w \<noteq> w\<^sub>1; succ5 w \<noteq> w\<^sub>1; 
      succ6 w \<noteq> w\<^sub>1; succ7 w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk> 
          \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte64_elI by blast 

\<comment> \<open>Load Bytes\<close>

lemma step_exps_load_byte1_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 7 \<sim> lo : 0)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte1_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 7 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_byte1_64_elI by blast

lemma step_exps_load_byte2_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 15 \<sim> lo : 8)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte2_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 15 \<sim> lo : 8)\<close>
  apply unfold_locales
  using step_exps_load_byte2_64_elI by blast

lemma step_exps_load_byte3_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ2 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 23 \<sim> lo : 16)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte3_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ2 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 23 \<sim> lo : 16)\<close>
  apply unfold_locales
  using step_exps_load_byte3_64_elI by blast

lemma step_exps_load_byte4_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ3 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 31 \<sim> lo : 24)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte4_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ3 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 31 \<sim> lo : 24)\<close>
  apply unfold_locales
  using step_exps_load_byte4_64_elI by blast

lemma step_exps_load_byte5_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ4 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 39 \<sim> lo : 32)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte5_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ4 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 39 \<sim> lo : 32)\<close>
  apply unfold_locales
  using step_exps_load_byte5_64_elI by blast

lemma step_exps_load_byte6_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ5 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 47 \<sim> lo : 40)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte6_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ5 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 47 \<sim> lo : 40)\<close>
  apply unfold_locales
  using step_exps_load_byte6_64_elI by blast

lemma step_exps_load_byte7_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ6 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 55 \<sim> lo : 48)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte7_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ6 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 55 \<sim> lo : 48)\<close>
  apply unfold_locales
  using step_exps_load_byte7_64_elI by blast

lemma step_exps_load_byte8_64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ7 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 63 \<sim> lo : 56)\<close>
  using assms unfolding storage_el64_def apply -
  by (solve_exps_mem32I add: assms)

interpretation step_exps_load_byte8_64_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 2 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v w\<^sub>1 v\<^sub>2)[succ7 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 63 \<sim> lo : 56)\<close>
  apply unfold_locales
  using step_exps_load_byte8_64_elI by blast

lemma step_exp_load_word_el64_strictE:
  assumes major: \<open>\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u64 \<leadsto>* (num' \<Colon> sz')\<close> and caveat: \<open>type v = mem\<langle>sz, 8\<rangle>\<close>
  obtains (Next) num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 num\<^sub>3 sz\<^sub>3 num\<^sub>4 sz\<^sub>4 num\<^sub>5 sz\<^sub>5 num'' sz'' num''' sz''' num'''' sz'''' where
    "\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u8 \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)"
    "\<Delta> \<turnstile> (Val v)[succ (num \<Colon> sz), el]:u8 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
    "\<Delta> \<turnstile> (Val v)[succ2 (num \<Colon> sz), el]:u8 \<leadsto>* (num\<^sub>3 \<Colon> sz\<^sub>3)"
    "\<Delta> \<turnstile> (Val v)[succ3 (num \<Colon> sz), el]:u8 \<leadsto>* (num\<^sub>4 \<Colon> sz\<^sub>4)"
    "\<Delta> \<turnstile> (Val v)[succ4 (num \<Colon> sz), el]:u32 \<leadsto>* (num\<^sub>5 \<Colon> sz\<^sub>5)"
    "\<Delta> \<turnstile> ((num'' \<Colon> sz'') \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* (num' \<Colon> sz')"
    "\<Delta> \<turnstile> ((num''' \<Colon> sz''') \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto>* (num'' \<Colon> sz'')"
    "\<Delta> \<turnstile> ((num'''' \<Colon> sz'''') \<copyright> (num\<^sub>3 \<Colon> sz\<^sub>3)) \<leadsto>* (num''' \<Colon> sz''')"
    "\<Delta> \<turnstile> ((num\<^sub>5 \<Colon> sz\<^sub>5) \<copyright> (num\<^sub>4 \<Colon> sz\<^sub>4)) \<leadsto>* (num'''' \<Colon> sz'''')"
using major caveat proof (elim step_exps_load_reduce_valE.word step_exp_load_word_el_strictE [where sz\<^sub>m\<^sub>e\<^sub>m = 8])
  fix e' :: exp and str :: "char list"
  assume "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')"
    and "e' = unknown[str]: imm\<langle>64\<rangle>"
  thus ?thesis
    by (meson step_exps_valE.unknown_imm word_unknown_neq)
next
  fix e' :: exp
  assume step: "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')"
    and e': "e' = ((Val v)[succ (num \<Colon> sz), el]:u(64 - 8)) \<copyright> ((Val v)[num \<Colon> sz, el]:u8)"
  show ?thesis
    using step unfolding e' apply -
    apply (erule step_exps_concat_lhs_reduce_totalE)
    apply (erule step_exps_concat_rhs_reduce_totalE)
    apply simp
    apply (elim step_exps_load_reduce_valE.word[where sza = 56] step_exp_load_word_el_strictE.succ 
                 step_exp_load_word_el_strictE)
    apply (rule caveat)
    apply linarith
    apply (meson step_exps_valE.unknown_imm word_unknown_neq)
    apply simp
    apply (erule step_exps_concat_lhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply (erule step_exps_concat_rhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply clarify
    apply (elim step_exps_load_reduce_valE.word[where sza = 48] 
                step_exp_load_word_el_strictE.is_word[rotated] step_exp_load_word_el_strictE)
    apply (rule caveat)
    apply linarith
    apply (meson step_exps_valE.unknown_imm word_unknown_neq)
    apply simp
    defer apply solve_is_wordI
    apply (erule step_exps_concat_lhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply (erule step_exps_concat_rhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply clarify
    apply (elim step_exps_load_reduce_valE.word[where sza = 40] 
                step_exp_load_word_el_strictE.is_word[rotated] step_exp_load_word_el_strictE)
    apply (rule caveat)
    apply linarith
    apply (meson step_exps_valE.unknown_imm word_unknown_neq)
    apply simp
    defer apply solve_is_wordI
    apply (erule step_exps_concat_lhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply (erule step_exps_concat_rhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    by (rule Next)
qed auto

lemma step_exps_load_word64_next_word16_elI:
  assumes neq: \<open>w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
               \<open>w \<noteq> succ2 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ3 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ4 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
               \<open>w \<noteq> succ5 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ6 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ7 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el64_strictE)
  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>1'' sz\<^sub>1'' num\<^sub>1''' sz\<^sub>1''' num\<^sub>1'''' sz\<^sub>1'''' num\<^sub>1''''' sz\<^sub>1'''''  num\<^sub>1'''''' 
        sz\<^sub>1'''''' num\<^sub>1''''''' sz\<^sub>1''''''' num\<^sub>5 sz\<^sub>5 :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
     and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''' \<Colon> sz\<^sub>1''')"
     and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')"
     and load4: "\<Delta> \<turnstile> (Val v)[succ3 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')"
     and load5: "\<Delta> \<turnstile> (Val v)[succ4 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u32 \<leadsto>* (num\<^sub>5 \<Colon> sz\<^sub>5)"
     and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
     and concat2: "\<Delta> \<turnstile> ((num\<^sub>1'''' \<Colon> sz\<^sub>1'''') \<copyright> (num\<^sub>1''' \<Colon> sz\<^sub>1''')) \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
     and concat3: "\<Delta> \<turnstile> ((num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''') \<copyright> (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')) \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')"
     and concat4: "\<Delta> \<turnstile> ((num\<^sub>5 \<Colon> sz\<^sub>5) \<copyright> (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')) \<leadsto>* (num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''')"
  show ?thesis
    unfolding w by (solve_exps_mem32I add: type neq[unfolded w] is_ok[unfolded w] load1 load2 
          load3 load4 load5 concat1  concat2 concat3 concat4)
qed

interpretation step_exps_load_word64_next_word16_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; w \<noteq> succ w\<^sub>1; w \<noteq> succ2 w\<^sub>1; w \<noteq> succ3 w\<^sub>1; w \<noteq> succ4 w\<^sub>1; w \<noteq> succ5 w\<^sub>1; 
      w \<noteq> succ6 w\<^sub>1; w \<noteq> succ7 w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; 
      \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v\<^sub>3 w v')[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word64_next_word16_elI by blast

lemma step_exps_load_word16_next_word64_elI:
  assumes neq: \<open>w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> 
               \<open>succ2 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ3 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ4 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> 
               \<open>succ5 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ6 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ7 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el16_strictE)
  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>1'' sz\<^sub>1'' :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
     and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
     and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
  show ?thesis
    unfolding storage_el64_def w
    by (solve_exps_mem32I add: type neq[unfolded w] is_ok[unfolded w] load1 load2 concat1)
qed

interpretation step_exps_load_word16_next_word64_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; succ4 w \<noteq> w\<^sub>1; succ5 w \<noteq> w\<^sub>1; succ6 w \<noteq> w\<^sub>1; 
      succ7 w \<noteq> w\<^sub>1; w \<noteq> succ w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; 
      \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v\<^sub>3 w v')[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word16_next_word64_elI by blast

lemma step_exps_load_word64_next_word32_elI:
  assumes neq': \<open>no_address_overlap_64_32 (num\<^sub>1 \<Colon> sz\<^sub>1) w\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el64_strictE)
  note neq = no_address_overlap_64_32[OF neq', symmetric]

  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>1'' sz\<^sub>1'' num\<^sub>1''' sz\<^sub>1''' num\<^sub>1'''' sz\<^sub>1'''' num\<^sub>1''''' sz\<^sub>1'''''  num\<^sub>1'''''' 
      sz\<^sub>1'''''' num\<^sub>1''''''' sz\<^sub>1''''''' num\<^sub>5 sz\<^sub>5 :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
     and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''' \<Colon> sz\<^sub>1''')"
     and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')"
     and load4: "\<Delta> \<turnstile> (Val v)[succ3 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')"
     and load5: "\<Delta> \<turnstile> (Val v)[succ4 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u32 \<leadsto>* (num\<^sub>5 \<Colon> sz\<^sub>5)"
     and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
     and concat2: "\<Delta> \<turnstile> ((num\<^sub>1'''' \<Colon> sz\<^sub>1'''') \<copyright> (num\<^sub>1''' \<Colon> sz\<^sub>1''')) \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
     and concat3: "\<Delta> \<turnstile> ((num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''') \<copyright> (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')) \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')"
     and concat4: "\<Delta> \<turnstile> ((num\<^sub>5 \<Colon> sz\<^sub>5) \<copyright> (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')) \<leadsto>* (num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''')"
  show "\<Delta> \<turnstile> (storage_el32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
    unfolding w by (solve_exps_mem32I add: type neq[unfolded w] is_ok[unfolded w] load1 load2 
          load3 load4 load5 concat1 concat2 concat3 concat4)
qed

interpretation step_exps_load_word64_next_word32_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>no_address_overlap_64_32 w\<^sub>1 w; type w = imm\<langle>sz\<^sub>1\<rangle>; 
      type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v\<^sub>3 w v')[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word64_next_word32_elI by blast

lemma step_exps_load_word32_next_word64_elI:
  assumes neq': \<open>no_address_overlap_64_32 w (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el32_strictE)
  note neq = no_address_overlap_64_32[OF neq']

  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>2' sz\<^sub>2' num'' sz'' num\<^sub>5 sz\<^sub>5 num\<^sub>3 sz\<^sub>3 :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
     and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>2' \<Colon> sz\<^sub>2')"
     and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u16 \<leadsto>* (num\<^sub>3 \<Colon> sz\<^sub>3) "
     and concat1: "\<Delta> \<turnstile> ((num'' \<Colon> sz'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
     and concat2: "\<Delta> \<turnstile> ((num\<^sub>3 \<Colon> sz\<^sub>3) \<copyright> (num\<^sub>2' \<Colon> sz\<^sub>2')) \<leadsto>* (num'' \<Colon> sz'')"
  have load3': \<open>\<Delta> \<turnstile> (storage_el64 v (num \<Colon> sz\<^sub>1) v')[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u16 \<leadsto>* (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
    apply (rule step_exps_load_word16_next_word64_elI.is_word2_val)
    apply (solve_is_wordI, solve_is_wordI, solve_is_valI)
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule type)
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (rule load3)
    done
  show ?thesis
    unfolding w 
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] 
           is_ok[unfolded w] load1 load2 load3' concat1 concat2 load3')
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1' \<Colon> sz\<^sub>1'\<close>])
    apply (rule step_exps_load_next_byte64_elI)
    apply (rule neq[unfolded w])+
    apply (rule load1)
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] load1
                                 is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>2' \<Colon> sz\<^sub>2'\<close>])
    apply (rule step_exps_load_next_byte64_elI.succ.val)
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule load2)
    apply (solve_exps_mem32I add: load3' concat2 concat1)
    apply (rule concat1)
    done
qed

interpretation step_exps_load_word32_next_word64_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>no_address_overlap_64_32 w w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; 
      \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v\<^sub>3 w v')[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word32_next_word64_elI by blast

method solve_no_address_overlap_64_32 uses add = (
  solves \<open>rule add\<close> |
  (rule no_address_overlap_64_32_plusI, solve_lt_power, solve_lt_power, linarith) |
  \<comment> \<open>Bad case - slow\<close>
  (print_fact no_address_overlap_64_32_def, (unfold no_address_overlap_64_32_def)[1], intro conjI,
     solve_no_address_overlap_32_32 add: add, solve_word_neq add: add, solve_word_neq add: add,
     solve_word_neq add: add, solve_word_neq add: add)
)

lemma step_exps_load_word64_next_word64_elI:
  assumes neq': \<open>no_address_overlap_64_64 w (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u64 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el64_strictE)
  note neq = no_address_overlap_64_64[OF neq']

  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>1'' sz\<^sub>1'' num\<^sub>1''' sz\<^sub>1''' num\<^sub>1'''' sz\<^sub>1'''' num\<^sub>1''''' sz\<^sub>1'''''  num\<^sub>1'''''' 
      sz\<^sub>1'''''' num\<^sub>1''''''' sz\<^sub>1''''''' num\<^sub>5 sz\<^sub>5 :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
     and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''' \<Colon> sz\<^sub>1''')"
     and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')"
     and load4: "\<Delta> \<turnstile> (Val v)[succ3 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')"
     and load5: "\<Delta> \<turnstile> (Val v)[succ4 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u32 \<leadsto>* (num\<^sub>5 \<Colon> sz\<^sub>5)"
     and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
     and concat2: "\<Delta> \<turnstile> ((num\<^sub>1'''' \<Colon> sz\<^sub>1'''') \<copyright> (num\<^sub>1''' \<Colon> sz\<^sub>1''')) \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
     and concat3: "\<Delta> \<turnstile> ((num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''') \<copyright> (num\<^sub>1''''' \<Colon> sz\<^sub>1''''')) \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')"
     and concat4: "\<Delta> \<turnstile> ((num\<^sub>5 \<Colon> sz\<^sub>5) \<copyright> (num\<^sub>1''''''' \<Colon> sz\<^sub>1''''''')) \<leadsto>* (num\<^sub>1'''''' \<Colon> sz\<^sub>1'''''')"
  have load5': \<open>\<Delta> \<turnstile> (storage_el64 v (num \<Colon> sz\<^sub>1) v')[succ4 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u32 \<leadsto>* (num\<^sub>5 \<Colon> sz\<^sub>5)\<close>
    apply (rule step_exps_load_word32_next_word64_elI.is_word2_val)
    apply (solve_is_wordI, solve_is_wordI, solve_is_valI)
    apply (solve_no_address_overlap_64_32 add: neq[unfolded w] is_ok[unfolded w])
    apply (solve_typeI)
    apply (rule type)
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (rule load5)
    done
  show ?thesis
    unfolding w 
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] is_ok[unfolded w] load1 load2 
          load3 load4 load5' concat1 concat2 concat3 concat4)
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1' \<Colon> sz\<^sub>1'\<close>])
    apply (rule step_exps_load_next_byte64_elI)
    apply (rule neq[unfolded w])+
    apply (rule load1)
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] load1
                                 is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1''' \<Colon> sz\<^sub>1'''\<close>])
    apply (rule step_exps_load_next_byte64_elI.succ.val)
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule load2)
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] load1
                                 is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1''''' \<Colon> sz\<^sub>1'''''\<close>])
    apply (rule step_exps_load_next_byte64_elI.is_word_val)
    apply solve_is_wordI
    apply solve_is_valI
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule load3)
    apply (solve_exps_mem32I add: storage_el64_is_val type_storage_el64 type neq[unfolded w] load1
                                 is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1''''''' \<Colon> sz\<^sub>1'''''''\<close>])
    apply (rule step_exps_load_next_byte64_elI.is_word_val)
    apply solve_is_wordI
    apply solve_is_valI
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule load4)
    apply (rule step_exps_concat_lhs_totalI.word[where e\<^sub>1' = \<open>num\<^sub>5 \<Colon> sz\<^sub>5\<close>])
    apply (rule load5')
    apply (rule concat4)
    apply (rule concat3)
    apply (rule concat2)
    apply (rule concat1)
    done
qed


interpretation step_exps_load_word64_next_word64_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. \<lbrakk>no_address_overlap_64_64 w w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; 
      type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el64 v\<^sub>3 w v')[e\<^sub>1, el]:u64 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word64_next_word64_elI by blast

\<comment> \<open>Store\<close>

lemma step_exps_store_word64_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_el64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  apply (solve_exps_mem32I add: assms)
  unfolding storage_el64_def storage_el32_def storage_el16_def
  apply simp
  by solve_exps_mem32I

interpretation step_exps_store_word64_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  apply (standard)
  using step_exps_store_word64_elI by blast

subsubsection \<open>Big Endian\<close>

lemma step_exps_load_word64_beI:
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> sz \<sim> hi : 63 \<sim> lo : 0)\<close>
  using assms apply - 
  unfolding storage_be64_def
  apply (solve_exps_mem32I add: assms, simp)
  unfolding xtract64_56_0[symmetric] by solve_exps_mem32I

lemmas step_exps_load_word64_be64I = step_exps_load_word64_beI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

interpretation step_exps_load_word64_beI: exp_val_word_fixed_sz_syntax2 
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _. (\<And>\<Delta> v. 2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
\<Delta> \<turnstile> (storage_be64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, be]:u64 \<leadsto>* (ext e\<^sub>v \<sim> hi : 63 \<sim> lo : 0))\<close>
  apply standard
  using step_exps_load_word64_beI by blast

\<comment> \<open>Load Next\<close>

lemma step_exps_load_next_byte64_beI: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> 
               \<open>succ2 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ3 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
               \<open>succ4 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ5 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
               \<open>succ6 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ7 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be64 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
  unfolding storage_be64_def apply -
  by (solve_exps_mem32I add: nxt neq step_exps_load_next_byte32_beI)

interpretation step_exps_load_next_byte64_beI: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; succ4 w \<noteq> w\<^sub>1; succ5 w \<noteq> w\<^sub>1; 
      succ6 w \<noteq> w\<^sub>1; succ7 w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk> 
          \<Longrightarrow> \<Delta> \<turnstile> (storage_be64 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte64_beI by blast 

\<comment> \<open>Store\<close>

lemma step_exps_store_word64_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_be64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  unfolding storage_be16_def storage_be32_def storage_be64_def
  apply (solve_exps_mem32I add: assms)
  apply simp
  by solve_exps_mem32I

interpretation step_exps_store_word64_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  apply standard
  using step_exps_store_word64_beI by blast

subsubsection \<open>The 64 bit solver scaffold\<close>

method solve_no_address_overlap_64_64 uses add = (
  solves \<open>rule add\<close> |
  (rule no_address_overlap_64_64_swapI, solves \<open>rule add\<close>) |
  (rule no_address_overlap_64_64_plusI, solve_lt_power, solve_lt_power, linarith) |
  \<comment> \<open>Bad case - slow\<close>
  (print_fact no_address_overlap_64_64_def, ((unfold no_address_overlap_64_64_def)[1], intro conjI),
    solve_no_address_overlap_64_32 add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add)
)

method fastsolve_exps_mem64I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  \<comment> \<open>Load 64bit word\<close>
  (rule step_exps_load_word64_el_num_ltI.is_sz_word, solve_is_wordI, (solves \<open>rule add\<close> | linarith), 
    solve_lt_power add: add) |
  (rule step_exps_load_word64_elI.is_word2 step_exps_load_word64_beI.is_word2
    step_exps_load_byte1_64_elI.is_word2 step_exps_load_byte2_64_elI.is_word2 
    step_exps_load_byte3_64_elI.is_word2 step_exps_load_byte4_64_elI.is_word2 
    step_exps_load_byte5_64_elI.is_word2 step_exps_load_byte6_64_elI.is_word2 
    step_exps_load_byte7_64_elI.is_word2 step_exps_load_byte8_64_elI.is_word2, solve_is_wordI, 
    solve_is_wordI, (solves \<open>rule add\<close> | linarith)) |

  \<comment> \<open>Skip 16bit load on 64bit memory\<close>
  (rule step_exps_load_word16_next_word64_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
    solve_is_val,
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_type, solve_type, typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 32bit load on 64bit memory\<close>
  (rule step_exps_load_word32_next_word64_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
    solve_is_val, solve_no_address_overlap_64_32 add: add, 
    solve_type, solve_type, typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 64bit load on 16bit memory\<close>
  (rule step_exps_load_word64_next_word16_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
    solve_is_val,
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_type, solve_type, typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 64bit load on 32bit memory\<close>
  (rule step_exps_load_word64_next_word32_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
    solve_is_val, solve_no_address_overlap_64_32 add: add,
    solve_type, solve_type, typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 64bit load on 64bit memory\<close>
  (rule step_exps_load_word64_next_word64_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
    solve_is_val, solve_no_address_overlap_64_64 add: add, 
    solve_type, solve_type,
    typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  (rule step_exps_concat_last_word64_el_lt_numI, (solves \<open>rule add\<close> | ((unfold power_numeral Num.pow.simps Num.sqr.simps)?, linarith))) |
  (rule step_exps_concat_last_word64_elI.is_word step_exps_concat_word64_elI.is_word, 
    solve_is_wordI) |

  (rule step_exps_load_next_byte64_elI.is_word_val step_exps_load_next_byte64_beI.is_word_val, 
    solve_is_wordI, solve_is_val, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add,
    recurs?) |
  (rule step_exps_store_word64_elI.is_word_val2 step_exps_store_word64_beI.is_word_val2, 
    defer_tac, solve_is_wordI, solve_is_wordI, solve_is_val, prefer_last,
    solve_type) |
                  
  (fastsolve_exps_mem32I_scaffold recurs solve_exp solve_type solve_is_val add: add)
)

method solve_exps_mem64I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  fastsolve_exps_mem64I_scaffold recurs solve_exp solve_type solve_is_val add: add |
                  
  (solve_expsI_scaffold recurs solve_exp solve_type solve_is_val add: add)
)

(* These will be deleted *)
lemmas solve_exps_mem64_simps = 
  xtract64_56_48 xtract64_48_40 xtract64_40_32 xtract64_32_24 xtract64_24_16 xtract64_16_8 
  xtract64_8_0   xtract40_32_0  xtract48_40_0  xtract56_48_0  xtract64_56_0

  xtract_nested_63_8_55_8  xtract_nested_63_16_47_8 xtract_nested_63_24_39_8 
  xtract_nested_63_32_31_8 xtract_nested_63_40_23_8 xtract_nested_63_48_15_8
  xtract_nested_55_0_47_0  xtract_nested_47_0_39_0  xtract_nested_39_0_31_0
  xtract_nested_63_8_7_0   xtract_nested_63_16_7_0  xtract_nested_63_24_7_0
  xtract_nested_63_32_7_0  xtract_nested_63_40_7_0  xtract_nested_63_48_7_0
  xtract_nested_55_0_55_48 xtract_nested_47_0_47_40 xtract_nested_39_0_39_32


method fastsolve_exps_mem64I uses add = (
  solves \<open>rule add\<close> |
  fastsolve_exps_mem64I_scaffold \<open>fastsolve_exps_mem64I add: add\<close> \<open>solve_expI add: add\<close>
      \<open>solve_type64I add: add\<close> \<open>solve_is_val64I add: add\<close> add: add
)

method solve_exps_mem64I uses add = (
  solves \<open>rule add\<close> |
  solve_exps_mem64I_scaffold \<open>solve_exps_mem64I add: add\<close> \<open>solve_expI add: add\<close>
      \<open>solve_type64I add: add\<close> \<open>solve_is_val64I add: add\<close> add: add
)

method solve_bil_mem64I uses add = (
  solve_bilI_scaffold \<open>solve_bil_mem64I add: add\<close> \<open>solve_exps_mem64I add: add\<close> 
      \<open>solve_is_val64I add: add\<close> add: add
)

context bil_syntax
begin

method solve_prog_mem64I uses add decoder = (
  solve_progI_scaffold \<open>solve_bil_mem64I add: add\<close> decoder: decoder
)

end

end
