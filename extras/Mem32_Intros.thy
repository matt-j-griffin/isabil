theory Mem32_Intros
  imports Mem32
          Mem16_Intros
begin

(** TODO **)
lemma storage32_nat_simps[simp, exp_cast_simps]: 
    \<open>32 - 24 = (8::nat)\<close> \<open>32 - 1 = (31::nat)\<close> \<open>31 - 8 = (23::nat)\<close> \<open>31 - 24 = (7::nat)\<close>
    \<open>24 - 1 = (23::nat)\<close> \<open>24 - 16 = (8::nat)\<close> \<open>23 - 8 = (15::nat)\<close> \<open>23 - 16 = (7::nat)\<close>
    \<open>Suc 23 = 24\<close> \<open>Suc 15 = 16\<close>
  by auto (* after performing a store, attempt to unfold some nats *)

lemma xtract_num_lt32:
  assumes num_lt: \<open>num < 2 ^ 32\<close>
    shows \<open>(ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0) = num \<Colon> 32\<close>
  using extract_concat32 num_lt by auto

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_last_word32_elI: \<open>\<Delta> \<turnstile> ((((ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot> 
               ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num \<Colon> sz \<sim> hi : 7 \<sim> lo : 0) 
          \<leadsto>* ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0\<close>
  unfolding xtract32_8_0[symmetric] xtract32[symmetric] by solve_exps_mem16I

interpretation step_exps_concat_last_word32_elI: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. \<Delta> \<turnstile> ((((ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext e\<^sub>1 \<sim> hi : 23 \<sim> lo : 16) \<cdot> 
               ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e\<^sub>1 \<sim> hi : 7 \<sim> lo : 0) 
          \<leadsto>* ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_concat_last_word32_elI by blast

lemma step_exps_concat_last_word32_el_lt_numI:  (* TODO: Is it worth having these if our simpwords can handle it *)
  assumes num_lt: \<open>num < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> ((((ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot> 
               ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext num \<Colon> sz \<sim> hi : 7 \<sim> lo : 0)
           \<leadsto>* (num \<Colon> 32)\<close>
  using step_exps_concat_last_word32_elI[where num = num and sz = sz]
  unfolding xtract_num_lt32[OF num_lt] .
(*
interpretation step_exps_concat_last_word32_el_lt_numI: exp_val_word_fixed_num_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 num\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. num\<^sub>1 < 2 ^ 32 \<Longrightarrow> \<Delta> \<turnstile> ((((ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext e\<^sub>1 \<sim> hi : 23 \<sim> lo : 16) \<cdot> 
               ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e\<^sub>1 \<sim> hi : 7 \<sim> lo : 0) 
          \<leadsto>* (num\<^sub>1 \<Colon> 32))\<close>
  apply unfold_locales
  using step_exps_concat_last_word32_el_lt_numI[where num = num and sz = sz] by blast*)

lemma step_exps_concat_word32_elI: \<open>\<Delta> \<turnstile> ((((
  ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<copyright>
  ext num \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0)\<close>
  by (solve_exps_mem16I add: step_exps_concat_last_word32_elI)

interpretation step_exps_concat_word32_elI: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. \<Delta> \<turnstile> ((((ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext e\<^sub>1 \<sim> hi : 23 \<sim> lo : 16) \<copyright> 
               ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e\<^sub>1 \<sim> hi : 7 \<sim> lo : 0) 
          \<leadsto>* ext e\<^sub>1 \<sim> hi : 31 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_concat_word32_elI by blast

lemma step_exps_load_word32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leadsto>* (ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply -
  unfolding storage_el32_def
  by (solve_exps_mem16I add: step_exps_concat_last_word32_elI)

interpretation step_exps_load_word32_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u32 \<leadsto>* ext e\<^sub>2 \<sim> hi : 31 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_word32_elI by blast

lemma step_exps_load_word32_el_num_ltI: (* TODO might not be needed when the extract simplifier comes *)
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and num_lt: \<open>num\<^sub>v < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leadsto>* (num\<^sub>v \<Colon> 32)\<close>
  using step_exps_load_word32_elI[OF assms(1), where num=num\<^sub>v]
  unfolding xtract_num_lt32[OF num_lt] .

interpretation step_exps_load_word32_el_num_ltI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>\<Delta> v num\<^sub>v sz. \<lbrakk>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; num\<^sub>v < 2 ^ 32\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el32 v w\<^sub>a (num\<^sub>v \<Colon> sz))[e\<^sub>a, el]:u32 \<leadsto>* (num\<^sub>v \<Colon> 32))\<close>
  apply standard
  using step_exps_load_word32_el_num_ltI by blast

lemma step_exps_load_next_byte32_elI: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> 
               \<open>succ2 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ3 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
  unfolding storage_el32_def
  by (solve_exps_mem16I add: nxt neq)

interpretation step_exps_load_next_byte32_elI: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk> 
          \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte32_elI by blast 

lemma step_exps_load_byte1_32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 7 \<sim> lo : 0)\<close>
  using assms unfolding storage_el32_def apply -
  by (solve_exps_mem16I add: assms)

interpretation step_exps_load_byte1_32_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 7 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_byte1_32_elI by blast

lemma step_exps_load_byte2_32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 15 \<sim> lo : 8)\<close>
  using assms unfolding storage_el32_def apply -
  by (solve_exps_mem16I add: assms)

interpretation step_exps_load_byte2_32_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v w\<^sub>1 v\<^sub>2)[succ e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 15 \<sim> lo : 8)\<close>
  apply unfold_locales
  using step_exps_load_byte2_32_elI by blast

lemma step_exps_load_byte3_32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ2 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 23 \<sim> lo : 16)\<close>
  using assms unfolding storage_el32_def apply -
  by (solve_exps_mem16I add: assms)

interpretation step_exps_load_byte3_32_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v w\<^sub>1 v\<^sub>2)[succ2 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 23 \<sim> lo : 16)\<close>
  apply unfold_locales
  using step_exps_load_byte3_32_elI by blast

lemma step_exps_load_byte4_32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[succ3 (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                  \<leadsto>* (ext (num\<^sub>v \<Colon> sz) \<sim> hi : 31 \<sim> lo : 24)\<close>
  using assms unfolding storage_el32_def apply -
  by (solve_exps_mem16I add: assms)

interpretation step_exps_load_byte4_32_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v w\<^sub>1 v\<^sub>2)[succ3 e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 31 \<sim> lo : 24)\<close>
  apply unfold_locales
  using step_exps_load_byte4_32_elI by blast

lemma step_exp_load_word_el32_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u32 \<leadsto>* (num' \<Colon> sz')\<close> and caveat: \<open>type v = mem\<langle>sz, 8\<rangle>\<close>
  obtains (Next) num\<^sub>1 num\<^sub>2 num\<^sub>3 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 num'' sz'' where \<open>\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u8 \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
          \<open>\<Delta> \<turnstile> (Val v)[succ (num \<Colon> sz), el]:u8 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
          \<open>\<Delta> \<turnstile> (Val v)[succ2 (num \<Colon> sz), el]:u16 \<leadsto>* (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
          "\<Delta> \<turnstile> ((num'' \<Colon> sz'') \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* (num' \<Colon> sz')"
          "\<Delta> \<turnstile> ((num\<^sub>3 \<Colon> sz\<^sub>3) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto>* (num'' \<Colon> sz'')"
using major caveat proof (elim step_exps_load_reduce_valE.word 
                               step_exp_load_word_el_strictE[where sz\<^sub>m\<^sub>e\<^sub>m = 8])
  fix e' str
  assume step: "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')" and e': "e' = unknown[str]: imm\<langle>32\<rangle>"
  show thesis
    using step unfolding e' by (meson step_exps_valE.unknown_imm word_unknown_neq)
next
  fix e' assume step: "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')"
    and e': "e' = ((Val v)[succ (num \<Colon> sz), el]:u(32 - 8)) \<copyright> ((Val v)[num \<Colon> sz, el]:u8)"
  show thesis
    using step unfolding e' apply -
    apply (erule step_exps_concat_lhs_reduce_totalE)
    apply (erule step_exps_concat_rhs_reduce_totalE)
    apply simp
    apply (elim step_exps_load_reduce_valE.word[where sza = 24] step_exp_load_word_el_strictE.succ 
                 step_exp_load_word_el_strictE)
    apply (rule caveat)
    apply linarith
    apply (meson step_exps_valE.unknown_imm word_unknown_neq)
    apply simp
    apply (erule step_exps_concat_lhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    apply (erule step_exps_concat_rhs_reduce_totalE[where e = \<open>_[_, el]:u_\<close>])
    by (rule Next)
qed auto

lemma step_exps_load_word32_next_word16_elI:
  assumes neq: \<open>w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
               \<open>w \<noteq> succ2 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ3 (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el32_strictE)
  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' num\<^sub>1'' num\<^sub>2' sz\<^sub>1' sz\<^sub>1'' sz\<^sub>2' num\<^sub>1'''' sz\<^sub>1'''' :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
    and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
    and concat2: "\<Delta> \<turnstile> ((num\<^sub>1'''' \<Colon> sz\<^sub>1'''') \<copyright> (num\<^sub>2' \<Colon> sz\<^sub>2')) \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
    and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>2' \<Colon> sz\<^sub>2')"
    and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u16 \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')"
  show ?thesis
    unfolding w by (solve_exps_mem16I add: type neq[unfolded w] is_ok[unfolded w] load1 load2 type 
                                           load3 concat2 concat1)
qed

interpretation step_exps_load_word32_next_word16_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; w \<noteq> succ w\<^sub>1; w \<noteq> succ2 w\<^sub>1; w \<noteq> succ3 w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; 
      type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v\<^sub>3 w v')[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word32_next_word16_elI by blast

lemma step_exps_load_word16_next_word32_elI:
  assumes neq: \<open>w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ2 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
               \<open>succ3 w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el16_strictE)
  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>2' sz\<^sub>2' :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
    and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>2' \<Colon> sz\<^sub>2')"
    and concat: "\<Delta> \<turnstile> ((num\<^sub>2' \<Colon> sz\<^sub>2') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
  show ?thesis
    unfolding storage_el32_def w
    by (solve_exps_mem16I add: type neq[unfolded w] load1 is_ok[unfolded w] load2 concat)
qed

interpretation step_exps_load_word16_next_word32_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; w \<noteq> succ w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; 
      type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok; \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v\<^sub>3 w v')[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word16_next_word32_elI by blast

lemma step_exps_load_word32_next_word32_elI:
  assumes neq': \<open>no_address_overlap_32_32 w (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u32 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el32_strictE)
  note neq = no_address_overlap_32_32[OF neq']

  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' sz\<^sub>1' num\<^sub>1'' sz\<^sub>1'' num\<^sub>2' sz\<^sub>2' num\<^sub>1'''' sz\<^sub>1'''' :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
    and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>2' \<Colon> sz\<^sub>2')"
    and load3: "\<Delta> \<turnstile> (Val v)[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u16 \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')"
    and concat1: "\<Delta> \<turnstile> ((num\<^sub>1'' \<Colon> sz\<^sub>1'') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
    and concat2: "\<Delta> \<turnstile> ((num\<^sub>1'''' \<Colon> sz\<^sub>1'''') \<copyright> (num\<^sub>2' \<Colon> sz\<^sub>2')) \<leadsto>* (num\<^sub>1'' \<Colon> sz\<^sub>1'')"
  have load3': \<open>\<Delta> \<turnstile> (storage_el32 v (num \<Colon> sz\<^sub>1) v')[succ2 (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u16 \<leadsto>* (num\<^sub>1'''' \<Colon> sz\<^sub>1'''')\<close>
    apply (rule step_exps_load_word16_next_word32_elI.is_word2_val)
    apply solve_is_wordI
    apply solve_is_wordI
    apply solve_is_valI
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule type)
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (typec_word_is_ok add: is_ok[unfolded w])
    apply (rule load3)
    done

  show ?thesis
    unfolding w
    apply (solve_exps_mem16I add: storage_el32_is_val type_storage_el32 type neq[unfolded w] load1
                                  is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>1' \<Colon> sz\<^sub>1'\<close>])
    apply (rule step_exps_load_next_byte32_elI)
    apply (rule neq[unfolded w])+
    apply (rule load1)
    apply (solve_exps_mem16I add: storage_el32_is_val type_storage_el32 type neq[unfolded w] load1
                                 is_ok[unfolded w] load2 concat1 concat2 )
    apply (rule step_exps_concat_rhs_totalI[where e\<^sub>2' = \<open>num\<^sub>2' \<Colon> sz\<^sub>2'\<close>])
    apply (rule step_exps_load_next_byte32_elI.succ.val)
    apply (solve_word_neq add: neq[unfolded w] is_ok[unfolded w])+
    apply (rule load2)
    apply (rule step_exps_concat_lhs_totalI.word[where e\<^sub>1' = \<open>num\<^sub>1'''' \<Colon> sz\<^sub>1''''\<close>])
    apply (rule load3')
    apply (rule concat2)
    apply (rule concat1)
    done
qed

interpretation step_exps_load_word32_next_word32_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta> w v'. 
    \<lbrakk>no_address_overlap_32_32 w w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>; w is ok; w\<^sub>1 is ok;
      \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2
    \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (storage_el32 v\<^sub>3 w v')[e\<^sub>1, el]:u32 \<leadsto>* e\<^sub>2)\<close>
  apply unfold_locales
  using step_exps_load_word32_next_word32_elI by blast

lemma step_exps_store_word32_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (storage_el32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))\<close>
  apply (solve_exps_mem16I add: assms, simp)
  unfolding storage_el32_def storage_el16_def
  by solve_exps_mem16I

interpretation step_exps_store_word32_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
      (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el32 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 32
  apply standard
  using step_exps_store_word32_elI by blast

\<comment> \<open>Big Endian\<close>
(* TODO it is now worth doing last BE concats too *)

lemma step_exps_load_word32_beI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leadsto>* (ext num \<Colon> sz \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply - 
  unfolding storage_be32_def
  apply (solve_exps_mem16I add: assms)
  apply simp
  unfolding xtract32_24_0[symmetric] by solve_exps_mem16I

interpretation step_exps_load_word32_beI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 1 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_be32 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, be]:u32 \<leadsto>* ext e\<^sub>2 \<sim> hi : 31 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_word32_beI by blast

lemma step_exps_load_next_byte32_beI: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> 
               \<open>succ2 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ3 w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be32 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
  unfolding storage_be32_def
  by (solve_exps_mem16I add: nxt neq step_exps_load_next_byte16_beI)

interpretation step_exps_load_next_byte32_beI: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; succ2 w \<noteq> w\<^sub>1; succ3 w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk>
          \<Longrightarrow> \<Delta> \<turnstile> (storage_be32 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte32_beI by blast 

lemma step_exps_store_word32_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (storage_be32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))\<close>
  using assms apply -
  unfolding storage_be16_def storage_be32_def
  apply (solve_exps_mem16I add: assms, simp)
  by solve_exps_mem16I

interpretation step_exps_store_word32_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be32 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 32
  apply standard
  using step_exps_store_word32_beI by blast


method solve_no_address_overlap_32_32 uses add = (
  solves \<open>rule add\<close> |
  (rule no_address_overlap_32_32_plusI, solve_lt_power, solve_lt_power, linarith) |
  (rule no_address_overlap_32_32_swapI, solves \<open>rule add\<close>) |
  \<comment> \<open>Bad case - slow\<close>
  (print_fact no_address_overlap_32_32_def, ((unfold no_address_overlap_32_32_def)[1], intro conjI); 
    solve_word_neq add: add)
)

\<comment> \<open>The 32 bit solver scaffold\<close>
method fastsolve_exps_mem32I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  \<comment> \<open>Load 32bit\<close>
  (rule step_exps_load_word32_el_num_ltI.is_sz_word, solve_is_wordI, (solves \<open>rule add\<close> | linarith), 
    solve_lt_power add: add) |
  (rule step_exps_load_word32_elI.is_word2 step_exps_load_word32_beI.is_word2 
    step_exps_load_byte1_32_elI.is_word2 step_exps_load_byte2_32_elI.is_word2 
    step_exps_load_byte3_32_elI.is_word2 step_exps_load_byte4_32_elI.is_word2, solve_is_wordI,
    solve_is_wordI, (solves \<open>rule add\<close> | linarith)) |

  \<comment> \<open>Skip 16bit load on 32bit memory\<close>
  (rule step_exps_load_word16_next_word32_elI.is_word2_val, solve_is_wordI, solve_is_wordI, solve_is_val,
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_type, solve_type, 
    typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 32bit load on 16bit memory\<close>
  (rule step_exps_load_word32_next_word16_elI.is_word2_val, solve_is_wordI, solve_is_wordI, solve_is_val,
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, solve_type, solve_type, 
    typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  \<comment> \<open>Skip 32bit load on memory\<close>
  (rule step_exps_load_word32_next_word32_elI.is_word2_val, solve_is_wordI, solve_is_wordI, 
   solve_is_val, solve_no_address_overlap_32_32 add: add, solve_type, solve_type,
   typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  (rule step_exps_concat_last_word32_el_lt_numI, (solves \<open>rule add\<close> | (solves \<open>rule add\<close> | ((unfold power_numeral Num.pow.simps Num.sqr.simps)?, linarith)))) |
  (rule step_exps_concat_last_word32_elI.is_word step_exps_concat_word32_elI.is_word, 
    solve_is_wordI) |

  (rule step_exps_load_next_byte32_elI.is_word_val step_exps_load_next_byte32_beI.is_word_val, 
    solve_is_wordI, solve_is_val, solve_word_neq add: add, solve_word_neq add: add, 
    solve_word_neq add: add, solve_word_neq add: add, 
    recurs?) |
  (rule step_exps_store_word32_elI.is_word_val2 step_exps_store_word32_beI.is_word_val2, 
    defer_tac, solve_is_wordI, solve_is_wordI, solve_is_val, prefer_last,
    solve_type) |


  fastsolve_exps_mem16I_scaffold recurs solve_exp solve_type solve_is_val add: add
)

method solve_exps_mem32I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  fastsolve_exps_mem32I_scaffold recurs solve_exp solve_type solve_is_val add: add |

  solve_expsI_scaffold recurs solve_exp solve_type solve_is_val add: add
)

method solve_exps_mem32I uses add = (
  solves \<open>rule add\<close> |
  solve_exps_mem32I_scaffold \<open>solve_exps_mem32I add: add\<close> \<open>solve_expI add: add\<close>
      \<open>solve_type32I add: add\<close> \<open>solve_is_val32I add: add\<close> add: add
)

method solve_bil_mem32I uses add = (
  solve_bilI_scaffold \<open>solve_bil_mem32I add: add\<close> \<open>solve_exps_mem32I add: add\<close> \<open>solve_is_val32I add: add\<close> add: add
)

context bil_syntax
begin

method solve_prog_mem32I uses add decoder = (
  solve_progI_scaffold \<open>solve_bil_mem32I add: add\<close> decoder: decoder
)

end

end
