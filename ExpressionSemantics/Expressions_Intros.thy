theory Expressions_Intros
  imports Expression_Intros Expressions_Rules
begin

subsection \<open>Refl\<close>

lemmas step_exps_reduceI = converse_rtranclp_into_rtranclp[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]
lemmas step_exps_reflI = rtranclp.rtrancl_refl[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]

lemma step_exps_reduce_singleI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>2\<close>
  using assms apply (rule step_exps_reduceI[of _ _ e\<^sub>2])
  by (rule step_exps_reflI)

lemmas step_exps_valI = step_exps_reflI[of _ \<open>Val _\<close>]

interpretation step_exps_valI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta>. \<Delta> \<turnstile> e \<leadsto>* e)\<close>
  apply (standard)
  using step_exps_valI by blast

lemmas step_exps_valsI =
    step_exps_reflI[of _ \<open>(_ \<Colon> _)\<close>] step_exps_reflI[of _ true] step_exps_reflI[of _ false]
    step_exps_reflI[of _ \<open>unknown[_]: _\<close>] step_exps_reflI[of _ \<open>_[(_ \<Colon> _) \<leftarrow> _, _]\<close>]
    step_exps_reflI[of _ \<open>Val _\<close>]

text \<open>RHS values, no assumptions - easy to discharge\<close>

lemmas step_exps_load_un_addrI = step_exps_reduce_singleI[OF step_load_un_addrI]
lemmas step_exps_not_trueI = step_exps_reduce_singleI[OF step_not_trueI]
lemmas step_exps_not_falseI = step_exps_reduce_singleI[OF step_not_falseI]
lemmas step_exps_uop_unk_notI = step_exps_reduce_singleI[OF step_uop_unk_notI]
lemmas step_exps_uop_unk_negI = step_exps_reduce_singleI[OF step_uop_unk_negI]
lemmas step_exps_uop_unkI = step_exps_reduce_singleI[OF step_uop_unkI]
lemmas step_exps_notI = step_exps_reduce_singleI[OF step_notI]
interpretation step_exps_notI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (\<sim> e) \<leadsto>* (~\<^sub>b\<^sub>v e))\<close>
  apply (standard)
  using step_exps_notI by blast

lemmas step_exps_eqI' = step_exps_reduce_singleI[OF step_eqI']
interpretation step_exps_eqI': exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) \<leadsto>* (e\<^sub>1 =\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_eqI' by blast

lemmas step_exps_negI = step_exps_reduce_singleI[OF step_negI]
interpretation step_exps_negI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (- e) \<leadsto>* (-\<^sub>b\<^sub>v e))\<close>
  apply (standard)
  using step_exps_negI by blast

lemmas step_exps_lop_unk_lhsI = step_exps_reduce_singleI[OF step_lop_unk_lhsI]
lemmas step_exps_lop_unk_rhsI = step_exps_reduce_singleI[OF step_lop_unk_rhsI]
lemmas step_exps_aop_unk_lhsI = step_exps_reduce_singleI[OF step_aop_unk_lhsI]
lemmas step_exps_aop_unk_rhsI = step_exps_reduce_singleI[OF step_aop_unk_rhsI]
lemmas step_exps_extractI = step_exps_reduce_singleI[OF step_extractI]
lemmas step_exps_extract_unI = step_exps_reduce_singleI[OF step_extract_unI]
lemmas step_exps_cast_unkI = step_exps_reduce_singleI[OF step_cast_unkI]

lemmas step_exps_plusI = step_exps_reduce_singleI[OF step_plusI]
interpretation step_exps_plusI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 + e\<^sub>2) \<leadsto>* (e\<^sub>1 +\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_plusI by blast

lemmas step_exps_minusI = step_exps_reduce_singleI[OF step_minusI]
interpretation step_exps_minusI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 - e\<^sub>2) \<leadsto>* (e\<^sub>1 -\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_minusI by blast

lemmas step_exps_timesI = step_exps_reduce_singleI[OF step_timesI]
interpretation step_exps_timesI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 * e\<^sub>2) \<leadsto>* (e\<^sub>1 *\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_timesI by blast

lemmas step_exps_divI = step_exps_reduce_singleI[OF step_divI]
interpretation step_exps_divI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 div e\<^sub>2) \<leadsto>* (e\<^sub>1 div\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_divI by blast

lemmas step_exps_sdivI = step_exps_reduce_singleI[OF step_sdivI]
interpretation step_exps_sdivI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 sdiv e\<^sub>2) \<leadsto>* (e\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_sdivI by blast

lemmas step_exps_modI = step_exps_reduce_singleI[OF step_modI]
interpretation step_exps_modI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 % e\<^sub>2) \<leadsto>* (e\<^sub>1 %\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_modI by blast

lemmas step_exps_smodI = step_exps_reduce_singleI[OF step_smodI]
interpretation step_exps_smodI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 smod e\<^sub>2) \<leadsto>* (e\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_smodI by blast

lemmas step_exps_signed_less_eqI = step_exps_reduce_singleI[OF step_signed_less_eqI]
interpretation step_exps_signed_less_eqI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 sle e\<^sub>2) \<leadsto>* (e\<^sub>1 \<le>\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_signed_less_eqI by blast

lemmas step_exps_signed_lessI = step_exps_reduce_singleI[OF step_signed_lessI]
interpretation step_exps_signed_lessI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 slt e\<^sub>2) \<leadsto>* (e\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_signed_lessI by blast

lemmas step_exps_lslI = step_exps_reduce_singleI[OF step_lslI]
interpretation step_exps_lslI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 << e\<^sub>2) \<leadsto>* (e\<^sub>1 <<\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_lslI by blast

lemmas step_exps_lsrI = step_exps_reduce_singleI[OF step_lsrI]
interpretation step_exps_lsrI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 >> e\<^sub>2) \<leadsto>* (e\<^sub>1 >>\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_lsrI by blast

lemmas step_exps_asrI = step_exps_reduce_singleI[OF step_asrI]
interpretation step_exps_asrI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 >>> e\<^sub>2) \<leadsto>* (e\<^sub>1 >>>\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_asrI by blast

lemmas step_exps_landI = step_exps_reduce_singleI[OF step_landI]
interpretation step_exps_landI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 && e\<^sub>2) \<leadsto>* (e\<^sub>1 &\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_landI by blast

lemmas step_exps_lorI = step_exps_reduce_singleI[OF step_lorI]
interpretation step_exps_lorI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 || e\<^sub>2) \<leadsto>* (e\<^sub>1 |\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_lorI by blast

lemmas step_exps_xorI = step_exps_reduce_singleI[OF step_xorI]
interpretation step_exps_xorI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 xor e\<^sub>2) \<leadsto>* (e\<^sub>1 xor\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_xorI by blast

lemmas step_exps_eq_sameI = step_exps_reduce_singleI[OF step_eq_sameI]
interpretation step_exps_eq_sameI: exp_val_word_sz_syntax 
    \<open>\<lambda>e _ w _. (\<And>\<Delta>. \<Delta> \<turnstile> BinOp e (LOp Eq) e \<leadsto>* true)\<close>
  apply (standard)
  using step_exps_eq_sameI by blast

lemmas step_exps_eq_diffI = step_exps_reduce_singleI[OF step_eq_diffI]
interpretation step_exps_eq_diffI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta>. w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = true \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 (LOp Eq) e\<^sub>2 \<leadsto>* false)\<close>
  apply (standard)
  using step_exps_eq_diffI by blast

lemmas step_exps_neq_sameI = step_exps_reduce_singleI[OF step_neq_sameI]
lemmas step_exps_neq_diffI = step_exps_reduce_singleI[OF step_neq_diffI]

lemmas step_exps_lessI = step_exps_reduce_singleI[OF step_lessI]
interpretation step_exps_lessI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. 
  (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 lt e\<^sub>2) \<leadsto>* (e\<^sub>1 <\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_lessI by blast

lemmas step_exps_less_eqI = step_exps_reduce_singleI[OF step_less_eqI]
interpretation step_exps_less_eqI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. 
  (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 le e\<^sub>2) \<leadsto>* (e\<^sub>1 \<le>\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_exps_less_eqI by blast

lemmas step_exps_concatI = step_exps_reduce_singleI[OF step_concatI]
interpretation step_exps_concatI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto>* (e\<^sub>1 \<cdot> e\<^sub>2))\<close>
  apply (standard)
  using step_exps_concatI by blast

interpretation step_exps_cast_lowI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> low:sz[e] \<leadsto>* ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_cast_lowI] by blast

interpretation step_exps_cast_highI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ sz'. (\<And>\<Delta> sz. \<Delta> \<turnstile> high:sz[e] \<leadsto>* ext e \<sim> hi : sz' - 1 \<sim> lo : sz' - sz)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_cast_highI] by blast

interpretation step_exps_cast_signedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> extend:sz[e] \<leadsto>* ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_cast_signedI] by blast

interpretation step_exps_cast_unsignedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> pad:sz[e] \<leadsto>* ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_cast_unsignedI] by blast

interpretation step_exps_load_byteI: exp_val_syntax \<open>\<lambda>e v'. (\<And>\<Delta> v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz ed. \<Delta> \<turnstile> v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, ed]:usz \<leadsto>* e)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_load_byteI] by blast

interpretation step_exps_load_un_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> str t ed sz. \<Delta> \<turnstile> (unknown[str]: t)[e, ed]:usz \<leadsto>* unknown[str]: imm\<langle>sz\<rangle>)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_load_un_memI] by blast

interpretation step_exps_letI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' var. \<Delta> \<turnstile> Let var e e' \<leadsto>* [v\<sslash>var]e')\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_letI] by blast

lemmas step_exps_store_valI = step_exps_reduce_singleI[OF step_store_valI] 
interpretation step_exps_store_valI: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m . (\<And>\<Delta> en. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>3 \<leadsto>* (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m]))\<close>
  apply (standard)
  using step_exps_store_valI by blast

interpretation step_exps_ite_trueI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto>* e\<^sub>1)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_ite_trueI] by blast

interpretation step_exps_ite_falseI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto>* e\<^sub>2)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_ite_falseI] by blast

lemmas step_exps_concat_lhs_unI = step_exps_reduce_singleI[OF step_concat_lhs_unI]
interpretation step_exps_concat_lhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>1 str. \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> e) \<leadsto>* unknown[str]: imm\<langle>sz\<^sub>1 + sz\<rangle>)\<close>
  apply standard
  using step_exps_concat_lhs_unI by blast

interpretation step_exps_concat_rhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>2 str. \<Delta> \<turnstile> (e \<copyright> unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto>* unknown[str]: imm\<langle>sz + sz\<^sub>2\<rangle>)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_concat_rhs_unI] by blast
(*
(* TODO might not need these for proofs *)
thm
   step_plusI.unk_lhsI step_plusI.unk_rhsI
   step_minusI.unk_lhsI step_minusI.unk_rhsI
   step_timesI.unk_lhsI step_timesI.unk_rhsI 
   step_divideI.unk_lhsI step_divideI.unk_rhsI 
   step_sdivideI.unk_lhsI step_sdivideI.unk_rhsI 
   step_modI.unk_lhsI step_modI.unk_rhsI 
   step_smodI.unk_lhsI step_smodI.unk_rhsI 
   step_lslI.unk_lhsI step_lslI.unk_rhsI 
   step_lsrI.unk_lhsI step_lsrI.unk_rhsI
   step_asrI.unk_lhsI step_asrI.unk_rhsI
   step_landI.unk_lhsI step_landI.unk_rhsI
   step_lorI.unk_lhsI step_lorI.unk_rhsI
   step_xorI.unk_lhsI step_xorI.unk_rhsI
   step_ltI.unk_lhsI step_ltI.unk_rhsI
   step_leI.unk_lhsI step_leI.unk_rhsI
   step_sltI.unk_lhsI step_sltI.unk_rhsI
   step_sleI.unk_lhsI step_sleI.unk_rhsI


lemmas step_exps_singleI = step_exps_load_un_addrI step_exps_not_trueI step_exps_not_falseI
  step_exps_uop_unk_notI step_exps_uop_unk_negI step_exps_uop_unkI step_exps_notI step_exps_negI
  step_exps_lop_unk_lhsI step_exps_lop_unk_rhsI step_exps_aop_unk_lhsI step_exps_aop_unk_rhsI
  step_exps_concatI 
  step_exps_extractI step_exps_extract_unI 
  step_exps_cast_lowI.word step_exps_cast_highI step_exps_cast_signedI step_exps_cast_unsignedI
    step_exps_cast_unkI
  step_exps_plusI step_exps_minusI step_exps_timesI step_exps_divI step_exps_sdivI step_exps_modI
    step_exps_signed_less_eqI step_exps_signed_lessI
  step_exps_load_byteI.syntaxs
  step_exps_load_un_memI.syntaxs
  step_exps_letI.syntaxs
  step_exps_store_valI.storage.syntaxs step_exps_store_valI.unknown.syntaxs
  step_exps_ite_trueI.syntaxs2
  step_exps_ite_falseI.syntaxs2
  step_exps_concat_lhs_unI.word_syntaxs step_exps_concat_rhs_unI.word_syntaxs
*)
text \<open>RHS values, assumptions - easy to discharge\<close>

lemmas step_exps_var_inI = step_exps_reduce_singleI[OF step_var_inI]

interpretation step_exps_var_inI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> name t ed sz. (name :\<^sub>t t, v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> (name :\<^sub>t t) \<leadsto>* e)\<close>
  apply (standard)
  using step_exps_var_inI by blast

lemmas step_exps_var_unI = step_exps_reduce_singleI[OF step_var_unI]

interpretation step_exps_ite_un: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str . type v\<^sub>1 = t' \<Longrightarrow> \<Delta> \<turnstile> ite unknown[str]: t e\<^sub>1 e\<^sub>2 \<leadsto>* unknown[str]: t')\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_ite_unI] by blast

interpretation step_exps_store_un_addr: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str ed sz. type v\<^sub>1 = t \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [unknown[str]: t', ed]:usz \<leftarrow> e\<^sub>2 \<leadsto>* unknown[str]: t)\<close>
  apply (standard)
  using step_exps_reduce_singleI[OF step_store_un_addrI] by blast


text \<open>Recursive on expressions only - medium to discharge\<close>

interpretation step_exps_load_byte_from_nextI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 v' sz ed e'. 
  \<lbrakk>num\<^sub>1 \<Colon> sz\<^sub>1 \<noteq> num\<^sub>2 \<Colon> sz\<^sub>2; \<Delta> \<turnstile> (e[num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz) \<leadsto>* e'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>1 \<leftarrow> v', sz][num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz \<leadsto>* e')\<close>
  apply (standard)
  apply (rule step_exps_reduceI)
  apply (rule step_load_byte_from_nextI, simp)
  by blast


interpretation step_exps_load_word_beI: exp_val_is_mem_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num sz e'. 
  \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; \<Delta> \<turnstile> ((e\<^sub>1[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> (e\<^sub>1[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) \<leadsto>* e'\<rbrakk> 
    \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz \<leadsto>* e')\<close>
  apply standard
  apply (rule step_exps_reduceI)
  apply (rule step_load_word_beI, simp)
  by assumption

lemmas step_exps_load_word_elI = step_exps_reduceI[OF step_load_word_elI]
interpretation step_exps_load_word_elI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> num sz e'. 
  \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; \<Delta> \<turnstile> (e\<^sub>1[succ e\<^sub>w, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<copyright> (e\<^sub>1[e\<^sub>w, el]:usz\<^sub>m\<^sub>e\<^sub>m)) \<leadsto>* e'\<rbrakk> 
    \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, el]:usz \<leadsto>* e')\<close>
  apply (standard)
  using step_exps_load_word_elI by blast

lemmas step_exps_store_word_beI = step_exps_reduceI[OF step_store_word_beI]
interpretation step_exps_store_word_beI: store_multiple_syntax \<open>\<lambda>e\<^sub>1 _ e\<^sub>2 _ _ e\<^sub>3 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> e e' sz.
  \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; e = e\<^sub>1 with [e\<^sub>2, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3]); 
   \<Delta> \<turnstile> (e with [succ e\<^sub>2, be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) \<leadsto>* e'\<rbrakk>
    \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:usz \<leftarrow> e\<^sub>3 \<leadsto>* e')\<close>
  apply (standard)
  using step_exps_store_word_beI by blast
                                                                  
lemmas step_exps_store_word_elI = step_exps_reduceI[OF step_store_word_elI]
interpretation step_exps_store_word_elI: store_multiple_syntax \<open>\<lambda>e\<^sub>1 _ e\<^sub>2 _ _ e\<^sub>3 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> e e' sz.
  \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; e = e\<^sub>1 with [e\<^sub>2, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3]);
   \<Delta> \<turnstile> (e with [succ e\<^sub>2, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) \<leadsto>* e'\<rbrakk>
    \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:usz \<leftarrow> e\<^sub>3 \<leadsto>* e')\<close>
  apply (standard)
  using step_exps_store_word_elI by blast

text \<open>Recursive - hard to discharge\<close>

lemmas step_exps_load_addrI = step_exps_reduceI[OF step_load_addrI]
lemmas step_exps_let_stepI = step_exps_reduceI[OF step_let_stepI]
lemmas step_exps_ite_elseI = step_exps_reduceI[OF step_ite_elseI]
lemmas step_exps_store_step_valI = step_exps_reduceI[OF step_store_step_valI]

lemmas step_exps_load_memI = step_exps_reduceI[OF step_load_memI]
interpretation step_exps_load_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e' ed sz. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; \<Delta> \<turnstile> e\<^sub>1'[e, ed]:usz \<leadsto>* e'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e, ed]:usz \<leadsto>* e')\<close>
  apply standard
  using step_exps_load_memI by blast

lemmas step_exps_store_addrI = step_exps_reduceI[OF step_store_addrI]
interpretation step_exps_store_addrI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2' e' en sz. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e \<leadsto>* e'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e \<leadsto>* e')\<close>
  apply (standard)
  using step_exps_store_addrI by blast

lemmas step_exps_store_memI = step_exps_reduceI[OF step_store_memI]
interpretation step_exps_store_memI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e' en sz x. \<lbrakk>\<Delta> \<turnstile> e \<leadsto> e'; \<Delta> \<turnstile> e' with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2 \<leadsto>* x\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2 \<leadsto>* x)\<close>
  apply (standard)
  using step_exps_store_memI by blast

interpretation step_exps_ite_condI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e' x. \<lbrakk>\<Delta> \<turnstile> e \<leadsto> e'; \<Delta> \<turnstile> ite e' e\<^sub>1 e\<^sub>2 \<leadsto>* x\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ite e e\<^sub>1 e\<^sub>2 \<leadsto>* x)\<close>
  apply standard
  using step_exps_reduceI[OF step_ite_condI] by blast

interpretation step_exps_ite_thenI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2' x. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2' e \<leadsto>* x\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e \<leadsto>* x)\<close>
  apply standard
  using step_exps_reduceI[OF step_ite_thenI] by blast

lemmas step_exps_uopI = step_exps_reduceI[OF step_uopI]
lemmas step_exps_reduce_notI = step_exps_uopI[where uop = Not, unfolded not_exp_def[symmetric]] 
lemmas step_exps_reduce_negI = step_exps_uopI[where uop = Neg, unfolded uminus_exp_def[symmetric]]
lemmas step_exps_cast_reduceI = step_exps_reduceI[OF step_cast_reduceI]
lemmas step_exps_concat_rhsI = step_exps_reduceI[OF step_concat_rhsI]
lemmas step_exps_extract_reduceI = step_exps_reduceI[OF step_extract_reduceI]

lemmas step_exps_concat_lhsI = step_exps_reduceI[OF step_concat_lhsI]
interpretation step_exps_concat_lhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' x. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; \<Delta> \<turnstile> (e\<^sub>1' \<copyright> e) \<leadsto>* x\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e) \<leadsto>* x)\<close>
  apply (standard)
  using step_exps_concat_lhsI by blast

(* TODO *)
subsection \<open>Bop\<close>

lemmas step_exps_bop_lhsI = step_exps_reduceI[OF step_bop_lhsI]

lemmas step_exps_bop_rhsI = step_exps_reduceI[OF step_bop_rhsI]
interpretation step_exps_bop_rhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 bop e\<^sub>2' e\<^sub>3. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp e bop e\<^sub>2' \<leadsto>* e\<^sub>3 \<Longrightarrow> \<Delta> \<turnstile> BinOp e bop e\<^sub>2 \<leadsto>* e\<^sub>3)\<close>
  apply (standard)
  using step_exps_bop_rhsI by blast

context bop_lemmas
begin

lemma step_exps_lhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> and \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1' e\<^sub>2 \<leadsto>* e\<^sub>3\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto>* e\<^sub>3\<close>
  using assms unfolding bop_simps by (rule step_exps_bop_lhsI)

sublocale step_exps_rhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 bop e\<^sub>2' e\<^sub>3. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> bop_fun e e\<^sub>2' \<leadsto>* e\<^sub>3 \<Longrightarrow> \<Delta> \<turnstile> bop_fun e e\<^sub>2 \<leadsto>* e\<^sub>3)\<close>
  apply standard
  unfolding bop_simps using step_exps_bop_rhsI by blast

end

context aop_lemmas
begin

lemma step_exps_unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto>* (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_exps_aop_unk_lhsI)

lemma step_exps_unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto>* (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_exps_aop_unk_rhsI)

end

context lop_lemmas
begin

lemma step_exps_unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto>* (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_exps_lop_unk_lhsI)

lemma step_exps_unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto>* (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_exps_lop_unk_rhsI)

end

method solve_expsI_scaffold methods recurs solve_exp solve_type uses add = (
    \<comment> \<open>Try added assumptions, they must solve the goal though\<close>
  (solves \<open>rule add\<close>) |

  (rule step_exps_var_inI.is_val[rotated], solve_var_inI add: add, solve_is_valI add: add) |
  (rule step_exps_var_inI.is_val[rotated], solve_in_var add: add, solve_is_valI add: add) | \<comment> \<open>Remove this method\<close>

  \<comment> \<open>Can the below rule be removed?\<close>
  (rule step_exps_plusI step_exps_minusI step_exps_landI step_exps_lorI step_exps_lslI
        step_exps_lsrI step_exps_less_eqI step_exps_lessI step_exps_eq_sameI
        step_exps_not_falseI step_exps_not_trueI) |          

  (rule step_exps_eq_diffI, solve_bv_neqI) |

  (rule step_exps_notI.is_word step_exps_negI.is_word step_exps_cast_highI.is_word 
        step_exps_cast_lowI.is_word step_exps_cast_signedI.is_word step_exps_cast_unsignedI.is_word, 
      solve_is_wordI) |

  (rule step_exps_plusI.is_word2 step_exps_minusI.is_word2 step_exps_timesI.is_word2
        step_exps_divI.is_word2 step_exps_sdivI.is_word2 step_exps_modI.is_word2 
        step_exps_smodI.is_word2 step_exps_signed_less_eqI.is_word2 step_exps_signed_lessI.is_word2
        step_exps_lessI.is_word2 step_exps_less_eqI.is_word2 step_exps_lslI.is_word2
        step_exps_lsrI.is_word2 step_exps_asrI.is_word2 step_exps_landI.is_word2
        step_exps_lorI.is_word2 step_exps_xorI.is_word2 step_exps_concatI.is_word2
        step_exps_eqI'.is_word2,
     solve_is_wordI, solve_is_wordI) |

  (rule plus.step_exps_lhsI minus.step_exps_lhsI times.step_exps_lhsI divide.step_exps_lhsI
        sdivide.step_exps_lhsI mod.step_exps_lhsI smod.step_exps_lhsI le.step_exps_lhsI
        sle.step_exps_lhsI lt.step_exps_lhsI slt.step_exps_lhsI lsl.step_exps_lhsI 
        lsr.step_exps_lhsI asr.step_exps_lhsI land.step_exps_lhsI lor.step_exps_lhsI 
        xor.step_exps_lhsI step_exps_bop_lhsI step_exps_cast_reduceI step_exps_store_step_valI
        step_exps_reduce_notI step_exps_reduce_negI step_exps_concat_rhsI,
     solve_exp, (recurs | succeed)) |

  (rule plus.step_exps_rhsI.is_word minus.step_exps_rhsI.is_word times.step_exps_rhsI.is_word
        divide.step_exps_rhsI.is_word sdivide.step_exps_rhsI.is_word mod.step_exps_rhsI.is_word
        smod.step_exps_rhsI.is_word le.step_exps_rhsI.is_word sle.step_exps_rhsI.is_word 
        lt.step_exps_rhsI.is_word slt.step_exps_rhsI.is_word lsl.step_exps_rhsI.is_word
        lsr.step_exps_rhsI.is_word asr.step_exps_rhsI.is_word land.step_exps_rhsI.is_word
        lor.step_exps_rhsI.is_word xor.step_exps_rhsI.is_word step_exps_bop_rhsI.is_word
        step_exps_concat_lhsI.is_word step_exps_store_addrI.is_word,
     solve_is_wordI, solve_exp, (recurs | succeed)) |

  (rule step_exps_valI.is_val, solve_is_valI) |

  \<comment> \<open>Below this is unsorted\<close>
  (((rule step_exps_load_word_elI.storage.word step_exps_load_word_elI.storage.plus | 
    (rule step_exps_load_word_elI.storage.is_word, solve_is_wordI)) | 
    (rule step_exps_load_word_elI.storage_addr.word step_exps_load_word_elI.storage_addr.plus | 
    (rule step_exps_load_word_elI.storage_addr.is_word, solve_is_wordI)), 
     solve_type), 
    (unfold load_byte_minus_simps)?,
    linarith, (recurs | succeed)
  ) |

  ((rule step_exps_load_word_beI.storage | rule step_exps_load_word_beI.storage_addr, solve_type), linarith, (recurs | succeed)) |
  (rule step_exps_load_memI.word step_exps_load_memI.plus step_exps_load_addrI, solve_exp, (recurs | succeed)) |

  \<comment> \<open>Store\<close>
  (rule step_exps_store_valI.succ.storage_addr.xtract step_exps_store_valI, solve_type) |
  (rule step_exps_store_word_elI.succ.storage.xtract step_exps_store_word_elI.word.storage.word 
        step_exps_store_word_beI.succ.storage.xtract step_exps_store_word_beI.word.storage.word,
   (unfold load_byte_minus_simps)?,
   linarith, standard, (recurs | succeed)) |

  (rule step_exps_store_word_elI.succ.storage_addr.xtract 
        step_exps_store_word_elI.word.storage_addr.xtract
        step_exps_store_word_elI.plus.val.xtract 
        step_exps_store_word_elI.plus.val.word
        step_exps_store_word_elI.word.val.word  
        step_exps_store_word_beI.succ.storage_addr.xtract
        step_exps_store_word_beI.word.storage_addr.xtract
        step_exps_store_word_beI.word.val.word, 
   solve_type, linarith, standard, (recurs | succeed)) |

  (rule step_exps_store_memI.succ.xtract step_exps_store_memI.plus.xtract
        step_exps_store_memI.word.xtract step_exps_store_memI.plus.word
        step_exps_store_memI.word.word step_exps_store_memI
        
        , solve_exp, (recurs | succeed))
  
(*
   \<open>Reflexive case\<close>
   \<open>(rule step_exps_reflI) \<comment> TODO added ?\<close>*)
)

method solve_expsI uses add = (
  solve_expsI_scaffold \<open>solve_expsI add: add\<close> \<open>solve_expI add: add\<close> solve_typeI add: add
)

lemmas REFL = step_exps_reflI
lemmas REDUCE = step_exps_reduceI

end