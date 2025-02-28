section \<open>Introduction rules\<close>

theory Expression_Intros
  imports Expression_Rules Solve_BitVector
begin

subsection \<open>Preliminaries\<close>

subsection \<open>Vars\<close>

lemmas step_var_inI[intro] = VarIn
lemmas step_var_unI[intro] = VarNotIn

interpretation step_var_inI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> name t ed sz. (name :\<^sub>t t, v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> (name :\<^sub>t t) \<leadsto> e)\<close>
  apply (standard, simp)
  by (rule step_var_inI)

subsection \<open>Loads\<close>

lemmas step_load_addrI[intro] = LoadStepAddr
lemmas step_load_memI[intro] = LoadStepMem
lemmas step_load_byteI[intro] = LoadByte
lemmas step_load_byte_from_nextI[intro] = LoadByteFromNext
lemmas step_load_un_addrI[intro] = LoadUnAddr
lemmas step_load_un_memI[intro] = LoadUnMem
lemmas step_load_word_beI[intro] = LoadWordBe
lemmas step_load_word_elI[intro] = LoadWordEl

interpretation step_load_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' ed sz. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e, ed]:usz \<leadsto> (e\<^sub>1'[e, ed]:usz))\<close>
  by (standard, simp, rule step_load_memI)

interpretation step_load_un_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> str t ed sz. \<Delta> \<turnstile> (unknown[str]: t)[e, ed]:usz \<leadsto> unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (standard, simp, rule step_load_un_memI)

interpretation step_load_byteI: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v'. (\<And>\<Delta> sz v ed. \<Delta> \<turnstile> v[w\<^sub>w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e)\<close>
  apply (standard, auto)
  using step_load_byteI by force

interpretation step_load_byte_from_nextI: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v. 
    (\<And>\<Delta> w sz v' ed. w \<noteq> w\<^sub>w \<Longrightarrow> \<Delta> \<turnstile> v[w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> (e[w\<^sub>e, ed]:usz))\<close>
  apply (standard, simp)                             
  using step_load_byte_from_nextI by force

interpretation step_load_word_beI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, be]:usz \<leadsto> ((e\<^sub>1[e\<^sub>w, be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> (e\<^sub>1[succ e\<^sub>w, be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close>
  apply (standard)
  using step_load_word_beI by blast

interpretation step_load_word_elI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, el]:usz \<leadsto> (e\<^sub>1[succ e\<^sub>w, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<copyright> (e\<^sub>1[e\<^sub>w, el]:usz\<^sub>m\<^sub>e\<^sub>m)))\<close>
  apply (standard)
  using step_load_word_elI by blast

subsection \<open>Stores\<close>

lemmas step_store_step_valI[intro] = StoreStepVal

lemmas step_store_addrI[intro] = StoreStepAddr
interpretation step_store_addrI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2' en sz. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e))\<close>
  by (standard, simp, rule step_store_addrI)

lemmas step_store_un_addrI[intro] = StoreUnAddr
interpretation step_store_un_addrI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str ed sz. type v\<^sub>1 = t \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [unknown[str]: t', ed]:usz \<leftarrow> e\<^sub>2 \<leadsto> unknown[str]: t)\<close>
  by (standard, simp, rule step_store_un_addrI)

lemmas step_store_memI[intro] = StoreStepMem
interpretation step_store_memI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e' en sz. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> e with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e' with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2))\<close>
  by (standard, simp, rule step_store_memI)

lemmas step_store_valI[intro] = StoreVal
interpretation step_store_valI: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> en. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>3 \<leadsto> (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m]))\<close>
  by (standard, use step_store_valI in blast)

lemmas step_store_word_beI[intro] = StoreWordBe
interpretation step_store_word_beI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num  sz  e. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz \<leftarrow> e\<^sub>2 \<leadsto> ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, simp, intro step_store_word_beI refl)
  
lemmas step_store_word_elI[intro] = StoreWordEl
interpretation step_store_word_elI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num sz e. 
  \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leftarrow> e\<^sub>2 \<leadsto> ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, simp, intro step_store_word_elI refl)

subsection \<open>Let\<close>

lemmas step_let_stepI[intro] = LetStep
lemmas step_letI[intro] = Let

interpretation step_letI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' var. \<Delta> \<turnstile> Let var e e' \<leadsto> [v\<sslash>var]e')\<close>
  by (standard, simp, rule step_letI)

subsection \<open>Ite\<close>

lemmas step_ite_condI[intro] = IfStepCond
lemmas step_ite_thenI[intro] = IfStepThen
lemmas step_ite_elseI[intro] = IfStepElse
lemmas step_ite_trueI[intro] = IfTrue
lemmas step_ite_falseI[intro] = IfFalse
lemmas step_ite_unI[intro] = IfUnknown

interpretation step_ite_thenI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e \<leadsto> ite e\<^sub>1 e\<^sub>2' e)\<close>
  by (standard, simp, rule step_ite_thenI)

interpretation step_ite_condI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e'. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> ite e e\<^sub>1 e\<^sub>2 \<leadsto> ite e' e\<^sub>1 e\<^sub>2)\<close>
  by (standard, simp, rule step_ite_condI)

interpretation step_ite_trueI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto> e\<^sub>1)\<close>
  by (standard, simp, rule step_ite_trueI)

interpretation step_ite_falseI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto> e\<^sub>2)\<close>
  by (standard, simp, rule step_ite_falseI)

interpretation step_ite_unI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str . type v\<^sub>1 = t' \<Longrightarrow> \<Delta> \<turnstile> ite unknown[str]: t e\<^sub>1 e\<^sub>2 \<leadsto> unknown[str]: t')\<close>
  by (standard, simp, rule step_ite_unI)


subsection \<open>Bop\<close>

lemmas step_bop_lhsI[intro] = BopLhs
lemmas step_bop_rhsI[intro] = BopRhs

interpretation step_bop_rhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 bop e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp e bop e\<^sub>2 \<leadsto> BinOp e bop e\<^sub>2')\<close>
  by (standard, simp, rule step_bop_rhsI)

context bop_lemmas
begin

lemma step_exp_lhsI[intro]:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> bop_fun e\<^sub>1' e\<^sub>2\<close>
  using assms unfolding bop_simps by (rule step_bop_lhsI)

sublocale step_exp_rhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> bop_fun e e\<^sub>2 \<leadsto> bop_fun e e\<^sub>2')\<close>
  apply standard
  unfolding bop_simps by (simp, rule step_bop_rhsI)

end

lemmas step_aop_unk_rhsI[intro] = AopUnkRhs
lemmas step_aop_unk_lhsI[intro] = AopUnkLhs

context aop_lemmas
begin

lemma step_exp_unk_lhsI[intro]: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_lhsI)

lemma step_exp_unk_rhsI[intro]: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_rhsI)

end

lemmas step_lop_unk_rhsI[intro] = LopUnkRhs
lemmas step_lop_unk_lhsI[intro] = LopUnkLhs

context lop_lemmas
begin

lemma step_exp_unk_lhsI[intro]: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_lhsI)

lemma step_exp_unk_rhsI[intro]: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_rhsI)

end

lemmas step_plusI[intro] = Plus
interpretation step_plusI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 + e\<^sub>2) \<leadsto> (e\<^sub>1 +\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_plusI by blast

lemmas step_minusI[intro] = Minus
interpretation step_minusI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 - e\<^sub>2) \<leadsto> (e\<^sub>1 -\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_minusI by blast

lemmas step_timesI[intro] = Times
interpretation step_timesI: exp_val_word_fixed_sz_syntax2 
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 * e\<^sub>2) \<leadsto> (e\<^sub>1 *\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_timesI by blast

lemmas step_divI[intro] = Div
interpretation step_divI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 div e\<^sub>2) \<leadsto> (e\<^sub>1 div\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_divI by blast

lemmas step_sdivI[intro] = SDiv
interpretation step_sdivI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 sdiv e\<^sub>2) \<leadsto> (e\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_sdivI by blast

lemmas step_modI[intro] = Mod
interpretation step_modI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 mod e\<^sub>2) \<leadsto> (e\<^sub>1 %\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_modI by blast

lemmas step_smodI[intro] = SMod
interpretation step_smodI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 smod e\<^sub>2) \<leadsto> (e\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_smodI by blast

lemmas step_lslI[intro] = Lsl
interpretation step_lslI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 << e\<^sub>2) \<leadsto> (e\<^sub>1 <<\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_lslI by blast

lemmas step_lsrI[intro] = Lsr
interpretation step_lsrI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 >> e\<^sub>2) \<leadsto> (e\<^sub>1 >>\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_lsrI by blast

lemmas step_asrI[intro] = Asr
interpretation step_asrI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 >>> e\<^sub>2) \<leadsto> (e\<^sub>1 >>>\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_asrI by blast

lemmas step_landI[intro] = LAnd
interpretation step_landI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 && e\<^sub>2) \<leadsto> (e\<^sub>1 &\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_landI by blast

lemmas step_lorI[intro] = LOr
interpretation step_lorI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 || e\<^sub>2) \<leadsto> (e\<^sub>1 |\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_lorI by blast

lemmas step_xorI[intro] = XOr
interpretation step_xorI: exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 xor e\<^sub>2) \<leadsto> (e\<^sub>1 xor\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_xorI by blast

lemmas step_eq_sameI[intro] = EqSame
lemma step_eqI:
  assumes \<open>(num1 \<Colon> sz1) =\<^sub>b\<^sub>v (num2 \<Colon> sz2) = (true::val)\<close>
    shows \<open>\<Delta> \<turnstile> BinOp (num1 \<Colon> sz1) (LOp Eq) (num2 \<Colon> sz2) \<leadsto> true\<close>
  using assms step_eq_sameI 
  by (metis Val_simp_word bv_negation_true_false bv_neq_true one_neq_zero word_bool_inject(1))

lemmas step_eq_diffI[intro] = EqDiff
interpretation step_eq_diffI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta>. w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = true \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 (LOp Eq) e\<^sub>2 \<leadsto> false)\<close>
  apply (standard)
  using step_eq_diffI by force


lemma step_eqI':
 \<open>\<Delta>' \<turnstile> BinOp (num1 \<Colon> sz1) (LOp Eq) (num2 \<Colon> sz2) \<leadsto> ((num1 \<Colon> sz1) =\<^sub>b\<^sub>v (num2 \<Colon> sz2))\<close>
proof (cases \<open>(num1 \<Colon> sz1) =\<^sub>b\<^sub>v (num2 \<Colon> sz2) = (true::exp)\<close>)
  case True
  show ?thesis 
    unfolding True apply (rule step_eqI)
    by (metis True bv_eq bv_not_eq word_inject)
next
  case False
  then show ?thesis 
    using step_eq_diffI by (smt (z3) bv_eq bv_neq_true bv_not_eq word_inject)
qed

interpretation step_eqI': exp_val_word_fixed_sz_syntax2 \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) \<leadsto> (e\<^sub>1 =\<^sub>b\<^sub>v e\<^sub>2))\<close> sz sz
  apply (standard)
  using step_eqI' by blast

lemmas step_neq_sameI[intro] = NeqSame
lemmas step_neq_diffI[intro] = NeqDiff

lemmas step_lessI[intro] = Less
lemmas step_less_eqI[intro] = LessEq
lemmas step_signed_lessI[intro] = SignedLess
lemmas step_signed_less_eqI[intro] = SignedLessEq

subsection \<open>Uop\<close>

lemmas step_uopI[intro] = Uop
lemmas step_reduce_notI[intro] = step_uopI[where uop = Not, unfolded not_exp_def[symmetric]] 
lemmas step_reduce_negI[intro] = step_uopI[where uop = Neg, unfolded uminus_exp_def[symmetric]] 

lemmas step_notI[intro] = Not
interpretation step_notI: exp_val_word_fixed_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (\<sim> e\<^sub>1) \<leadsto> (~\<^sub>b\<^sub>v e\<^sub>1))\<close> sz
  apply (standard)
  using step_notI by blast

lemmas step_negI[intro] = Neg
interpretation step_negI: exp_val_word_fixed_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (- e\<^sub>1) \<leadsto> (-\<^sub>b\<^sub>v e\<^sub>1))\<close> sz
  apply (standard)
  using step_negI by blast

lemmas step_uop_unkI[intro] = UopUnk

lemma step_uop_unk_notI: \<open>\<Delta> \<turnstile> (\<sim> (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding not_exp_def by (rule step_uop_unkI)

lemma step_uop_unk_negI: \<open>\<Delta> \<turnstile> (- (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding uminus_exp_def by (rule step_uop_unkI)

lemma step_not_falseI: \<open>\<Delta> \<turnstile> (\<sim>false) \<leadsto> true\<close>
  using bv_negation_false_true step_notI by (metis)

lemma step_not_trueI: \<open>\<Delta> \<turnstile> (\<sim>true) \<leadsto> false\<close>
  using bv_negation_true_false step_notI by (metis)

subsection \<open>Concat\<close>

lemmas step_concat_rhsI[intro] = ConcatRhs

lemmas step_concatI[intro] = Concat
interpretation step_concatI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> (e\<^sub>1 \<cdot> e\<^sub>2))\<close>
  apply standard
  using step_concatI by force

lemmas step_concat_lhsI[intro] = ConcatLhs
interpretation step_concat_lhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e) \<leadsto> (e\<^sub>1' \<copyright> e))\<close>
  by (standard, use step_concat_lhsI in blast)

lemmas step_concat_lhs_unI[intro] = ConcatLhsUn
interpretation step_concat_lhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>1 str. \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> e) \<leadsto> unknown[str]: imm\<langle>sz\<^sub>1 + sz\<rangle>)\<close>
  apply standard
  using step_concat_lhs_unI by force

lemmas step_concat_rhs_unI[intro] = ConcatRhsUn
interpretation step_concat_rhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>2 str. \<Delta> \<turnstile> (e \<copyright> unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> unknown[str]: imm\<langle>sz + sz\<^sub>2\<rangle>)\<close>
  apply standard
  using step_concat_rhs_unI by force

subsection \<open>Extract\<close>

lemmas step_extract_reduceI[intro] = ExtractReduce
lemmas step_extract_unI[intro] = ExtractUn
lemmas step_extractI[intro] = Extract

subsection \<open>Cast\<close>

lemmas step_cast_reduceI[intro] = CastReduce
lemmas step_cast_unkI[intro] = CastUnk
lemmas step_cast_lowI[intro] = CastLow
interpretation step_cast_lowI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> low:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_lowI by force

lemmas step_cast_highI[intro] = CastHigh
interpretation step_cast_highI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ sz'. (\<And>\<Delta> sz. \<Delta> \<turnstile> high:sz[e] \<leadsto> ext e \<sim> hi : sz' - 1 \<sim> lo : sz' - sz)\<close>
  apply standard
  using step_cast_highI by force

lemmas step_cast_signedI[intro] = CastSigned 
interpretation step_cast_signedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> extend:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_signedI by force

lemmas step_cast_unsignedI[intro] = CastUnsigned
interpretation step_cast_unsignedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> pad:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_unsignedI by force

lemma neq_64_Suc0: \<open>64 \<noteq> Suc 0\<close>
  by simp

lemmas solve_in_var_simps[bil_var_simps] = string_simps var_syntax_class.var_eq Type.inject 
  neq_64_Suc0 not_Cons_self 

method simp_capture_avoid uses add = (simp (no_asm) only: capture_avoiding_sub_simps)

method solve_expI_scaffold methods recurs solve_type uses add = (
    \<comment> \<open>Vars\<close>
  (rule step_var_inI.is_val[rotated], solve_var_inI add: add, solve_is_valI) |
\<comment> \<open>  (rule step_var_inI.is_val[rotated], solve_in_var add: add, solve_is_valI) | Remove this method\<close>
  (rule step_var_unI, blast) |

  \<comment> \<open>Loads\<close>
  (rule step_load_un_addrI step_load_byteI.word.word 
        step_load_byteI.word.unknown 
        step_load_byteI.word.xtract step_load_byteI.word.succ step_load_byteI.word.val 
        step_load_byteI.succ.word   
        step_load_byteI.succ.unknown step_load_byteI.succ.xtract 
        step_load_byteI.succ.succ step_load_byteI.succ.val) |
  (rule step_load_byteI.is_word.word 
        step_load_byteI.is_word.unknown step_load_byteI.is_word.xtract step_load_byteI.is_word.succ 
        step_load_byteI.is_word.val, solve_is_wordI) |

  ((rule step_load_byte_from_nextI.word.storage step_load_byte_from_nextI.succ.storage
         step_load_byte_from_nextI.plus.storage step_load_byte_from_nextI | 
   (rule step_load_byte_from_nextI.is_word.storage, solve_is_wordI)), 
   solve_word_neq add: add) |

  ((rule step_load_word_elI.storage.word step_load_word_elI.storage.succ 
         step_load_word_elI.storage.plus
         step_load_word_beI.storage.word step_load_word_beI.storage.succ 
         step_load_word_beI.storage.plus | 
    (rule step_load_word_elI.storage.is_word step_load_word_beI.storage.is_word, solve_is_wordI) |
   ((rule step_load_word_elI.storage_addr.word step_load_word_elI.storage_addr.succ
          step_load_word_elI.storage_addr.plus
          step_load_word_beI.storage_addr.word step_load_word_beI.storage_addr.succ
          step_load_word_beI.storage_addr.plus | 
     (rule step_load_word_elI.storage_addr.is_word step_load_word_beI.storage_addr.is_word, solve_is_wordI)), 
     solve_type)
   ), 
   (unfold load_byte_minus_simps)?,
   linarith) |

  (rule step_load_memI.plus step_load_memI.word step_load_addrI, recurs) |

  \<comment> \<open>Store\<close>
  (rule step_store_valI.word.storage.xtract step_store_valI.succ.storage.xtract) |
  (rule step_store_valI.word.storage_addr.xtract step_store_valI.word.val.xtract
        step_store_valI.succ.storage_addr.xtract step_store_valI.succ.val.xtract, solve_type) |

  (rule step_store_step_valI, recurs) |

  \<comment> \<open>Let\<close>
  (rule step_letI.is_val, solve_is_valI, simp_capture_avoid?) |
  (rule step_let_stepI, recurs) |

  \<comment> \<open>Ite\<close>
  (rule step_ite_elseI, recurs) |

  \<comment> \<open>Bop\<close>

  \<comment> \<open>Eq\<close>
  (rule step_eqI, assumption) |
  (rule step_eq_diffI, (assumption | (rule bv_neq_true, assumption))) |

  \<comment> \<open>New\<close>
  (rule step_not_trueI step_not_falseI step_uop_unk_notI step_uop_unk_negI step_uop_unkI step_notI
       step_negI) |

  (rule step_cast_lowI.is_word step_cast_highI.is_word step_cast_signedI.is_word 
        step_cast_unsignedI.is_word step_notI.is_sz_word step_negI.is_sz_word, solve_is_wordI) |

  (rule step_plusI.is_word2 step_minusI.is_word2 step_timesI.is_word2 step_divI.is_word2 
        step_sdivI.is_word2 step_modI.is_word2 step_smodI.is_word2 step_lslI.is_word2 
        step_lsrI.is_word2 step_asrI.is_word2 step_landI.is_word2 step_lorI.is_word2 
        step_xorI.is_word2 step_concatI.is_word2 step_eqI'.is_word2 ,
     solve_is_wordI, solve_is_wordI) |

  (rule plus.step_exp_lhsI minus.step_exp_lhsI times.step_exp_lhsI divide.step_exp_lhsI
        sdivide.step_exp_lhsI mod.step_exp_lhsI smod.step_exp_lhsI lsl.step_exp_lhsI 
        lsr.step_exp_lhsI asr.step_exp_lhsI land.step_exp_lhsI lor.step_exp_lhsI xor.step_exp_lhsI
        step_concat_rhsI step_bop_lhsI,
      recurs) |

  (rule plus.step_exp_rhsI.is_val minus.step_exp_rhsI.is_val times.step_exp_rhsI.is_val
        divide.step_exp_rhsI.is_val sdivide.step_exp_rhsI.is_val mod.step_exp_rhsI.is_val
        smod.step_exp_rhsI.is_val lsl.step_exp_rhsI.is_val lsr.step_exp_rhsI.is_val
        asr.step_exp_rhsI.is_val land.step_exp_rhsI.is_val lor.step_exp_rhsI.is_val 
        xor.step_exp_rhsI.is_val step_concat_lhsI.is_val step_bop_rhsI.is_val, 
      solve_is_valI, recurs) |

   \<comment> \<open>End of New\<close>

   \<comment> \<open>Uop\<close>
  (rule step_uopI step_reduce_notI step_reduce_negI, recurs) |

  \<comment> \<open>Concat\<close>
  (rule step_concat_lhs_unI step_concat_rhs_unI, solve_type) |

  \<comment> \<open>Extract\<close>
  (rule step_extractI step_extract_unI) | 
  (rule step_extract_reduceI, recurs) |

  \<comment> \<open>Cast\<close>
  (rule step_cast_unkI) |
  (rule step_cast_reduceI, recurs)
)

method solve_expI uses add = (
  solve_expI_scaffold \<open>solve_expI add: add\<close> solve_typeI add: add
)

text \<open>Match names of the rules from the manual\<close>

lemmas VAR_IN = step_var_inI
lemmas VAR_UNKNOWN = step_var_unI

lemmas LOAD_STEP_ADDR = step_load_addrI
lemmas LOAD_STEP_MEM = step_load_memI
lemmas LOAD_BYTE = step_load_byteI
lemmas LOAD_BYTE_FROM_NEXT = step_load_byte_from_nextI
lemmas LOAD_UN_MEM = step_load_un_memI
lemmas LOAD_UN_ADDR = step_load_un_addrI
lemmas LOAD_WORD_BE = step_load_word_beI
lemmas LOAD_WORD_EL = step_load_word_elI

lemmas STORE_STEP_VAL = step_store_step_valI
lemmas STORE_STEP_ADDR = step_store_addrI 
lemmas STORE_STEP_MEM = step_store_memI 
lemmas STORE_WORD_BE = step_store_word_beI
lemmas STORE_WORD_EL = step_store_word_elI
lemmas STORE_VAL = step_store_valI
lemmas STORE_UN_ADDR = step_store_un_addrI

lemmas LET_STEP = step_let_stepI
lemmas LET = step_letI

lemmas ITE_STEP_COND = step_ite_condI
lemmas ITE_STEP_THEN = step_ite_thenI
lemmas ITE_STEP_ELSE = step_ite_elseI
lemmas ITE_TRUE = step_ite_trueI
lemmas ITE_FALSE = step_ite_falseI
lemmas ITE_UNK = step_ite_unI

lemmas BOP_RHS = step_bop_rhsI
lemmas BOP_LHS = step_bop_lhsI

lemmas AOP_UNK_RHS = step_aop_unk_rhsI
lemmas AOP_UNK_LHS = step_aop_unk_lhsI

lemmas LOP_UNK_RHS = step_lop_unk_rhsI
lemmas LOP_UNK_LHS = step_lop_unk_lhsI

lemmas PLUS = step_plusI
lemmas MINUS = step_minusI
lemmas TIMES = step_timesI
lemmas DIV = step_divI
lemmas SDIV = step_sdivI
lemmas MOD = step_modI
lemmas SMOD = step_smodI
lemmas LSL = step_lslI
lemmas LSR = step_lsrI.word.word
lemmas ASR = step_asrI
lemmas LAND = step_landI
lemmas LOR = step_lorI
lemmas XOR = step_xorI

lemmas EQ_SAME = step_eq_sameI
lemmas EQ_DIFF = step_eq_diffI

lemmas NEQ_SAME = step_neq_sameI
lemmas NEQ_DIFF = step_neq_diffI

lemmas LESS = step_lessI
lemmas LESS_EQ = step_less_eqI
lemmas SIGNED_LESS = step_signed_lessI
lemmas SIGNED_LESS_EQ = step_signed_less_eqI

lemmas UOP = step_uopI
lemmas UOP_UNK = step_uop_unkI

lemmas NOT = step_notI
lemmas NEG = step_negI

lemmas CONCAT_RHS = step_concat_rhsI
lemmas CONCAT_LHS = step_concat_lhsI
lemmas CONCAT_RHS_UN = step_concat_rhs_unI
lemmas CONCAT_LHS_UN = step_concat_lhs_unI
lemmas CONCAT = step_concatI

lemmas EXTRACT_REDUCE = step_extract_reduceI
lemmas EXTRACT_UN = step_extract_unI
lemmas EXTRACT = step_extractI

lemmas CAST_REDUCE = step_cast_reduceI
lemmas CAST_UNK = step_cast_unkI
lemmas CAST_HIGH = step_cast_highI
lemmas CAST_LOW = step_cast_lowI
lemmas CAST_SIGNED = step_cast_signedI
lemmas CAST_UNSIGNED = step_cast_unsignedI

lemmas(in word_constructor) SUCC = succI

end
