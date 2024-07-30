
section \<open>Introduction rules\<close>

theory Expression_Intros
  imports Expression_Rules
          "HOL-Eisbach.Eisbach_Tools"
begin

subsection \<open>Preliminaries\<close>

(* match_inline method - preserves schematic variables during sublocaling 
   (I HAVE NO IDEA IF THIS HAS SIDE EFFECTS )*)
ML_file \<open>../../isabil/extras/match_inline_method.ML\<close>

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)
no_notation (ASCII) HOL.Not (\<open>~ _\<close> [40] 40)

subsection \<open>Vars\<close>

lemmas step_var_inI = VarIn
lemmas step_var_unI = VarNotIn

interpretation step_var_inI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> name t ed sz. (name :\<^sub>t t, v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> (name :\<^sub>t t) \<leadsto> e)\<close>
  apply (standard, simp)
  by (rule step_var_inI)

subsection \<open>Loads\<close>

lemmas step_load_addrI = LoadStepAddr
lemmas step_load_memI = LoadStepMem
lemmas step_load_byteI = LoadByte
lemmas step_load_byte_from_nextI = LoadByteFromNext
lemmas step_load_un_addrI = LoadUnAddr
lemmas step_load_un_memI = LoadUnMem
lemmas step_load_word_beI = LoadWordBe
lemmas step_load_word_elI = LoadWordEl

interpretation step_load_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' ed sz. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e, ed]:usz \<leadsto> (e\<^sub>1'[e, ed]:usz))\<close>
  by (standard, simp, rule step_load_memI)

interpretation step_load_un_memI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> str t ed sz. \<Delta> \<turnstile> (unknown[str]: t)[e, ed]:usz \<leadsto> unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (standard, simp, rule step_load_un_memI)

interpretation step_load_byteI: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v'. (\<And>\<Delta> sz v ed. \<Delta> \<turnstile> v[w\<^sub>w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e)\<close>
  apply (standard, auto)
  using step_load_byteI by force


interpretation step_load_byte_from_nextI: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v. (\<And>\<Delta> w sz v' ed. w \<noteq> w\<^sub>w \<Longrightarrow> \<Delta> \<turnstile> v[w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> (e[w\<^sub>e, ed]:usz))\<close>
  apply (standard, simp)                             
  using step_load_byte_from_nextI by force

interpretation step_load_word_beI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, be]:usz \<leadsto> ((e\<^sub>1[e\<^sub>w, be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (e\<^sub>1[succ e\<^sub>w, be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close>
  apply (standard)
  using step_load_word_beI by blast

interpretation step_load_word_elI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, el]:usz \<leadsto> (e\<^sub>1[succ e\<^sub>w, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (e\<^sub>1[e\<^sub>w, el]:usz\<^sub>m\<^sub>e\<^sub>m)))\<close>
  apply (standard)
  using step_load_word_elI by blast

subsection \<open>Stores\<close>

lemmas step_store_step_valI = StoreStepVal

lemmas step_store_addrI = StoreStepAddr
interpretation step_store_addrI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2' en sz. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e))\<close>
  by (standard, simp, rule step_store_addrI)

lemmas step_store_un_addrI = StoreUnAddr
interpretation step_store_un_addrI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str ed sz. type v\<^sub>1 = t \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [unknown[str]: t', ed]:usz \<leftarrow> e\<^sub>2 \<leadsto> unknown[str]: t)\<close>
  by (standard, simp, rule step_store_un_addrI)

lemmas step_store_memI = StoreStepMem
interpretation step_store_memI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e' en sz. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> e with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e' with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2))\<close>
  by (standard, simp, rule step_store_memI)

lemmas step_store_valI = StoreVal
interpretation step_store_valI: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> en. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>3 \<leadsto> (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m]))\<close>
  by (standard, simp, rule step_store_valI)

lemmas step_store_word_beI = StoreWordBe
interpretation step_store_word_beI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num  sz  e. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz;
   e = e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, simp, intro step_store_word_beI refl)
  
lemmas step_store_word_elI = StoreWordEl
interpretation step_store_word_elI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num sz e. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz;
   e = e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, simp, intro step_store_word_elI refl)

subsection \<open>Let\<close>

lemmas step_let_stepI = LetStep
lemmas step_letI = Let

interpretation step_letI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' var. \<Delta> \<turnstile> Let var e e' \<leadsto> [v\<sslash>var]e')\<close>
  by (standard, simp, rule step_letI)

subsection \<open>Ite\<close>

lemmas step_ite_condI = IfStepCond
lemmas step_ite_thenI = IfStepThen
lemmas step_ite_elseI = IfStepElse
lemmas step_ite_trueI = IfTrue
lemmas step_ite_falseI = IfFalse
lemmas step_ite_unI = IfUnknown

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

lemmas step_bop_lhsI = BopLhs
lemmas step_bop_rhsI = BopRhs

interpretation step_bop_rhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 bop e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp e bop e\<^sub>2 \<leadsto> BinOp e bop e\<^sub>2')\<close>
  by (standard, simp, rule step_bop_rhsI)

locale bop_lemmas =
    fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and bop :: BinOp
  assumes bop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 bop e\<^sub>2\<close>
begin

lemma lhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> bop_fun e\<^sub>1' e\<^sub>2\<close>
  using assms unfolding bop_simps by (rule step_bop_lhsI)

sublocale rhs: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>2 e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> bop_fun e e\<^sub>2 \<leadsto> bop_fun e e\<^sub>2')\<close>
  apply standard
  unfolding bop_simps by (simp, rule step_bop_rhsI)

end

lemmas step_aop_unk_rhsI = AopUnkRhs
lemmas step_aop_unk_lhsI = AopUnkLhs

locale aop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and aop :: AOp
  assumes aop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (AOp aop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>AOp aop\<close>
  by (standard, rule aop_simps)


lemma unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_lhsI)

lemma unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_rhsI)

end

interpretation step_plusI: aop_lemmas \<open>(+)\<close> \<open>Plus\<close> by (standard, unfold plus_exp.simps, rule)
interpretation step_minusI: aop_lemmas \<open>(-)\<close> \<open>Minus\<close> by (standard, unfold minus_exp.simps, rule)
interpretation step_timesI: aop_lemmas \<open>(*)\<close> \<open>Times\<close> by (standard, unfold times_exp.simps, rule)
interpretation step_divideI: aop_lemmas \<open>(div)\<close> \<open>Divide\<close> by (standard, unfold divide_exp.simps, rule)
interpretation step_modI: aop_lemmas \<open>(mod)\<close> \<open>Mod\<close> by (standard, unfold modulo_exp.simps, rule)
interpretation step_sdivideI: aop_lemmas \<open>(sdiv)\<close> \<open>SDivide\<close> by (standard, unfold sdivide_exp.simps, rule)
interpretation step_smodI: aop_lemmas \<open>(smod)\<close> \<open>SMod\<close> by (standard, unfold smod_exp.simps, rule)
interpretation step_landI: aop_lemmas \<open>(&&)\<close> \<open>And\<close> by (standard, unfold land_exp.simps, rule)
interpretation step_lorI: aop_lemmas \<open>(||)\<close> \<open>Or\<close> by (standard, unfold lor_exp.simps, rule)
interpretation step_xorI: aop_lemmas \<open>(xor)\<close> \<open>Xor\<close> by (standard, unfold xor_exp.simps, rule)
interpretation step_lslI: aop_lemmas \<open>(<<)\<close> \<open>LShift\<close> by (standard, unfold lsl_exp.simps, rule)
interpretation step_lsrI: aop_lemmas \<open>(>>)\<close> \<open>RShift\<close> by (standard, unfold lsr_exp.simps, rule)
interpretation step_asrI: aop_lemmas \<open>(>>>)\<close> \<open>ARShift\<close> by (standard, unfold asr_exp.simps, rule)

lemmas step_lop_unk_rhsI = LopUnkRhs
lemmas step_lop_unk_lhsI = LopUnkLhs

locale lop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and lop :: LOp
  assumes lop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (LOp lop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>LOp lop\<close>
  by (standard, rule lop_simps)


lemma unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_lhsI)

lemma unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_rhsI)

end

interpretation step_ltI:  lop_lemmas \<open>(le)\<close>  Le  by (standard, unfold le_exp.simps, rule)
interpretation step_leI:  lop_lemmas \<open>(lt)\<close>  Lt  by (standard, unfold lt_exp.simps, rule)
interpretation step_sltI: lop_lemmas \<open>(sle)\<close> Sle by (standard, unfold sle_exp.simps, rule)
interpretation step_sleI: lop_lemmas \<open>(slt)\<close> Slt by (standard, unfold slt_exp.simps, rule)

lemmas step_plusI = Plus
lemmas step_minusI = Minus
lemmas step_timesI = Times
lemmas step_divI = Div
lemmas step_sdivI = SDiv
lemmas step_modI = Mod
lemmas step_smodI = SMod
lemmas step_lslI = Lsl
lemmas step_lsrI = Lsr
lemmas step_asrI = Asr
lemmas step_landI = LAnd
lemmas step_lorI = LOr
lemmas step_xorI = XOr

lemmas step_eq_sameI = EqSame
lemma step_eqI:
  assumes \<open>(num1 \<Colon> sz1) =\<^sub>b\<^sub>v (num2 \<Colon> sz2) = (true::val)\<close>
    shows \<open>\<Delta> \<turnstile> BinOp (num1 \<Colon> sz1) (LOp Eq) (num2 \<Colon> sz2) \<leadsto> true\<close>
  using assms step_eq_sameI 
  by (metis Val_simp_word bv_negation_true_false bv_neq_true false_word one_neq_zero word_bool_inject(1))

lemmas step_eq_diffI = EqDiff
interpretation step_eq_diffI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta>. w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = true \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 (LOp Eq) e\<^sub>2 \<leadsto> false)\<close>
  apply (standard)
  using step_eq_diffI by force

lemmas step_neq_sameI = NeqSame
lemmas step_neq_diffI = NeqDiff

lemmas step_lessI = Less
lemmas step_less_eqI = LessEq
lemmas step_signed_lessI = SignedLess
lemmas step_signed_less_eqI = SignedLessEq

subsection \<open>Uop\<close>

lemmas step_uopI = Uop
lemmas step_notI = Not
lemmas step_negI = Neg
lemmas step_uop_unkI = UopUnk

lemma step_uop_unk_notI: \<open>\<Delta> \<turnstile> (~ (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding BIL_Syntax.not_exp.simps by (rule step_uop_unkI)

lemma step_uop_unk_negI: \<open>\<Delta> \<turnstile> (- (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding uminus_exp.simps by (rule step_uop_unkI)

lemma step_not_falseI: \<open>\<Delta> \<turnstile> (~false) \<leadsto> true\<close>
  using bv_negation_false_true step_notI by (metis false_word)

lemma step_not_trueI: \<open>\<Delta> \<turnstile> (~true) \<leadsto> false\<close>
  using bv_negation_true_false step_notI by (metis true_word)

subsection \<open>Concat\<close>

lemmas step_concat_rhsI = ConcatRhs

lemmas step_concatI = Concat
interpretation step_concatI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<leadsto> (e\<^sub>1 \<cdot> e\<^sub>2))\<close>
  apply standard
  using step_concatI by force

lemmas step_concat_lhsI = ConcatLhs
interpretation step_concat_lhsI: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e\<^sub>1 e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ e) \<leadsto> (e\<^sub>1' @ e))\<close>
  apply standard
  using step_concat_lhsI by force

lemmas step_concat_lhs_unI = ConcatLhsUn
interpretation step_concat_lhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>1 str. \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ e) \<leadsto> unknown[str]: imm\<langle>sz\<^sub>1 + sz\<rangle>)\<close>
  apply standard
  using step_concat_lhs_unI by force

lemmas step_concat_rhs_unI = ConcatRhsUn
interpretation step_concat_rhs_unI: exp_val_is_imm_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>2 str. \<Delta> \<turnstile> (e @ unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> unknown[str]: imm\<langle>sz + sz\<^sub>2\<rangle>)\<close>
  apply standard
  using step_concat_rhs_unI by force

subsection \<open>Extract\<close>

lemmas step_extract_reduceI = ExtractReduce
lemmas step_extract_unI = ExtractUn
lemmas step_extractI = Extract

subsection \<open>Cast\<close>

lemmas step_cast_reduceI = CastReduce
lemmas step_cast_unkI = CastUnk
lemmas step_cast_lowI = CastLow
interpretation step_cast_lowI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> low:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_lowI by force

lemmas step_cast_highI = CastHigh
interpretation step_cast_highI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ sz'. (\<And>\<Delta> sz. \<Delta> \<turnstile> high:sz[e] \<leadsto> ext e \<sim> hi : sz' - 1 \<sim> lo : sz' - sz)\<close>
  apply standard
  using step_cast_highI by force

lemmas step_cast_signedI = CastSigned 
interpretation step_cast_signedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> extend:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_signedI by force

lemmas step_cast_unsignedI = CastUnsigned
interpretation step_cast_unsignedI: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. (\<And>\<Delta> sz. \<Delta> \<turnstile> pad:sz[e] \<leadsto> ext e \<sim> hi : sz - 1 \<sim> lo : 0)\<close>
  apply standard
  using step_cast_unsignedI by force

(* TODO move *)

lemmas solve_exp_simpset = (*mod_mod_trivial*) mod_Suc_eq not_dvd_plus_mod_neq not_dvd_Suc_Suc_mod_neq 
  not_dvd_Suc_mod_neq plus_mod_neq mod_Suc_neq
  plus_Suc_right_mod_neq plus_Suc_left_mod_neq 
  plus_Suc_Suc_right_mod_neq plus_Suc_Suc_left_mod_neq

lemma power_le_min: fixes x n N :: nat assumes \<open>n \<le> N\<close> and \<open>x < 2 ^ n\<close> shows \<open>x < 2 ^ N\<close>
  using assms order_less_le_trans by fastforce

lemma power_lt_min: fixes x n N :: nat assumes \<open>n < N\<close> and \<open>x < 2 ^ (Suc n)\<close> shows \<open>x < 2 ^ N\<close>
  using Suc_leI assms power_le_min by blast


interpretation succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 0 \<Longrightarrow> succ w \<noteq> w)\<close>
  apply standard
  apply auto
  by (simp add: solve_exp_simpset succ.simps bv_plus.simps)


interpretation succ2_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ w) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  
  apply (rule not_dvd_Suc_Suc_mod_neq)
  apply simp_all 
  by (metis less_exp not_less_eq numeral_2_eq_2)

interpretation succ2_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 0 \<Longrightarrow> succ (succ w) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ_neqI.succ)

interpretation succ3_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ w)) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 apply (rule mod_between_neq')
  apply auto
  by (metis Suc_lessI Suc_mask_eq_exp less_mask not_less_eq numeral_3_eq_3 order_less_trans)

interpretation succ3_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ w)) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ2_neqI.succ, simp)

interpretation succ4_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ w))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ4_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ (succ w))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ3_neqI.succ, simp)

interpretation succ5_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ w)))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ5_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ w)))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ4_neqI.succ, simp)

interpretation succ6_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ w))))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ6_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ w))))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ5_neqI.succ, simp)

interpretation succ7_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ (succ w)))))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ7_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ (succ w)))))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ6_neqI.succ, simp)

lemma succ_lt_neqI:
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>num\<^sub>2 < 2 ^ sz\<^sub>2\<close> and \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq> num\<^sub>2 \<Colon> sz\<^sub>2\<close>
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding succ.simps bv_plus.simps apply auto
  using assms mod_lt_neqI Suc_mod_neq by force

interpretation succ_lt_neqI: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>_ _ w\<^sub>1 _ _ _ w\<^sub>2 _. (w\<^sub>1 \<noteq> w\<^sub>2 \<Longrightarrow> succ w\<^sub>1 \<noteq> succ w\<^sub>2)\<close>
  by (standard, rule succ_lt_neqI)

lemma succ_left_neqI:
    fixes w :: word
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
    shows \<open>succ (succ w) \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using Suc_mod_neq by auto
qed

interpretation succ_left_neqI: exp_val_word_fixed_sz_is_ok_syntax
\<open>\<lambda>_ _ w\<^sub>1 _. (\<And>w::word. succ w \<noteq> w\<^sub>1 \<Longrightarrow> succ (succ w) \<noteq> succ w\<^sub>1)\<close>
  by (standard, rule succ_left_neqI)

lemma succ_right_neqI: 
    fixes w :: word
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ w\<close> 
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (succ w)\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using Suc_mod_neq by auto
qed

interpretation succ_right_neqI: exp_val_word_fixed_sz_is_ok_syntax
  \<open>\<lambda>_ _ w\<^sub>1 _. (\<And>w::word. w\<^sub>1 \<noteq> succ w \<Longrightarrow> succ w\<^sub>1 \<noteq> succ (succ w))\<close>
  by (standard, rule succ_right_neqI)

lemma succ_succ_neqI: 
    fixes w :: word
  assumes \<open>succ w \<noteq> succ w'\<close>
    shows \<open>succ (succ w) \<noteq> succ (succ w')\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    proof (cases w' rule: word_exhaust)
      case w': (1 num\<^sub>2 sz\<^sub>2)
      show ?thesis 
        using w w' assms apply safe
        unfolding succ.simps bv_plus.simps apply auto
        using Suc_mod_neq by auto
    qed
  qed

method solve_lt_power uses add = (rule add | ((unfold power_numeral Num.pow.simps Num.sqr.simps)[1], linarith))

method solve_word_neq uses add = (
  (rule succ_neqI.word  succ_neqI.word [symmetric] succ_neqI.plus  succ_neqI.plus [symmetric]
        succ2_neqI.word succ2_neqI.word[symmetric] succ2_neqI.plus succ2_neqI.plus[symmetric]
        succ3_neqI.word succ3_neqI.word[symmetric] succ3_neqI.plus succ3_neqI.plus[symmetric]
        succ4_neqI.word succ4_neqI.word[symmetric] succ4_neqI.plus succ4_neqI.plus[symmetric]
        succ5_neqI.word succ5_neqI.word[symmetric] succ5_neqI.plus succ5_neqI.plus[symmetric]
        succ6_neqI.word succ6_neqI.word[symmetric] succ6_neqI.plus succ6_neqI.plus[symmetric]
        succ7_neqI.word succ7_neqI.word[symmetric] succ7_neqI.plus succ7_neqI.plus[symmetric]
        succ2_succ_neqI.word succ2_succ_neqI.word[symmetric] succ2_succ_neqI.plus succ2_succ_neqI.plus[symmetric]
        succ3_succ_neqI.word succ3_succ_neqI.word[symmetric] succ3_succ_neqI.plus succ3_succ_neqI.plus[symmetric]
        succ4_succ_neqI.word succ4_succ_neqI.word[symmetric] succ4_succ_neqI.plus succ4_succ_neqI.plus[symmetric]
        succ5_succ_neqI.word succ5_succ_neqI.word[symmetric] succ5_succ_neqI.plus succ5_succ_neqI.plus[symmetric]
        succ6_succ_neqI.word succ6_succ_neqI.word[symmetric] succ6_succ_neqI.plus succ6_succ_neqI.plus[symmetric]
        succ7_succ_neqI.word succ7_succ_neqI.word[symmetric] succ7_succ_neqI.plus succ7_succ_neqI.plus[symmetric],
   linarith) |

  ( rule succ_succ_neqI, solve_word_neq add: add) |
  ( rule succ_left_neqI, solve_lt_power add: add, solve_word_neq add: add) |
  ( rule succ_left_neqI.plus, solve_word_neq add: add) |
  (rule succ_right_neqI, solve_lt_power add: add, solve_word_neq add: add) |
  (rule succ_right_neqI.plus, solve_word_neq add: add) |
  (rule succ_lt_neqI.plus.plus, solve_word_neq add: add) |
  (rule succ_lt_neqI.plus.word_is_ok, solve_lt_power add: add, solve_word_neq add: add) |
  (rule succ_lt_neqI, solve_lt_power add: add, solve_lt_power add: add, solve_word_neq add: add) |
  (solves \<open>rule add\<close> | (match conclusion in P for P  \<Rightarrow> \<open>print_term P\<close>, 
    solves \<open>simp (no_asm) add: add solve_exp_simpset succ.simps bv_plus.simps\<close>))
)

method solve_bv_neqI = (rule bv_not_eq_same_sz_true, (simp; fail))


lemma load_byte_minus_simps:
  \<open>16 - (8::nat) = 8\<close>  \<open>24 - (8::nat) = 16\<close> \<open>32 - (8::nat) = 24\<close> \<open>40 - (8::nat) = 32\<close> 
  \<open>48 - (8::nat) = 40\<close> \<open>56 - (8::nat) = 48\<close> \<open>64 - (8::nat) = 56\<close>
  by auto

method solve_expI_scaffold methods recurs solve_type uses add = (
    \<comment> \<open>Vars\<close>
  (rule step_var_inI.xtract2 step_var_inI.xtract step_var_inI.word step_var_inI, solve_in_var add: add) |
  (rule step_var_unI, blast) |

  \<comment> \<open>Loads\<close>
  (rule step_load_un_addrI step_load_byteI.word.word step_load_byteI.word.true 
        step_load_byteI.word.false step_load_byteI.word.unknown 
        step_load_byteI.word.xtract step_load_byteI.word.succ step_load_byteI.word.val 
        step_load_byteI.succ.word step_load_byteI.succ.true step_load_byteI.succ.false  
        step_load_byteI.succ.unknown step_load_byteI.succ.xtract 
        step_load_byteI.succ.succ step_load_byteI.succ.val) |
  (rule step_load_byteI.is_word.word step_load_byteI.is_word.true step_load_byteI.is_word.false 
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
  (rule step_let_stepI, recurs) |

  \<comment> \<open>Ite\<close>
  (rule step_ite_elseI, recurs) |

  \<comment> \<open>Bop\<close>
  (rule step_bop_lhsI, recurs) |

  \<comment> \<open>Eq\<close>
  (rule step_eqI, assumption) |
  (rule step_eq_diffI, (assumption | (rule bv_neq_true, assumption))) |
  (rule step_eq_diffI.true.word, assumption) |

  \<comment> \<open>Plus\<close>
  (rule step_plusI) |
  (rule step_plusI.lhsI, recurs) |
 
  \<comment> \<open>Uop\<close>
  rule step_not_trueI step_not_falseI step_uop_unk_notI step_uop_unk_negI step_uop_unkI step_notI
       step_negI |
  (rule step_uopI, recurs) |

  \<comment> \<open>Concat\<close>
  (rule step_concatI step_concatI.xtract.xtract) |
  (rule step_concat_lhs_unI step_concat_rhs_unI, solve_type) |
  (rule step_concat_lhsI.word step_concat_lhsI.xtract step_concat_rhsI, recurs) | 

  \<comment> \<open>Extract\<close>
  (rule step_extractI step_extract_unI) | 
  (rule step_extract_reduceI, recurs) |

  \<comment> \<open>Cast\<close>
  (rule step_cast_lowI      step_cast_lowI.xtract      step_cast_lowI.plus
        step_cast_highI     step_cast_highI.xtract     step_cast_highI.plus
        step_cast_signedI   step_cast_signedI.xtract   step_cast_signedI.plus
        step_cast_unsignedI step_cast_unsignedI.xtract step_cast_unsignedI.plus
        step_cast_unkI) |
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
lemmas LSR = step_lsrI
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
