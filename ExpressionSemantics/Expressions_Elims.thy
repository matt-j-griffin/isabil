
section \<open>Elimination rules for big step expressions\<close>

theory Expressions_Elims
  imports Expressions_Rules Expression_Elims
          
begin

text \<open>Better reduce rule that includes the assumption e3 \<noteq> e1\<close>

lemmas step_exps_reduce_baseE = 
    converse_rtranclpE[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]

lemma step_exps_reduceE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close>
  obtains 
    (Reduce) e\<^sub>2 where 
        \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close> \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<close>
  | (Refl) 
        \<open>e\<^sub>3 = e\<^sub>1\<close>
proof (cases \<open>e\<^sub>3 = e\<^sub>1\<close>)
  case True
  thus ?thesis by (rule Refl)
next
  case False 
  show ?thesis 
  using assms(1) proof (rule step_exps_reduce_baseE)
    assume "e\<^sub>1 = e\<^sub>3" thus thesis
      using False by (elim notE, blast)
  next
    fix e\<^sub>2 :: exp
    assume "\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2" "\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3"
    thus thesis
      using False by (intro Reduce[of e\<^sub>2] conjI)
  qed
qed

lemma step_exps_reduce_strictE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> and \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close>
  obtains (Reduce) e\<^sub>2 where \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close> \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<close>
  using assms(1) apply (rule step_exps_reduceE)
  subgoal for e\<^sub>2
    using assms(2) by (intro Reduce[of e\<^sub>2] conjI)
  using assms(2) by (elim notE)

lemmas step_exps_reduce_strict_valE = step_exps_reduce_strictE[where e\<^sub>3 = \<open>Val _\<close>]
lemmas step_exps_load_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>_[_, _]:u_\<close>, simplified]
lemmas step_exps_store_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>_ with [_, _]:u_ \<leftarrow> _\<close>, simplified]
lemmas step_exps_binary_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>BinOp _ _ _\<close>, simplified]
lemmas step_exps_unary_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>UnOp _ _\<close>, simplified]
lemmas step_exps_cast_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>_:_[_]\<close>, simplified]
lemmas step_exps_let_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>Let _ _ _\<close>, simplified]
lemmas step_exps_ite_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>ite _ _ _\<close>, simplified]
lemmas step_exps_extract_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>extract:_:_[_]\<close>, simplified]
lemmas step_exps_concat_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>_ \<copyright> _\<close>, simplified]
lemmas step_exps_var_reduce_valE = step_exps_reduce_strict_valE[where e\<^sub>1 = \<open>_ :\<^sub>t _\<close>, simplified]

interpretation step_exps_load_reduce_valE: exp_val_syntax \<open>\<lambda>e v.
    (\<And>\<Delta> e\<^sub>1 e\<^sub>2 P. \<lbrakk>\<Delta> \<turnstile> e1[e2, en]:usz \<leadsto>* e; (\<And>e'. \<lbrakk>\<Delta> \<turnstile> e1[e2, en]:usz \<leadsto> e'; \<Delta> \<turnstile> e' \<leadsto>* e\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_load_reduce_valE in blast)


context bop_lemmas
begin

lemma step_exps_reduce_valE:
  assumes major: \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto>* Val v\<close>
  obtains (minor) e' where \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> e'\<close> \<open>\<Delta> \<turnstile> e' \<leadsto>* Val v\<close>
  using assms unfolding bop_simps by (rule step_exps_binary_reduce_valE)

interpretation step_exps_reduce_valE: exp_val_syntax \<open>\<lambda>e v.
    (\<And>\<Delta> e\<^sub>1 e\<^sub>2 P. \<lbrakk>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto>* e; (\<And>e'. \<lbrakk>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> e'; \<Delta> \<turnstile> e' \<leadsto>* e\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_reduce_valE in blast)

lemmas step_exps_reduce_wordE = step_exps_reduce_valE.word

end

context uop_lemmas
begin

(*(\<And>e\<^sub>2. ?\<Delta> \<turnstile> BinOp ?uua ?uuaa ?uub \<leadsto> e\<^sub>2 \<Longrightarrow> ?\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* Val ?uu \<Longrightarrow> ?P) \<Longrightarrow> ?P*)
lemma step_exps_reduce_valE:
  assumes major: \<open>\<Delta> \<turnstile> uop_fun e \<leadsto>* Val v\<close>
  obtains (minor) e' where \<open>\<Delta> \<turnstile> uop_fun e \<leadsto> e'\<close> \<open>\<Delta> \<turnstile> e' \<leadsto>* Val v\<close>
  using assms unfolding uop_simps by (rule step_exps_unary_reduce_valE)

interpretation step_exps_reduce_valE: exp_val_syntax \<open>\<lambda>e v.
    (\<And>\<Delta> e\<^sub>1 e\<^sub>2 P. \<lbrakk>\<Delta> \<turnstile> uop_fun e\<^sub>1 \<leadsto>* e; (\<And>e'. \<lbrakk>\<Delta> \<turnstile> uop_fun e\<^sub>1 \<leadsto> e'; \<Delta> \<turnstile> e' \<leadsto>* e\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_reduce_valE in blast)

lemmas step_exps_reduce_wordE = step_exps_reduce_valE.word

end

subsection \<open>Values\<close>

lemma step_exps_valE:
  assumes \<open>\<Delta> \<turnstile> (Val v) \<leadsto>* e\<close>
      and \<open>e = (Val v) \<Longrightarrow> P\<close>
    shows P
  apply (rule step_exps_reduceE[OF assms(1) _ assms(2)])
  using step_exp_not_val by blast

interpretation step_exps_valE: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e' P. \<Delta> \<turnstile> e \<leadsto>* e' \<Longrightarrow> (e' = e \<Longrightarrow> P) \<Longrightarrow> P)\<close>
  by (standard, use step_exps_valE in blast)

(* These goals are spawned from moves *)
lemmas step_exps_val_valE = step_exps_valE[where e = \<open>Val _\<close>, simplified]

interpretation step_exps_val_valE: exp_val_syntax \<open>\<lambda>e v.
    (\<And>\<Delta> v' P. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (Val v'); v' = v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_val_valE in blast)

(* These goals are spawned from jumps *)
lemma step_exps_val_wordE: 
  assumes major: \<open>\<Delta> \<turnstile> (num \<Colon> sz) \<leadsto>* (num' \<Colon> sz')\<close>
      and minor: \<open>\<lbrakk>num' \<Colon> sz' = ((num \<Colon> sz)::exp); num' \<Colon> sz' = ((num \<Colon> sz)::val);
                   num' \<Colon> sz' = ((num \<Colon> sz)::word)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major unfolding word_constructor_exp_def[where num = num and sz = sz]
  apply (elim step_exps_valE[where e = \<open>_ \<Colon> _\<close>])
  apply (rule minor)
  unfolding word_constructor_exp_def[symmetric] by auto

interpretation step_exps_val_wordE: exp_val_word_sz_syntax \<open>\<lambda>e v w _.
    (\<And>\<Delta> num sz P. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz); \<lbrakk>(num \<Colon> sz) = e; num \<Colon> sz = v; num \<Colon> sz = w\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_val_wordE in blast)

subsection \<open>Optimisations\<close>

text \<open>Note necessarily needed but makes proofs easier\<close> 

(* TODO surely there's a way of simplifying these lemmas *)

lemma step_exps_var_inE:
  assumes major: \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto>* Val v\<close> and var_in: \<open>(id' :\<^sub>t t, v') \<in>\<^sub>\<Delta> \<Delta>\<close> 
      and minor: \<open>v = v' \<Longrightarrow> P\<close> 
    shows P
using major proof (rule step_exps_var_reduce_valE)
  fix e\<^sub>2 assume step: "\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> e\<^sub>2"
    and steps: "\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* Val v"
  have e\<^sub>2: \<open>e\<^sub>2 = Val v'\<close>
    using step var_in by (rule step_exp_var_inE)
  show ?thesis
    using steps unfolding e\<^sub>2 apply (rule step_exps_val_valE)
    by (rule minor)
qed

interpretation step_exps_var_inE: exp_val_syntax \<open>\<lambda>e v. 
    (\<And>\<Delta> v' id t P. \<lbrakk>\<Delta> \<turnstile> (id :\<^sub>t t) \<leadsto>* e; (id :\<^sub>t t, v') \<in>\<^sub>\<Delta> \<Delta>; v = v' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_var_inE in blast)

interpretation step_exps_var_in_wordE: exp_val_word_sz_syntax \<open>\<lambda>e v w sz'. 
    (\<And>\<Delta> v' id t P num sz. \<lbrakk>\<Delta> \<turnstile> (id :\<^sub>t t) \<leadsto>* (num \<Colon> sz); (id :\<^sub>t t, v) \<in>\<^sub>\<Delta> \<Delta>; \<lbrakk>(num \<Colon> sz) = e; (num \<Colon> sz) = v; (num \<Colon> sz) = w; sz = sz'\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  apply unfold_locales
  using step_exps_var_inE word_constructor_exp_def by (metis word_inject)

lemma step_exps_concatE:
  assumes major: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto>* (Val v)\<close> 
      and minor: \<open>v = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) \<Longrightarrow> P\<close> 
    shows P
proof (insert major, elim step_exps_concat_reduce_valE step_exp_concatE, clarify)
  fix e\<^sub>2 assume "\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto>* Val v"
  thus P
    apply -
    apply (erule step_exps_val_valE.is_val[rotated])
    apply (rule minor, assumption)
    by (metis bv_simps(39) word_constructor_exp_def)
qed

interpretation step_exps_concatE: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 _ _ e\<^sub>2 v\<^sub>2 _ _. 
    (\<And>\<Delta> v P. \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto>* (Val v)
    \<Longrightarrow> (v = v\<^sub>1 \<cdot> v\<^sub>2 \<Longrightarrow> P) 
    \<Longrightarrow> P)\<close>
  by (standard, use step_exps_concatE in blast)

lemma step_exps_concat_rhs_stepE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto>* Val v\<close> and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
      and minor:\<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2') \<leadsto>* Val v\<rbrakk> \<Longrightarrow> P\<close>
    shows P
using major proof (elim step_exps_concat_reduce_valE step_exp_concat_rhs_stepE [OF _ caveat])
  fix e\<^sub>2' e\<^sub>2'' :: exp
  assume "\<Delta> \<turnstile> e\<^sub>2' \<leadsto>* Val v" "e\<^sub>2' = e\<^sub>1 \<copyright> e\<^sub>2''" "\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2''"
  thus P
    apply clarify
    by (rule minor)
qed

lemma step_exps_concat_lhs_stepE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> Val v\<^sub>2) \<leadsto>* Val v\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; \<Delta> \<turnstile> (e\<^sub>1' \<copyright> Val v\<^sub>2) \<leadsto>* Val v\<rbrakk> \<Longrightarrow> P\<close>
    shows P
using major sketch (elim step_exps_concat_reduce_valE step_exp_concat_lhs_stepE [OF _ caveat])
proof (elim step_exps_concat_reduce_valE step_exp_concat_lhs_stepE [OF _ caveat])
  fix e\<^sub>2 e\<^sub>1' :: exp
  assume "\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* Val v" "\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'" "e\<^sub>2 = e\<^sub>1' \<copyright> Val v\<^sub>2"
  thus P
    apply clarify
    by (rule minor)
qed

interpretation step_exps_concat_lhs_stepE: exp_val_syntax \<open>\<lambda>e\<^sub>2 _. (\<And>\<Delta> e\<^sub>1 v P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto>* Val v; \<forall>v'. e\<^sub>1 \<noteq> Val v';
      (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; \<Delta> \<turnstile> (e\<^sub>1' \<copyright> e\<^sub>2) \<leadsto>* Val v\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_concat_lhs_stepE in blast)

subsection \<open>Symbolic execution\<close>

(* simplifier which uses only the basic simpset - effectively rewrites only *)

method solve_expsE_scaffold methods recurs solve_exp solve_is_val uses add = (

  (erule step_exps_var_in_wordE.is_sz_word[rotated] step_exps_var_inE.is_val[rotated], solve_var_inI add: add,
         defer_tac, solve_is_wordI, prefer_last, rewrite) |
  (erule step_exps_var_inE, solve_var_inI add: add) |

  (erule step_exps_concatE) |
  (erule step_exps_concatE.is_word2[rotated 2], prefer_last, solve_is_wordI, prefer_last, solve_is_wordI) |

  (erule step_exps_concat_rhs_stepE, solves force, solve_exp, recurs?) |

  (erule step_exps_concat_lhs_stepE.is_val[rotated], solves force, prefer_last, solve_is_val, 
    solve_exp, recurs?) |

  \<comment> \<open>Solve other values\<close>
  (erule step_exps_val_valE.is_val[rotated], defer_tac, solve_is_val, prefer_last, rewrite) |

  \<comment> \<open>Reduction rules come last\<close>
  (erule 
    plus.step_exps_reduce_wordE plus.step_exps_reduce_valE
    minus.step_exps_reduce_wordE minus.step_exps_reduce_valE
    le.step_exps_reduce_wordE le.step_exps_reduce_valE
    lt.step_exps_reduce_wordE lt.step_exps_reduce_valE
    not.step_exps_reduce_valE not.step_exps_reduce_wordE 
    neg.step_exps_reduce_valE neg.step_exps_reduce_wordE
    lsl.step_exps_reduce_valE lsl.step_exps_reduce_wordE
    lsr.step_exps_reduce_valE lsr.step_exps_reduce_wordE
    asr.step_exps_reduce_valE asr.step_exps_reduce_wordE
    land.step_exps_reduce_valE land.step_exps_reduce_wordE
    lor.step_exps_reduce_valE lor.step_exps_reduce_wordE
    xor.step_exps_reduce_valE xor.step_exps_reduce_wordE
    step_exps_concat_reduce_valE step_exps_load_reduce_valE step_exps_store_reduce_valE
    step_exps_cast_reduce_valE plus.step_exps_reduce_valE step_exps_binary_reduce_valE 
    step_exps_unary_reduce_valE step_exps_let_reduce_valE step_exps_ite_reduce_valE 
    step_exps_extract_reduce_valE step_exps_var_reduce_valE,
    solve_exp, recurs?)
  |
  (erule step_exps_val_wordE.is_word[rotated], defer_tac, solve_is_wordI, prefer_last, rewrite?)
)

method solve_expsE uses add = (
  solves \<open>rule add\<close> | erule add |
  solve_expsE_scaffold \<open>solve_expsE add: add\<close> \<open>solve_expE add: add\<close> \<open>solve_is_valI add: add\<close> add: add
)

primrec
  has_unknownable_var :: \<open>var \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>has_unknownable_var _ (Val _) = False\<close> |
  \<open>has_unknownable_var var (EVar var') = (var = var')\<close> |
  \<open>has_unknownable_var var (Load e1 e2 _ _) = (has_unknownable_var var e1 \<or> has_unknownable_var var e2)\<close> |
  \<open>has_unknownable_var var (Store e1 e2 _ _ e3) = (has_unknownable_var var e2)\<close> |
  \<open>has_unknownable_var var (BinOp e1 _ e2) = (has_unknownable_var var e1 \<or> has_unknownable_var var e2)\<close> |
  \<open>has_unknownable_var var (UnOp _ e) = has_unknownable_var var e\<close> |
  \<open>has_unknownable_var var (Cast _ _ e) = has_unknownable_var var e\<close> |
  \<open>has_unknownable_var var (Let var' e1 e2) = (has_unknownable_var var e1 \<or> has_unknownable_var var e2)\<close> |
  \<open>has_unknownable_var var (Ite e1 e2 e3) = (has_unknownable_var var e1 \<or> (e1 = true \<and> has_unknownable_var var e2) \<or> (e1 = false \<and> has_unknownable_var var e3))\<close> |
  \<open>has_unknownable_var var (Extract _ _ e) = has_unknownable_var var e\<close> |
  \<open>has_unknownable_var var (e1 \<copyright> e2) = (has_unknownable_var var e1 \<or> has_unknownable_var var e2)\<close>





lemma word_isnt_var[simp]: \<open>isnt_var var (num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def by simp

lemma unknown_isnt_var[simp]: \<open>isnt_var var unknown[str]: t\<close>
  unfolding unknown_constructor_exp_def by simp

lemma storage_isnt_var[simp]: \<open>isnt_var var (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  unfolding storage_constructor_exp_def by simp

lemma var_isnt_var_simps[simp]: \<open>isnt_var var (name :\<^sub>t t) \<longleftrightarrow> var \<noteq> (name :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by simp

lemma var_is_var[simp]: \<open>\<not>isnt_var (name :\<^sub>t t) (name :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by (rule is_var)


\<comment> \<open>The var does not appear in the given expression\<close>

lemma capture_isnt_var[intro]:
  assumes \<open>isnt_var var e\<close>
    shows \<open>isnt_var var ([v\<sslash>var']e)\<close>
  using assms by (induct e, auto) 

lemma isnt_var_captureD: "isnt_var var e \<Longrightarrow> ([v\<sslash>var]e) = e"
  by (induct e, auto)

(*
lemma isnt_var_capture[simp]: \<open>isnt_var var ([v\<sslash>var]e)\<close>
  apply (induct e, auto)
*)
lemma isnt_var_capture_neq: 
  assumes \<open>var \<noteq> var'\<close>
    shows \<open>isnt_var var ([v\<sslash>var']e) \<longleftrightarrow> isnt_var var e\<close>
  using assms by (induct e, auto)



primrec
  has_unknowns :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>has_unknowns (Val v) = (\<exists>str t. v = unknown[str]: t)\<close> |
  \<open>has_unknowns (EVar var) = False\<close> |
  \<open>has_unknowns (Load e1 e2 _ _) = (has_unknowns e1 \<or> has_unknowns e2)\<close> |
  \<open>has_unknowns (Store e1 e2 _ _ e3) = (has_unknowns e2)\<close> |
  \<open>has_unknowns (BinOp e1 _ e2) = (has_unknowns e1 \<or> has_unknowns e2)\<close> |
  \<open>has_unknowns (UnOp _ e) = has_unknowns e\<close> |
  \<open>has_unknowns (Cast _ _ e) = has_unknowns e\<close> |
  \<open>has_unknowns (Let var e1 e2) = ((has_unknowns e1) \<and> has_unknowns e2)\<close> |
  \<open>has_unknowns (Ite e1 e2 e3) = (has_unknowns e1 \<or> (e1 = true \<and> has_unknowns e2) \<or> 
          (e1 = false \<and> has_unknowns e3))\<close> |
  \<open>has_unknowns (Extract _ _ e) = has_unknowns e\<close> |
  \<open>has_unknowns (e1 \<copyright> e2) = (has_unknowns e1 \<or> has_unknowns e2)\<close>

lemma not_unknown_word[simp]: \<open>\<not>has_unknowns (num \<Colon> sz)\<close>
  by (simp add: word_constructor_exp_def)

lemma not_unknown_storage[simp]: \<open>\<not>has_unknowns (v[w \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def)

lemma not_unknown[simp]: \<open>has_unknowns (unknown[str]: t)\<close>
  by (simp add: unknown_constructor_exp_def)

lemma not_unknown_var[simp]: \<open>\<not>has_unknowns (name' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by simp

context bop_lemmas
begin

lemma not_unknown[simp]: \<open>has_unknowns (bop_fun e\<^sub>1 e\<^sub>2) \<longleftrightarrow> has_unknowns e\<^sub>1 \<or> has_unknowns e\<^sub>2\<close>
  unfolding bop_simps by simp

end

context uop_lemmas
begin

lemma not_unknown[simp]: \<open>has_unknowns (uop_fun e) \<longleftrightarrow> has_unknowns e\<close>
  unfolding uop_simps by simp

end

declare capture_avoid.word[simp add] (* todo move *)

lemma TL:  "var \<noteq> x1a \<Longrightarrow> has_unknownable_var x1a e \<Longrightarrow> has_unknownable_var x1a ([val\<sslash>var]e)"
proof (induct e)
qed auto


lemma TK: \<open>has_unknowns e \<Longrightarrow> has_unknowns ([val\<sslash>var]e)\<close>
  apply (induct e)
  apply auto[7]
  subgoal 
    unfolding has_unknowns.simps capture_avoiding_sub.simps
    by simp
 by auto

lemma step_exp_always_has_unknownsI:
  assumes \<open>\<delta>' \<turnstile> e \<leadsto> e'\<close>
      and \<open>has_unknowns e\<close>
    shows \<open>has_unknowns e'\<close>
using assms proof (induct rule: step_exp.induct)
  case (Let \<Delta> var v e)
  thus ?case 
    apply auto 
    by (rule TK)
qed auto

lemma step_exps_always_has_unknownsI:
  assumes \<open>\<delta>' \<turnstile> e \<leadsto>* e'\<close>
      and \<open>has_unknowns e\<close>
    shows \<open>has_unknowns e'\<close>
using assms proof (induct rule: step_exps_induct)
  case (step y z)
  thus ?case 
    using step_exp_always_has_unknownsI by auto
qed auto


lemma step_exps_not_unknownD:
  assumes \<open>\<delta>' \<turnstile> e \<leadsto>* (Val v)\<close>
      and unk: \<open>\<forall>str t. v \<noteq> unknown[str]: t\<close>
    shows \<open>\<not>has_unknowns e\<close>
proof (rule notI)
  assume hunk: "has_unknowns e"
  show False
    using step_exps_always_has_unknownsI[OF assms(1) hunk] unk by auto
qed


primrec
  no_problem_children :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>no_problem_children (Val v) = True\<close> |
  \<open>no_problem_children (EVar var) = True\<close> |
  \<open>no_problem_children (Load e1 e2 _ _) = (no_problem_children e1 \<and> no_problem_children e2)\<close> |
  \<open>no_problem_children (Store e1 e2 _ _ e3) = False\<close> |
  \<open>no_problem_children (BinOp e1 _ e2) = (no_problem_children e1 \<and> no_problem_children e2)\<close> |
  \<open>no_problem_children (UnOp _ e) = no_problem_children e\<close> |
  \<open>no_problem_children (Cast _ _ e) = no_problem_children e\<close> |
  \<open>no_problem_children (Let var e1 e2) = ((\<exists>v. e1 = Val v) \<and> no_problem_children e2)\<close> |
  \<open>no_problem_children (Ite e1 e2 e3) = (no_problem_children e1  \<and> (\<exists>v. e2 = Val v) \<and> (\<exists>v. e3 = Val v))\<close> |
  \<open>no_problem_children (Extract _ _ e) = no_problem_children e\<close> |
  \<open>no_problem_children (e1 \<copyright> e2) = (no_problem_children e1 \<and> no_problem_children e2)\<close>

lemma no_problem_children_word[simp]: \<open>no_problem_children (num \<Colon> sz)\<close>
  by (simp add: word_constructor_exp_def)

lemma no_problem_children_storage[simp]: \<open>no_problem_children (v[w \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def)

lemma no_problem_children_unknown[simp]: \<open>no_problem_children (unknown[str]: t)\<close>
  by (simp add: unknown_constructor_exp_def)

lemma no_problem_children_unknown_var[simp]: \<open>no_problem_children (name' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by simp


\<comment> \<open>The var does not appear in the given expression\<close>

context uop_is_word
begin

lemma bv_no_problem_children[simp]: \<open>no_problem_children (bv_fun1 (num\<^sub>1 \<Colon> sz))\<close>
  using bv_fun_is_word[where num\<^sub>1 = num\<^sub>1] apply (elim exE conjE)
  using word_isnt_var by auto

end

context bop_is_word
begin

lemma bv_no_problem_children[simp]: \<open>no_problem_children (bv_fun1 (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2))\<close>
  using bv_fun_is_word[where num\<^sub>1 = num\<^sub>1 and num\<^sub>2 = num\<^sub>2] apply (elim exE conjE)
  using word_isnt_var by auto

end

context bop_lemmas
begin

lemma no_problem_children[simp]: \<open>no_problem_children (bop_fun e\<^sub>1 e\<^sub>2) \<longleftrightarrow> no_problem_children e\<^sub>1 \<and> no_problem_children e\<^sub>2\<close>
  unfolding bop_simps by simp

end

context uop_lemmas
begin

lemma no_problem_children[simp]: \<open>no_problem_children (uop_fun e) \<longleftrightarrow> no_problem_children e\<close>
  unfolding uop_simps by simp

end

lemma no_problem_children_capture_avoid[intro]: "no_problem_children e \<Longrightarrow> no_problem_children ([v\<sslash>var]e)"
  apply (induct e)
  by auto

lemma never_problem_children:
  assumes \<open>\<delta>' \<turnstile> e \<leadsto> e'\<close>
      and \<open>no_problem_children e\<close>
    shows \<open>no_problem_children e'\<close>
using assms proof (induct rule: step_exp.induct)
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  thus ?case 
    unfolding bv_lor.simps bv_lt.simps bv_eq_def by auto
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  thus ?case 
    unfolding bv_lor.simps bv_slt.simps bv_eq_def by auto
qed (auto simp add: xtract.simps bv_concat.simps bv_uminus.simps bv_negation.simps bv_lt.simps 
                    bv_slt.simps bv_plus.simps succ.simps bv_xor.simps bv_lor.simps bv_land.simps
                    bv_asr.simps bv_lsl.simps bv_lsr.simps bv_smod.simps bv_mod\<^sub>b\<^sub>v.simps 
                    bv_divide.simps bv_sdivide.simps bv_minus.simps bv_times.simps)

lemma step_exp_detD:
  assumes steps: \<open>\<delta>' \<turnstile> e \<leadsto> e1\<close> \<open>\<delta>' \<turnstile> e \<leadsto> e2\<close>
      and unk: \<open>\<not> has_unknowns e\<close> \<open>\<not>has_unknowns e1\<close>      "no_problem_children e"
    shows \<open>e1 = e2\<close>
using steps unk proof (induct arbitrary: e2 rule: step_exp.induct)
  case (VarNotIn name' t \<Delta> str)
  thus ?case 
    apply (elim step_exp_var_unknownE)
    by simp_all
next
  case (LoadStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 ed sz e\<^sub>2'')
  show ?case 
    using LoadStepAddr.prems
    apply (elim step_exp_load_step_addr_strictE)
    using LoadStepAddr.hyps(1) apply fastforce
    apply simp
    apply (rule LoadStepAddr.hyps(2))
    by auto
next
  case (LoadStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 ed sz)
  show ?case 
    using LoadStepMem.prems
    apply (elim step_exp_load_step_mem_strictE)
    using LoadStepMem.hyps(1) apply fastforce
    apply simp
    apply (rule LoadStepMem.hyps(2))
    by auto
next
  case (LoadWordBe sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
  using LoadWordBe.prems proof (elim step_exp_load_word_beE)
    fix va v' :: val
    assume "v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz])" thus ?thesis
      using LoadWordBe.hyps by simp
  next
    fix w :: word and va v' :: val
    assume v: "v = (va[w \<leftarrow> v', sz])" show ?thesis
    proof (cases w rule: word_exhaust)
      case (Word a b)
      thus ?thesis 
        using v LoadWordBe.hyps by simp
    qed
  qed (simp_all add: LoadWordBe.hyps)
next
  case (LoadWordEl v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz \<Delta> num)
  show ?case 
  using LoadWordEl.prems proof (elim step_exp_load_word_elE)
    fix va v' :: val
    assume "v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz])" thus ?thesis
      using LoadWordEl.hyps by simp
  next
    fix w :: word and va v' :: val
    assume v: "v = (va[w \<leftarrow> v', sz])" show ?thesis
    proof (cases w rule: word_exhaust)
      case (Word a b)
      thus ?thesis 
        using v LoadWordEl.hyps by simp
    qed
  qed (simp_all add: LoadWordEl.hyps)
next
  case (StoreStepVal \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2 en sz)
  thus ?case 
    by auto
next
  case (StoreStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 en sz v\<^sub>3)
  thus ?case 
    by auto
next
  case (StoreStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 en sz v\<^sub>3)
  thus ?case 
    by auto
next
  case (LetStep \<Delta> e\<^sub>1 e\<^sub>1' var e\<^sub>2)
  thus ?case
    by auto
next
  case (Let \<Delta> var v e)
  thus ?case 
    by auto
next
  case (IfStepCond \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 v\<^sub>3)
  show ?case 
    using IfStepCond.prems apply (elim step_exp_if_step_cond_strictE)
    using IfStepCond.hyps(1) apply fastforce    
    apply simp 
    apply (rule IfStepCond.hyps(2))
    apply simp
    by auto
next
  case (IfStepThen \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 v\<^sub>3)
  thus ?case 
    by auto
next
  case (IfStepElse \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2)
  thus ?case 
    by auto
next
  case (BopRhs \<Delta> e\<^sub>2 e\<^sub>2' v bop)
  show ?case
    using BopRhs.prems apply (elim step_exp_bop_rhs_strictE)
    using BopRhs.hyps(1) apply fastforce
    apply simp 
    apply simp 
    apply (rule BopRhs.hyps(2))
    by auto
next
  case (BopLhs \<Delta> e\<^sub>1 e\<^sub>1' bop e\<^sub>2)
  show ?case 
    using BopLhs.prems apply (elim step_exp_bop_lhs_strictE)
    using BopLhs.hyps(1) apply fastforce
    apply simp 
    using not_unknown apply blast
    apply simp 
    apply (rule BopLhs.hyps(2))
    by auto
next
  case (EqSame \<Delta> num sz)
  thus ?case 
    by (elim step_exp_eq_sameE, simp)
next
  case (EqDiff num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta>)
  thus ?case 
    apply (elim step_exp_eqE)    
    by (metis bv_eq_neq bv_not_eq true_neq_false(1) word_inject)
next
  case (NeqSame \<Delta> num sz)
  thus ?case 
    by (elim step_exp_neq_sameE, simp)
next
  case (NeqDiff num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta>)
  thus ?case 
    apply (elim step_exp_neqE)    
    by (metis bv_eq_neq bv_neq_true word_inject)
next
  case (Uop \<Delta> e e' uop)
  show ?case 
    using Uop.prems apply (elim step_exp_uop_strictE)
    using Uop.hyps(1) apply fastforce
    apply simp
    apply (rule Uop.hyps(2))
    by auto
next
  case (ConcatRhs \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1)
  show ?case 
    using ConcatRhs.prems apply (elim step_exp_concat_rhs_stepE)
    using ConcatRhs.hyps(1) apply fastforce
    apply simp
    apply (rule ConcatRhs.hyps(2))
    by auto
next
  case (ConcatLhs \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2)
  show ?case 
    using ConcatLhs.prems apply (elim step_exp_concat_lhs_stepE)
    using ConcatLhs.hyps(1) apply fastforce
    apply simp
    apply (rule ConcatLhs.hyps(2))
    by auto
next
  case (ExtractReduce \<Delta> e e' sz\<^sub>1 sz\<^sub>2)
  show ?case 
    using ExtractReduce.prems apply (elim step_exp_extract_reduce_strictE)
    using ExtractReduce.hyps(1) apply fastforce
    apply simp
    apply (rule ExtractReduce.hyps(2))
    by auto
next
  case (CastReduce \<Delta> e e' cast sz)
  show ?case 
    using CastReduce.prems apply (elim step_exp_cast_reduceE)
    using CastReduce.hyps(1) apply fastforce
    apply simp
    apply (rule CastReduce.hyps(2))
    by auto
qed auto


lemma step_exps_detD:
  assumes \<open>\<delta>' \<turnstile> e \<leadsto>* (Val v\<^sub>1)\<close> and \<open>\<delta>' \<turnstile> e \<leadsto>* (Val v\<^sub>2)\<close>
      and \<open>no_problem_children e\<close> \<comment> \<open>This shouldn't need to exist, however\<close>
      and unk: \<open>(\<forall>str t. v\<^sub>1 \<noteq> unknown[str]: t) \<or> (\<forall>str t. v\<^sub>2 \<noteq> unknown[str]: t)\<close>
    shows \<open>v\<^sub>1 = v\<^sub>2\<close>
using assms(1-3) proof (induct rule: step_exps_converse_induct)
  case base
  thus ?case 
    using step_exps_val_valE by blast
next
  case (step y z)
  show ?case 
  proof (cases \<open>has_unknowns y\<close>)
    case True
    show ?thesis 
    using unk proof (elim disjE)
      assume "\<forall>str t. v\<^sub>1 \<noteq> unknown[str]: t" 
      thus "v\<^sub>1 = v\<^sub>2"
        using True step(1,2,4) step_exp_always_has_unknownsI step_exps_not_unknownD
        by meson
    next
      assume "\<forall>str t. v\<^sub>2 \<noteq> unknown[str]: t" thus "v\<^sub>1 = v\<^sub>2"
        using True step(1,2,4) step_exp_always_has_unknownsI step_exps_not_unknownD
        by meson
    qed
  next
    case no_unknowns: False
    show ?thesis
    proof (cases \<open>\<exists>v. y = Val v\<close>)
      case True
      thus ?thesis 
        using step by auto
    next
      case False
      show ?thesis
      using step.prems(1) proof (rule step_exps_reduce_strict_valE)
        show "Val v\<^sub>2 \<noteq> y"
          using False by auto
      next
        fix e\<^sub>2 :: exp
        assume "Val v\<^sub>2 \<noteq> y"
          and step2: "\<delta>' \<turnstile> y \<leadsto> e\<^sub>2"
          and steps2: "\<delta>' \<turnstile> e\<^sub>2 \<leadsto>* Val v\<^sub>2"
        have G: "e\<^sub>2 = z" 
          using step2 step(1) no_unknowns apply (rule step_exp_detD)
          apply (metis local.step(1) local.step(5) no_unknowns step.hyps(2) step2 step_exp_detD step_exps_not_unknownD steps2 unk)
          using step.prems(2) by auto
        show "v\<^sub>1 = v\<^sub>2"      
          apply (rule step.hyps)
          apply (rule steps2[unfolded G])
          using never_problem_children step.hyps(1) step.prems(2) by blast
      qed
    qed
  qed
qed

lemma INT_WORD_EQ_UNK: "\<forall>str t. ((num \<Colon> sz)::val) \<noteq> unknown[str]: t" (* TODO *)
  unfolding word_constructor_exp_def unknown_constructor_exp_def by auto

lemmas step_exps_word_detD1 = step_exps_detD[where v\<^sub>1 = \<open>(_ \<Colon> _)\<close>,
        unfolded word_constructor_exp_def[symmetric], OF _ _ _ disjI1[OF INT_WORD_EQ_UNK]]

lemmas step_exps_word_detD2 = step_exps_detD[where v\<^sub>2 = \<open>(_ \<Colon> _)\<close>,
        unfolded word_constructor_exp_def[symmetric], OF _ _ _ disjI2[OF INT_WORD_EQ_UNK]]

lemmas step_exps_word_detD = step_exps_detD[where v\<^sub>1 = \<open>(_ \<Colon> _)\<close> and v\<^sub>2 = \<open>(_ \<Colon> _)\<close>,
        unfolded word_constructor_exp_def[symmetric], OF _ _ _ disjI1[OF INT_WORD_EQ_UNK]]

lemma step_exps_loads_detD1:
  assumes \<open>\<Delta>' \<turnstile> (Val v)[Val v', en]:usz \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and \<open>\<Delta>' \<turnstile> (Val v)[Val v', en]:usz \<leadsto>* (Val v\<^sub>2)\<close>
    shows \<open>v\<^sub>2 = (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
  using step_exps_word_detD1[OF assms] by auto

interpretation step_exps_loads_detD1: exp_val_word_fixed_sz_syntax3 \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 v\<^sub>2 e\<^sub>3 v\<^sub>3 w\<^sub>3 sz\<^sub>3. (\<And>\<Delta> sz en v.
  \<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, en]:usz \<leadsto>* e\<^sub>3 \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, en]:usz \<leadsto>* Val v \<Longrightarrow> v = v\<^sub>3)\<close>
  apply unfold_locales
  using step_exps_loads_detD1 by blast

lemma step_exps_loads_detD:
  assumes \<open>\<Delta> \<turnstile> (Val v)[Val v', en]:usz \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and \<open>\<Delta> \<turnstile> (Val v)[Val v', en]:usz \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>num\<^sub>1 = num\<^sub>2 \<and> sz\<^sub>1 = sz\<^sub>2\<close>
  using step_exps_word_detD[OF assms] by auto

lemmas step_exps_concat_detD = step_exps_detD[where e = \<open>_ \<copyright> _\<close>, unfolded no_problem_children.simps, OF _ _ conjI]
lemmas step_exps_concat_detD1 = step_exps_concat_detD[where v\<^sub>1 = \<open>(_ \<Colon> _)\<close>,
        unfolded word_constructor_exp_def[symmetric], OF _ _ _ _ disjI1[OF INT_WORD_EQ_UNK]]


lemma step_exps_cast_reduce_totalD:
  assumes steps: "\<delta>' \<turnstile> (Cast cast sz' e) \<leadsto>* Val v"
      and lhs_exp: \<open>\<delta>' \<turnstile> e \<leadsto>* (num \<Colon> sz)\<close> and lhs_no_problem_children: \<open>no_problem_children e\<close>
    shows "\<delta>' \<turnstile> (Cast cast sz' (num \<Colon> sz)) \<leadsto>* Val v"
using lhs_exp steps lhs_no_problem_children proof (induct rule: step_exps_converse_induct)
  case base
  then show ?case 
    by simp
next
  case (step y z)
  show ?case
  proof (rule step.hyps(3), use step.prems in \<open>elim step_exps_cast_reduce_valE\<close>)
    fix e\<^sub>2 :: exp
    assume step_y: "\<delta>' \<turnstile> cast:sz'[y] \<leadsto> e\<^sub>2" and nxt: "\<delta>' \<turnstile> e\<^sub>2 \<leadsto>* Val v"
      show "\<delta>' \<turnstile> cast:sz'[z] \<leadsto>* Val v"
    using step_y proof (elim step_exp_cast_reduceE)
      show "\<forall>v. y \<noteq> Val v"
          using local.step(1) by blast
      next
        fix e\<^sub>1' :: exp
        assume e': "e\<^sub>2 = cast:sz'[e\<^sub>1']" and step_y_e1: "\<delta>' \<turnstile> y \<leadsto> e\<^sub>1'"
        have e\<^sub>1': \<open>e\<^sub>1' = z\<close> 
          using step_y_e1 step(1) apply (rule step_exp_detD)
          using local.step(1) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exps_always_has_unknownsI apply blast
          using local.step(1) local.step(5) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exp_detD step_exps_always_has_unknownsI step_y_e1 
          apply metis
          using step.prems(2) .
        show ?thesis
          using nxt unfolding e' e\<^sub>1' .
      qed
  next
    show "no_problem_children z"
      using step(1) step.prems(2) by (rule never_problem_children)
  qed
qed

interpretation step_exps_cast_reduce_totalD: exp_val_word_fixed_sz_syntax
    \<open>\<lambda>e\<^sub>1 _ _ _. (\<And>\<Delta> cast sz e P v. \<lbrakk>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto>* Val v; \<Delta> \<turnstile> e \<leadsto>* e\<^sub>1;
       no_problem_children e\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<leadsto>* Val v)\<close>
  apply (standard)
  using step_exps_cast_reduce_totalD by blast


lemma step_exps_bop_lhs_reduce_totalD:
  assumes steps: "\<delta>' \<turnstile> (BinOp lhs bop rhs) \<leadsto>* Val v"
      and lhs_exp: \<open>\<delta>' \<turnstile> lhs \<leadsto>* (num \<Colon> sz)\<close> and lhs_no_problem_children: \<open>no_problem_children lhs\<close>
      and rhs_not_exp: \<open>\<forall>str t. rhs \<noteq> unknown[str]: t\<close>
    shows "\<delta>' \<turnstile> (BinOp (num \<Colon> sz) bop rhs) \<leadsto>* Val v"
using lhs_exp steps lhs_no_problem_children proof (induct rule: step_exps_converse_induct)
  case base
  then show ?case 
    by simp
next
  case (step y z)
  show ?case
  proof (rule step.hyps(3), use step.prems in \<open>elim step_exps_binary_reduce_valE\<close>)
    fix e' :: exp
    assume step_y_rhs: "\<delta>' \<turnstile> (BinOp y bop rhs) \<leadsto> e'" and nxt: "\<delta>' \<turnstile> e' \<leadsto>* Val v"
      show \<open>\<delta>' \<turnstile> (BinOp z bop rhs) \<leadsto>* Val v\<close>
      using step_y_rhs proof (elim step_exp_bop_lhs_strictE[OF _ _ rhs_not_exp])
        show "\<forall>v. y \<noteq> Val v"
          using local.step(1) by blast
      next
        fix e\<^sub>1' :: exp
        assume e': "e' = BinOp e\<^sub>1' bop rhs" and step_y_e1: "\<delta>' \<turnstile> y \<leadsto> e\<^sub>1'"
        have e\<^sub>1': \<open>e\<^sub>1' = z\<close> 
          using step_y_e1 step(1) apply (rule step_exp_detD)
          using local.step(1) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exps_always_has_unknownsI apply blast
          using local.step(1) local.step(5) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exp_detD step_exps_always_has_unknownsI step_y_e1 
          apply metis
          using step.prems(2) .
        show ?thesis
          using nxt unfolding e' e\<^sub>1' .
      qed
    next
      show \<open>no_problem_children z\<close>        
        using step(1) step.prems(2) by (rule never_problem_children)
   qed
 qed

lemma step_exps_bop_rhs_reduce_totalD:
  assumes steps: "\<delta>' \<turnstile> (BinOp (Val v\<^sub>2) bop rhs) \<leadsto>* Val v"
      and rhs_exp: \<open>\<delta>' \<turnstile> rhs \<leadsto>* (num \<Colon> sz)\<close> and rhs_no_problem_children: \<open>no_problem_children rhs\<close>
      and not_unk: \<open>\<forall>str t. v\<^sub>2 \<noteq> ((unknown[str]: t)::val)\<close>
    shows "\<delta>' \<turnstile> (BinOp (Val v\<^sub>2) bop (num \<Colon> sz)) \<leadsto>* Val v"
using rhs_exp steps rhs_no_problem_children proof (induct rule: step_exps_converse_induct)
  case base
  then show ?case 
    by simp
next
  case (step y z)
  show ?case 
  proof (rule step.hyps(3), use step.prems in \<open>elim step_exps_binary_reduce_valE\<close>)
    fix e' :: exp
    assume step_lhs_y: "\<delta>' \<turnstile> (BinOp (Val v\<^sub>2) bop y) \<leadsto> e'" and nxt: "\<delta>' \<turnstile> e' \<leadsto>* Val v"
      show \<open>\<delta>' \<turnstile> (BinOp (Val v\<^sub>2) bop z) \<leadsto>* Val v\<close>
      using step_lhs_y proof (elim step_exp_bop_rhs_strictE) 
        show "\<forall>v. y \<noteq> Val v"
          using local.step(1) by blast
      next
        show "\<forall>str t. v\<^sub>2 \<noteq> ((unknown[str]: t)::val)"
          using not_unk by auto
      next
        fix e\<^sub>2' :: exp
        assume e': "e' = BinOp (Val v\<^sub>2) bop e\<^sub>2'" and step_y_e2: "\<delta>' \<turnstile> y \<leadsto> e\<^sub>2'"
        have e\<^sub>1': \<open>e\<^sub>2' = z\<close> 
          using step_y_e2 step(1) apply (rule step_exp_detD)
          using local.step(1) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exps_always_has_unknownsI apply blast
          using local.step(1) local.step(5) not_unknown_word step.hyps(2) step_exp_always_has_unknownsI step_exp_detD step_exps_always_has_unknownsI step_y_e2 apply metis
          using step.prems(2) .
        show ?thesis
          using nxt unfolding e' e\<^sub>1' .
      qed
  next
    show \<open>no_problem_children z\<close>
      using step(1) step.prems(2) by (rule never_problem_children)
  qed
qed

interpretation step_exps_bop_rhs_reduce_totalD: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 v\<^sub>1 _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (BinOp e\<^sub>1 bop rhs) \<leadsto>* Val v; \<Delta> \<turnstile> rhs \<leadsto>* e\<^sub>2; 
       no_problem_children rhs; \<forall>str t. v\<^sub>1 \<noteq> unknown[str]: t\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (BinOp e\<^sub>1 bop e\<^sub>2) \<leadsto>* Val v)\<close>
  apply (standard)
  using step_exps_bop_rhs_reduce_totalD[OF _ _ _ INT_WORD_EQ_UNK, unfolded word_constructor_exp_def[symmetric]] by blast

context bop_lemmas
begin

lemma step_exps_lhs_reduce_totalD:
  assumes steps: "\<delta> s \<turnstile> (bop_fun lhs rhs) \<leadsto>* Val v"
      and lhs_exp: \<open>\<delta> s \<turnstile> lhs \<leadsto>* (num \<Colon> sz)\<close> and lhs_no_problem_children: \<open>no_problem_children lhs\<close>
      and rhs_not_exp: \<open>\<forall>str t. rhs \<noteq> unknown[str]: t\<close>
    shows "\<delta> s \<turnstile> (bop_fun (num \<Colon> sz) rhs) \<leadsto>* Val v"
  using assms unfolding bop_simps by (rule step_exps_bop_lhs_reduce_totalD)

lemma step_exps_rhs_reduce_totalD:
  assumes steps: "\<delta> s \<turnstile> (bop_fun (Val v\<^sub>2) rhs) \<leadsto>* Val v"
      and rhs_exp: \<open>\<delta> s \<turnstile> rhs \<leadsto>* (num \<Colon> sz)\<close> and rhs_no_problem_children: \<open>no_problem_children rhs\<close>
      and not_unk: \<open>\<forall>str t. v\<^sub>2 \<noteq> ((unknown[str]: t)::val)\<close>
    shows "\<delta> s \<turnstile> (bop_fun (Val v\<^sub>2) (num \<Colon> sz)) \<leadsto>* Val v"
  using assms unfolding bop_simps by (rule step_exps_bop_rhs_reduce_totalD)

lemmas step_exps_word_rhs_reduce_totalD = step_exps_rhs_reduce_totalD[OF _ _ _ INT_WORD_EQ_UNK, unfolded word_constructor_exp_def[symmetric]]

end

end
