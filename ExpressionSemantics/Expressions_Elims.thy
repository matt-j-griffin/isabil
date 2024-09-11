
section \<open>Elimination rules for big step expressions\<close>

theory Expressions_Elims
  imports Expressions_Rules Expression_Elims
          
begin

text \<open>Better reduce rule that includes the assumption e3 \<noteq> e1\<close>

lemma step_exps_reduceE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and reflE: \<open>e\<^sub>3 = e\<^sub>1 \<Longrightarrow> P\<close>
    shows P
proof (cases \<open>e\<^sub>3 = e\<^sub>1\<close>)
  case True
  then show ?thesis by (rule reflE)
next
  case False
  show ?thesis 
    using assms(1) apply (rule ReduceE)
    subgoal for e\<^sub>2
      using False by (intro reduceE[of e\<^sub>2] conjI)
    using False by (elim notE)
qed


lemma step_exps_reduce_strictE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> and \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (rule step_exps_reduceE)
  subgoal for e\<^sub>2
    using assms(2) by (intro reduceE[of e\<^sub>2] conjI)
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

context bop_lemmas
begin

(*(\<And>e\<^sub>2. ?\<Delta> \<turnstile> BinOp ?uua ?uuaa ?uub \<leadsto> e\<^sub>2 \<Longrightarrow> ?\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* Val ?uu \<Longrightarrow> ?P) \<Longrightarrow> ?P*)
lemma step_exps_reduce_valE:
  assumes major: \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto>* Val v\<close>
      and minor: \<open>\<And>e'. \<lbrakk>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> e'; \<Delta> \<turnstile> e' \<leadsto>* Val v\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding bop_simps by (rule step_exps_binary_reduce_valE)

interpretation step_exps_reduce_valE: exp_val_syntax \<open>\<lambda>e v.
    (\<And>\<Delta> e\<^sub>1 e\<^sub>2 P. \<lbrakk>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto>* e; (\<And>e'. \<lbrakk>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> e'; \<Delta> \<turnstile> e' \<leadsto>* e\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
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
    (\<And>\<Delta> v' id t P. \<lbrakk>\<Delta> \<turnstile> (id :\<^sub>t t) \<leadsto>* e; (id :\<^sub>t t, v') \<in>\<^sub>\<Delta> \<Delta>; v' = v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exps_var_inE in blast)

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
method rewrite = (simp only:)

method solve_expsE_scaffold methods recurs solve_exp uses add = (
  (*TODO*)
  (erule step_exps_val_wordE.word, rewrite) |
(*  (erulel rules: step_exps_valE step_exps_valE.storage step_exps_valE.word 
    step_exps_valE.true step_exps_valE.false step_exps_valE.unknown, (unfold word_inject)?, clarify?) |*)

  (erule step_exps_var_inE.word step_exps_var_inE.true step_exps_var_inE.false, 
      solve_in_var add: add, (unfold word_inject)?, clarify?) |
  (erulel rules: step_exps_var_inE, solve_in_var add: add, clarify) |

  (erulel rules: step_exps_concatE) |
  (erulel rules: step_exps_concatE.is_word2[rotated 2], prefer_last, solve_is_wordI, prefer_last, solve_is_wordI) |

  (erule step_exps_concat_rhs_stepE, solves force, solve_exp, recurs?) |

  (erule step_exps_concat_lhs_stepE.is_val[rotated], solves force, prefer_last, solve_is_valI, 
    solve_exp, recurs?) |

  \<comment> \<open>Solve other values\<close>
  (erule step_exps_val_valE.is_val[rotated], prefer_last, solve_is_valI, clarify) |

  \<comment> \<open>Reduction rules come last\<close>
  (erulel rules: 
    plus.step_exps_reduce_wordE
    step_exps_concat_reduce_valE step_exps_load_reduce_valE step_exps_store_reduce_valE
    step_exps_cast_reduce_valE plus.step_exps_reduce_valE step_exps_binary_reduce_valE 
    step_exps_unary_reduce_valE step_exps_let_reduce_valE step_exps_ite_reduce_valE 
    step_exps_extract_reduce_valE step_exps_var_reduce_valE,
    solve_exp, recurs?)
  |
  (erule step_exps_val_wordE.is_word[rotated],
          prefer_last, solve_is_wordI, rewrite)
)

method solve_expsE uses add = (
    solve_expsE_scaffold \<open>solve_expsE add: add\<close> \<open>solve_expE add: add\<close>
)


end
