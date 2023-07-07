theory Statement_Elims
  imports Statement_Syntax
begin                  

lemma step_bil_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> ([]::bil) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding step_syntax_list_def by (rule EmptyE, safe)

lemma step_bil_seqE:
    fixes s :: stmt
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s # seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
    shows \<open>\<exists>\<Delta>\<^sub>2 w\<^sub>2. \<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s \<leadsto> \<Delta>\<^sub>2, w\<^sub>2 \<and> \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
  using assms unfolding step_syntax_list_def step_syntax_stmt_def apply (rule NextE)
  by blast

lemma step_stmt_specialE:
  assumes \<open>\<Delta>,w \<turnstile> (Special str) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding step_syntax_stmt_def by (rule SpecialE, safe)

lemma step_stmt_cpuexnE:
  assumes \<open>\<Delta>,w \<turnstile> (cpuexn code) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding step_syntax_stmt_def by (rule CpuExnE, safe)

lemma step_stmt_moveE:
  assumes \<open>\<Delta>,w \<turnstile> (var := e) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<exists>v. (\<Delta> \<turnstile> e \<leadsto>* v) \<and> \<Delta>' = \<Delta>(var \<mapsto> v) \<and> w' = w\<close>
  using assms unfolding step_syntax_stmt_def apply (rule MoveE, safe)
  apply (rule exI[of _ \<open>eval_exp \<Delta> e\<close>])
  by auto

lemma step_stmt_jmpE:
  assumes \<open>\<Delta>,w \<turnstile> (jmp e) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<exists>num sz. (\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz)) \<and> \<Delta>' = \<Delta> \<and> w' = (num \<Colon> sz)\<close>
  using assms unfolding step_syntax_stmt_def apply (rule JmpE, safe)
  by auto

lemma step_stmt_if_trueE:
  assumes \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w'\<close>
using assms(1) unfolding step_syntax_stmt_def step_syntax_list_def proof (rule IfE)
  show \<open>true = eval_exp \<Delta> e \<Longrightarrow>
    step_pred_bil \<Delta> w seq\<^sub>1 \<Delta>' w' \<Longrightarrow>
    step_pred_bil \<Delta> w seq\<^sub>1 \<Delta>' w'\<close>
    by blast
qed (use assms(2) in auto)

lemmas step_stmt_if_then_trueE = step_stmt_if_trueE[of _ _ _ _ \<open>[]\<close>]

lemma step_stmt_if_falseE:
  assumes \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w'\<close>
using assms(1) unfolding step_syntax_stmt_def step_syntax_list_def by (rule IfE, use assms(2) in auto)

lemma step_stmt_if_then_falseE:
  assumes \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  apply (rule step_bil_emptyE)
  using assms by (rule step_stmt_if_falseE)

lemma step_stmt_whileE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<close>
      and \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<exists>\<Delta>\<^sub>2 w\<^sub>2. \<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq \<leadsto> \<Delta>\<^sub>2, w\<^sub>2 \<and> \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<close>
using assms(1) unfolding step_syntax_stmt_def step_syntax_list_def by (rule WhileE, use assms(2) in auto)


lemma step_stmt_while_falseE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>2, w\<^sub>2\<close>
      and \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>\<^sub>2 = \<Delta>\<^sub>1 \<and> w\<^sub>2 = w\<^sub>1\<close>
using assms(1) unfolding step_syntax_stmt_def step_syntax_list_def by (rule WhileE, use assms(2) in auto)

lemma step_bil_stmt_deterministic_intermediary:
  fixes stmt :: stmt and seq :: bil shows
  "((\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>1,w1) \<longrightarrow> (\<forall>\<Delta>2 w2. (\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>2,w2) \<longrightarrow> \<Delta>1 = \<Delta>2 \<and> w1 = w2)) \<and>
   ((\<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>3,w3) \<longrightarrow> (\<forall>\<Delta>4 w4. (\<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>4,w4) \<longrightarrow> \<Delta>3 = \<Delta>4 \<and> w3 = w4))"
unfolding step_syntax_stmt_def step_syntax_list_def
proof (induct  rule: step_pred_stmt_step_pred_bil.induct)
  case (WhileTrue \<Delta>\<^sub>1 e w\<^sub>1 seq \<Delta>\<^sub>2 w\<^sub>2 \<Delta>\<^sub>3 w\<^sub>3)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (rule WhileE[of \<Delta>\<^sub>1], blast, blast)
      by (metis eval_exps_pred_exp.elims(2) true_not_false_val)
    .
next
  case (WhileFalse \<Delta> e w seq)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (rule WhileE[of \<Delta>], blast)
      apply (metis eval_exps_pred_exp.elims(2) true_not_false_val)
      by blast
    .
next
  case (IfTrue \<Delta> e w seq\<^sub>1 \<Delta>' w' seq\<^sub>2)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (rule IfE, blast, blast)
      by (metis eval_exps_pred_exp.elims(2) true_not_false_val)
    .
next
  case (IfFalse \<Delta> e w seq\<^sub>2 \<Delta>' w' seq\<^sub>1)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (rule IfE, blast)
      apply (metis eval_exps_pred_exp.elims(2) true_not_false_val)
      by blast
    .
next
  case (Jmp \<Delta> e num sz w)
  then show ?case
    apply clarify
    subgoal for \<Delta>2 w2 num' sz'
      apply simp
      by (metis word_eq)
    .
next
  case (Move \<Delta> e v w var)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      by simp
    .
next
  case (CpuExn \<Delta> w code)
  then show ?case 
    using step_stmt_cpuexnE by blast
next
  case (Special \<Delta> w str)
  then show ?case 
    using step_stmt_specialE by blast
next
  case (Next \<Delta> w s \<Delta>'' w'' seq \<Delta>' w')
  then show ?case 
    by force
next
  case (Empty \<Delta> w)
  then show ?case by force
qed

lemma step_bil_stmt_deterministic:
  fixes stmt :: stmt and seq :: bil shows
  \<open>\<lbrakk>\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>1,w1; \<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>2,w2\<rbrakk> \<Longrightarrow> \<Delta>1 = \<Delta>2 \<and> w1 = w2\<close>
  \<open>\<lbrakk>\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>3,w3; \<Delta>,w \<turnstile> seq \<leadsto> \<Delta>4,w4\<rbrakk> \<Longrightarrow> \<Delta>3 = \<Delta>4 \<and> w3 = w4\<close>
  using step_bil_stmt_deterministic_intermediary by presburger+

lemmas step_stmt_deterministic = step_bil_stmt_deterministic(1)
lemmas step_bil_deterministic = step_bil_stmt_deterministic(2)

end
