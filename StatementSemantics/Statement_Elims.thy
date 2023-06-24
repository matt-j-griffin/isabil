theory Statement_Elims
  imports Statement_Syntax
begin

lemma step_bil_sameE:
  assumes \<open>\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>',w',seq\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
using assms by (cases rule: step_pred_bil.cases[of _ _ seq _ _ seq], simp_all)

lemmas step_bil_emptyE = step_bil_sameE[of _ _ Empty]

lemma step_bil_seqE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>\<^sub>2,w\<^sub>2,seq\<close>
    shows \<open>(\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s\<^sub>1 \<leadsto> \<Delta>\<^sub>2, w\<^sub>2)\<close>
using assms proof (cases rule: step_pred_bil.cases)
  case (Next \<Delta>'' w'')
  show ?thesis 
    using Next(2) apply (drule_tac step_bil_sameE, simp)
    using Next(1) by simp
next
  case Eq
  then show ?thesis 
    using Stmt_not_nested by simp
qed

lemma step_bil_nextE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3,seq'\<close> and \<open>seq' \<noteq> Stmt s\<^sub>1 seq\<close>
    shows \<open>\<exists>\<Delta>\<^sub>2 w\<^sub>2. (\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s\<^sub>1 \<leadsto> \<Delta>\<^sub>2, w\<^sub>2 \<and> \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3,seq')\<close>
using assms proof (cases rule: step_pred_bil.cases)
  case (Next \<Delta>\<^sub>2 w\<^sub>2)
  show ?thesis 
    apply (rule exI[of _ \<Delta>\<^sub>2], rule exI[of _ w\<^sub>2])
    using Next by simp
next
  case Eq
  then show ?thesis 
    using assms(2) by simp
qed

lemma step_stmt_specialE:
  assumes \<open>\<Delta>,w \<turnstile> (Special str) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms by (cases rule: step_pred_stmt.cases, auto)

lemma step_stmt_cpuexnE:
  assumes \<open>\<Delta>,w \<turnstile> (cpuexn code) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms by (cases rule: step_pred_stmt.cases, auto)

lemma step_stmt_moveE:
  assumes \<open>\<Delta>,w \<turnstile> (var := e) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<exists>v. (\<Delta> \<turnstile> e \<leadsto>* v) \<and> \<Delta>' = \<Delta>(var \<mapsto> v) \<and> w' = w\<close>
using assms proof (cases rule: step_pred_stmt.cases)
  case (Move v)
  show ?thesis 
    apply (rule exI[of _ v])
    using Move by blast
qed

lemma step_stmt_jmpE:
  assumes \<open>\<Delta>,w \<turnstile> (jmp e) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<exists>num sz. (\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz)) \<and> \<Delta>' = \<Delta> \<and> w' = (num \<Colon> sz)\<close>
using assms proof (cases rule: step_pred_stmt.cases)
  case (Jmp num sz)
  show ?thesis 
    apply (rule exI[of _ num], rule exI[of _ sz])
    using Jmp by blast
qed

lemma step_stmt_if_trueE:
  assumes \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w',Empty\<close>
using assms by (cases rule: step_pred_stmt.cases, auto)

lemmas step_stmt_if_then_trueE = step_stmt_if_trueE[of _ _ _ _ Empty]

lemma step_stmt_if_falseE:
  assumes \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w',Empty\<close>
using assms by (cases rule: step_pred_stmt.cases, auto)

lemma step_stmt_if_then_falseE:
  assumes \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  apply (rule step_bil_emptyE)
  using assms by (rule step_stmt_if_falseE)

lemma step_stmt_whileE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<close>
      and \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<exists>\<Delta>\<^sub>2 w\<^sub>2. \<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq \<leadsto> \<Delta>\<^sub>2, w\<^sub>2, Empty \<and> \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<close>
using assms by (cases rule: step_pred_stmt.cases, auto)

lemma step_stmt_while_falseE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>2, w\<^sub>2\<close>
      and \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>\<^sub>2 = \<Delta>\<^sub>1 \<and> w\<^sub>2 = w\<^sub>1\<close>
  using assms by (cases rule: step_pred_stmt.cases, auto)

lemma step_bil_stmt_deterministic_intermediary:
  "((\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>1,w1) \<longrightarrow> (\<forall>\<Delta>2 w2. (\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>2,w2) \<longrightarrow> \<Delta>1 = \<Delta>2 \<and> w1 = w2)) \<and>
   ((\<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>3,w3,seq') \<longrightarrow> (\<forall>\<Delta>4 w4. (\<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>4,w4,seq') \<longrightarrow> \<Delta>3 = \<Delta>4 \<and> w3 = w4))"
proof (induct  rule: step_pred_stmt_step_pred_bil.induct)
  case (WhileTrue \<Delta>\<^sub>1 e w\<^sub>1 seq \<Delta>\<^sub>2 w\<^sub>2 \<Delta>\<^sub>3 w\<^sub>3)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_whileE[of \<Delta>\<^sub>1])
      apply clarify
      by blast
    .
next
  case (WhileFalse \<Delta> e w seq)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_while_falseE[of])
      apply clarify
      by blast
    .
next
  case (IfTrue \<Delta> e w seq\<^sub>1 \<Delta>' w' seq\<^sub>2)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_if_trueE)
      apply blast
      apply (erule allE[of _ \<Delta>2], erule allE[of _ w2])
      by blast
    .
next
  case (IfFalse \<Delta> e w seq\<^sub>2 \<Delta>' w' seq\<^sub>1)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_if_falseE)
      apply blast
      apply (erule allE[of _ \<Delta>2], erule allE[of _ w2])
      by blast
    .
next
  case (Jmp \<Delta> e num sz w)
  then show ?case
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_jmpE)
      apply (elim exE conjE)
      unfolding word_constructor_val_def
      apply simp
      by (metis word_eq)
    .
next
  case (Move \<Delta> e v w var)
  then show ?case 
    apply clarify
    subgoal for \<Delta>2 w2
      apply (drule_tac step_stmt_moveE)
      apply (elim exE conjE)
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
  case (Next \<Delta> w s\<^sub>1 \<Delta>'' w'' seq \<Delta>' w' seq')
  then show ?case 
    by (metis step_bil_nextE)
next
  case (Eq \<Delta> w seq)
  then show ?case 
    by (metis step_bil_sameE)
qed

lemma step_bil_stmt_deterministic:
  "\<lbrakk>\<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>1,w1; \<Delta>,w \<turnstile> stmt \<leadsto> \<Delta>2,w2\<rbrakk> \<Longrightarrow> \<Delta>1 = \<Delta>2 \<and> w1 = w2"
  "\<lbrakk>\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>3,w3,seq'; \<Delta>,w \<turnstile> seq \<leadsto> \<Delta>4,w4,seq'\<rbrakk> \<Longrightarrow> \<Delta>3 = \<Delta>4 \<and> w3 = w4"
  using step_bil_stmt_deterministic_intermediary by force+

lemmas step_stmt_deterministic = step_bil_stmt_deterministic(1)
lemmas step_bil_deterministic = step_bil_stmt_deterministic(2)

end
