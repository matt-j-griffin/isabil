theory Statement_Intros
  imports Statement_Syntax
          "../ExpressionSemantics/Expression_Intros"
begin

lemma SEQ_REC:
  assumes \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>',w',seq\<close>
  using assms apply (auto simp add: step_pred_bil_def eval_pred_stmt_def)
  by (simp add: eval_inf_stmt_eval_inf_bil.intros(9))

lemma SEQ_LAST:
  assumes \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 (Stmt s\<^sub>2 Empty) \<leadsto> \<Delta>',w',(Stmt s\<^sub>2 Empty)\<close>
  using assms SEQ_REC by auto

lemma SEQ_ONE:
  assumes \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 Empty \<leadsto> \<Delta>',w',Empty\<close>
  using assms SEQ_REC by auto

lemma SEQ_NIL: \<open>\<Delta>,w \<turnstile> Empty \<leadsto> \<Delta>,w,Empty\<close>
  by (simp add: step_pred_bil_def)

lemma SEQ_NIL_NEQ: 
  assumes \<open>\<Delta>\<noteq>\<Delta>' \<or> w\<noteq>w\<close> 
    shows \<open>\<not>(\<Delta>',w' \<turnstile> Empty \<leadsto> \<Delta>,w,Empty)\<close>
  using assms step_pred_bil_def by (metis bil.distinct(1) eval_inf_bil.simps)

lemma SEQ_TOTAL_REC: 
    \<open>(\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>',w',Empty) \<longleftrightarrow> eval_inf_bil \<Delta> w seq \<Delta>' w'\<close>
  apply (auto simp add: step_pred_bil_def)
  apply (simp add: eval_inf_stmt_eval_inf_bil.intros(10))
  by (metis bil.distinct(1) eval_inf_bil.simps)

lemma SEQ_NEXT:
  assumes \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close> and \<open>\<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>'',w'',Empty\<close>
    shows \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>'',w'',Empty\<close>
  using assms eval_inf_stmt_eval_inf_bil.intros(9) eval_pred_stmt_def step_pred_bil_empty_equiv by blast

lemma MOVE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>\<Delta>,w \<turnstile> (var := e) \<leadsto> (\<Delta>(var \<mapsto> v)),w\<close> 
  using assms apply auto 
  by (simp add: eval_inf_stmt_eval_inf_bil.intros(6) eval_pred_stmt_def)

lemma JMP:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w')\<close>
    shows \<open>\<Delta>,w \<turnstile> (Jmp e) \<leadsto> \<Delta>,w'\<close>
  using assms apply auto
  by (simp add: eval_inf_stmt_eval_inf_bil.intros(5) eval_pred_stmt_def)

lemma CPUEXN: \<open>\<Delta>,w \<turnstile> (CpuExn num) \<leadsto> \<Delta>,w\<close>
  by (simp add: eval_inf_stmt_eval_inf_bil.intros(7) eval_pred_stmt_def)

lemma SPECIAL:\<open>\<Delta>,w \<turnstile> (Special str) \<leadsto> \<Delta>,w\<close>
  by (simp add: eval_inf_stmt_eval_inf_bil.intros(8) eval_pred_stmt_def)

lemma IF_TRUE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
      and \<open>\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
  unfolding eval_pred_stmt_def apply (rule eval_inf_stmt_eval_inf_bil.intros(3))
  using assms(1) apply auto[1] (* TODO this is poor *)
  using assms(2) step_pred_bil_empty_equiv by auto

lemma IF_FALSE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
      and \<open>\<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
  unfolding eval_pred_stmt_def apply (rule eval_inf_stmt_eval_inf_bil.intros(4))
  using assms(1) apply auto[1] (* TODO this is poor *)
  using assms(2) step_pred_bil_empty_equiv by auto

lemmas IFTHEN_TRUE = IF_TRUE[of _ _ _ _ _ _ Empty]

lemma IFTHEN_FALSE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq) \<leadsto> \<Delta>,w\<close>
  using assms IF_FALSE SEQ_NIL by simp

lemma WHILE:
  assumes \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true\<close>
      and \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq \<leadsto> \<Delta>\<^sub>2,w\<^sub>2,Empty\<close>
      and \<open>\<Delta>\<^sub>2,w\<^sub>2 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
  using assms SEQ_TOTAL_REC eval_inf_stmt_eval_inf_bil.intros(1) eval_pred_stmt_def true_val_def by force

lemma WHILE_FALSE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (While e seq) \<leadsto> \<Delta>,w\<close>
  unfolding eval_pred_stmt_def apply (rule eval_inf_stmt_eval_inf_bil.intros(2))
  using assms(1) by simp


end
