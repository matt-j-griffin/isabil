theory Statement_Intros
  imports Statement_Syntax
          "../ExpressionSemantics/Expression_Intros"
begin

lemmas step_bil_emptyI = Eq[of _ _ Empty]
lemmas step_bil_nextI = Next

lemma step_bil_seqI:
  assumes \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>',w',seq\<close>
  using assms apply (rule step_bil_nextI)
  apply (rule Eq)
  by simp

lemmas step_stmt_whileI = WhileTrue
lemmas step_stmt_while_falseI = WhileFalse
lemmas step_stmt_if_trueI = IfTrue
lemmas step_stmt_if_then_trueI = step_stmt_if_trueI[of _ _ _ _ _ _ Empty]
lemmas step_stmt_if_falseI = IfFalse
lemmas step_stmt_jmpI = Jmp
lemmas step_stmt_moveI = Move
lemmas step_stmt_cpuexnI = CpuExn
lemmas step_stmt_specialI = Special

lemma step_stmt_if_then_falseI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>, w\<close>
  using assms apply (rule step_stmt_if_falseI)
  by (rule step_bil_emptyI)


lemmas SEQ_NIL = step_bil_emptyI
lemmas SEQ_ONE = step_bil_seqI[of _ _ _ _ _ Empty]
lemmas SEQ_REC = step_bil_seqI
lemmas SEQ_LAST = step_bil_seqI[of _ _ _ _ _ \<open>Stmt _ Empty\<close>]

lemmas WHILE = step_stmt_whileI
lemmas WHILE_FALSE = step_stmt_while_falseI
lemmas IF_TRUE = step_stmt_if_trueI
lemmas IFTHEN_TRUE = step_stmt_if_then_trueI
lemmas IF_FALSE = step_stmt_if_falseI
lemmas IFTHEN_FALSE = step_stmt_if_then_falseI
lemmas JMP = step_stmt_jmpI
lemmas MOVE = step_stmt_moveI
lemmas CPUEXN = step_stmt_cpuexnI
lemmas SPECIAL = step_stmt_specialI

(*
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
*)


end
