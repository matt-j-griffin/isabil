theory Statement_Intros
  imports Statement_Syntax
          "../ExpressionSemantics/Expression_Intros"
begin

lemma step_bil_emptyI[intro!]: \<open>\<Delta>,w \<turnstile> ([]::bil) \<leadsto> \<Delta>,w\<close>
  unfolding step_syntax_list_def by (rule Empty)

lemma step_bil_seqI[intro]:
  fixes s :: stmt
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close> and \<open>\<Delta>\<^sub>2,w\<^sub>2 \<turnstile> seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (s # seq) \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule Next)

lemma step_bil_singleI[intro]:
  fixes s :: stmt
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> [s] \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
  using assms apply (rule step_bil_seqI)
  by (rule step_bil_emptyI)

lemma step_stmt_whileI[intro]:
  assumes \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true\<close> and \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
      and \<open>\<Delta>\<^sub>2,w\<^sub>2 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule WhileTrue)

lemma step_stmt_while_falseI[intro]:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (While e seq) \<leadsto> \<Delta>,w\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule WhileFalse)

lemma step_stmt_if_trueI[intro]:
  assumes \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true\<close> and \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule IfTrue)

lemmas step_stmt_if_then_trueI = step_stmt_if_trueI[of _ _ _ _ _ _ \<open>[]\<close>]

lemma step_stmt_if_falseI:
  assumes \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* false\<close> and \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
    shows \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>\<^sub>2,w\<^sub>2\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule IfFalse)

lemma step_stmt_jmpI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz)\<close>
    shows \<open>\<Delta>,w \<turnstile> jmp e \<leadsto> \<Delta>,(num \<Colon> sz)\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule Jmp)

lemma step_stmt_moveI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>\<Delta>,w \<turnstile> (var := e) \<leadsto> (\<Delta>(var \<mapsto> v)),w\<close>
  using assms unfolding step_syntax_stmt_def step_syntax_list_def by (rule Move)

lemma step_stmt_cpuexnI: "\<Delta>,w \<turnstile> (cpuexn code) \<leadsto> \<Delta>,w"
   unfolding step_syntax_stmt_def step_syntax_list_def by (rule CpuExn)

lemma step_stmt_specialI: "\<Delta>,w \<turnstile> (special[str]) \<leadsto> \<Delta>,w"
   unfolding step_syntax_stmt_def step_syntax_list_def by (rule Special)

lemma step_stmt_if_then_falseI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>, w\<close>
  using assms apply (rule step_stmt_if_falseI)
  by (rule step_bil_emptyI)

(* Old names  *)
lemmas SEQ_NIL = step_bil_emptyI
lemmas SEQ_REC = step_bil_seqI

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

end
