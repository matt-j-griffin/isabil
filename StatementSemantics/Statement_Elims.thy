theory Statement_Elims
  imports Statement_Syntax
begin                  

subsection \<open>BIL\<close>

lemma step_bil_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> ([]::bil) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_list_def by (elim EmptyE E)

lemma step_bil_seqE:
    fixes s :: stmt
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s # seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<close>
      and E: \<open>\<And>\<Delta>\<^sub>2 w\<^sub>2.\<lbrakk>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> s \<leadsto> \<Delta>\<^sub>2, w\<^sub>2; \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> seq \<leadsto> \<Delta>\<^sub>3,w\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
    shows P 
  using assms(1) unfolding step_syntax_list_def apply (elim NextE)
  unfolding step_syntax_list_def[symmetric] step_syntax_stmt_def[symmetric] by (elim E)

subsection \<open>Special\<close>

lemma step_stmt_specialE:
  assumes \<open>\<Delta>,w \<turnstile> (Special str) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding step_syntax_stmt_def by (elim SpecialE E)

subsection \<open>CpuExn\<close>

lemma step_stmt_cpuexnE:
  assumes \<open>\<Delta>,w \<turnstile> (cpuexn code) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_stmt_def by (elim CpuExnE E)

subsection \<open>Move\<close>

lemma step_stmt_moveE:
  assumes \<open>\<Delta>,w \<turnstile> (var := e) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<And>v. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (Val v); \<Delta>' = \<Delta>(var \<mapsto> v); w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_stmt_def by (elim MoveE E)

subsection \<open>Jmp\<close>

lemma step_stmt_jmpE:
  assumes \<open>\<Delta>,w \<turnstile> (jmp e) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<And>num sz. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz); \<Delta>' = \<Delta>; w' = (num \<Colon> sz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_stmt_def by (elim JmpE E)

subsection \<open>If\<close>

lemma step_stmt_if_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> (If e [] []) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using E assms(1) step_stmt_if_empty by blast

lemma step_stmt_ifE:
  assumes \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
      and Etrue: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* true; \<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w'\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* false; \<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_stmt_def apply (elim IfE)
  unfolding step_syntax_list_def[symmetric]
  subgoal by (rule Etrue)
  subgoal by (rule Efalse)
  .

lemma step_stmt_if_thenE:
  assumes \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>',w'\<close>
      and Etrue: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* true; \<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w'\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* false; \<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim step_stmt_ifE Etrue Efalse step_bil_emptyE)

lemma step_stmt_if_elseE:
  assumes \<open>\<Delta>,w \<turnstile> (If e [] seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
      and Etrue: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* true; \<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* false; \<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim step_stmt_ifE Etrue Efalse step_bil_emptyE)

subsection \<open>While\<close>

lemma step_stmt_while_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> (While e []) \<leadsto> \<Delta>', w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using E assms(1) step_stmt_while_empty by auto

lemma step_stmt_whileE:
  assumes \<open>\<Delta>\<^sub>1,w\<^sub>1 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<close>
      and Etrue: \<open>\<And>\<Delta>\<^sub>2 w\<^sub>2.\<lbrakk>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true; \<Delta>\<^sub>1,w\<^sub>1 \<turnstile> seq \<leadsto> \<Delta>\<^sub>2, w\<^sub>2; \<Delta>\<^sub>2,w\<^sub>2 \<turnstile> (While e seq) \<leadsto> \<Delta>\<^sub>3, w\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* false; \<Delta>\<^sub>3 = \<Delta>\<^sub>1; w\<^sub>3 = w\<^sub>1\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding step_syntax_stmt_def apply - 
  apply (erule WhileE)
  subgoal 
    unfolding step_syntax_stmt_def[symmetric] step_syntax_list_def[symmetric] by (erule Etrue)
  subgoal by (erule Efalse)
  .

end
