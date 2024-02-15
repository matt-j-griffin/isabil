theory Statement_Syntax
  imports "../ExpressionSemantics/Expressions_Rules"
begin

inductive
  step_pred_stmt :: \<open>variables \<Rightarrow> word \<Rightarrow> stmt \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close> and
  step_pred_bil :: \<open>variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close>
where
  WhileTrue: \<open>\<lbrakk>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true; step_pred_bil \<Delta>\<^sub>1 w\<^sub>1 seq \<Delta>\<^sub>2 w\<^sub>2; step_pred_stmt \<Delta>\<^sub>2 w\<^sub>2 (While e seq) \<Delta>\<^sub>3 w\<^sub>3\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta>\<^sub>1 w\<^sub>1 (While e seq) \<Delta>\<^sub>3 w\<^sub>3\<close> |
  WhileFalse: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* false\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta> w (While e seq) \<Delta> w\<close> |
  IfTrue: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* true; step_pred_bil \<Delta> w seq\<^sub>1 \<Delta>' w'\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) \<Delta>' w'\<close> |
  IfFalse: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* false; step_pred_bil \<Delta> w seq\<^sub>2 \<Delta>' w'\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) \<Delta>' w'\<close> |
  Jmp: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz)\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta> w (Jmp e) \<Delta> (num \<Colon> sz)\<close> |
  Move: \<open>\<lbrakk>\<Delta> \<turnstile> e \<leadsto>* (Val v)\<rbrakk> \<Longrightarrow> step_pred_stmt \<Delta> w (Move var e) (\<Delta>(var \<mapsto> v)) w\<close> |
  CpuExn: \<open>step_pred_stmt \<Delta> w (CpuExn code) \<Delta> w\<close> |
  Special: \<open>step_pred_stmt \<Delta> w (Special str) \<Delta> w\<close> |
  Next: \<open>\<lbrakk>step_pred_stmt \<Delta> w s \<Delta>'' w''; step_pred_bil \<Delta>'' w'' seq \<Delta>' w'\<rbrakk> \<Longrightarrow> step_pred_bil \<Delta> w (s # seq) \<Delta>' w'\<close> |
  Empty: \<open>step_pred_bil \<Delta> w [] \<Delta> w\<close>

inductive_cases NextE[elim!]: \<open>step_pred_bil \<Delta> w (s # seq) \<Delta>' w'\<close>
inductive_cases EmptyE[elim!]: \<open>step_pred_bil \<Delta> w [] \<Delta>' w'\<close>

inductive_cases SpecialE[elim!]: \<open>step_pred_stmt \<Delta> w (Special str) \<Delta>' w'\<close>
inductive_cases CpuExnE[elim!]: \<open>step_pred_stmt \<Delta> w (CpuExn code) \<Delta>' w'\<close>
inductive_cases MoveE[elim!]: \<open>step_pred_stmt \<Delta> w (Move var e) \<Delta>' w'\<close>
inductive_cases JmpE[elim!]: \<open>step_pred_stmt \<Delta> w (Jmp e) \<Delta>' w'\<close>
inductive_cases IfE[elim!]: \<open>step_pred_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) \<Delta>' w'\<close>
inductive_cases WhileE[elim]: \<open>step_pred_stmt \<Delta> w (While e seq) \<Delta>' w'\<close>

declare step_pred_stmt_step_pred_bil.intros [intro]


text \<open>Fix syntax for BIL statements classes\<close>

class step_syntax = 
  fixes step_syntax :: \<open>variables \<Rightarrow> word \<Rightarrow> 'a \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close> (\<open>_,_ \<turnstile> _ \<leadsto> _,_\<close>)

instantiation list :: (step_syntax) step_syntax
begin 

definition
  step_syntax_list :: \<open>variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close>
where
  \<open>step_syntax_list \<equiv> step_pred_bil\<close>

instance .. 
end

instantiation stmt :: step_syntax
begin 

definition
  step_syntax_stmt :: \<open>variables \<Rightarrow> word \<Rightarrow> stmt \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close>
where
  \<open>step_syntax_stmt \<equiv> step_pred_stmt\<close>


instance .. 
end

lemma step_stmt_while_empty_intermediary:
  assumes \<open>\<Delta>,w \<turnstile> stmt::stmt \<leadsto> \<Delta>',w'\<close> and \<open>\<exists>e. stmt = while e []\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding step_syntax_stmt_def
  by (induct rule: step_pred_stmt_step_pred_bil.inducts(1)[of _ _ _ _ _ \<open>\<lambda>_ _ _ _ _. True\<close>], auto)

lemma step_stmt_while_empty:
  assumes \<open>\<Delta>,w \<turnstile> while e [] \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms apply (rule step_stmt_while_empty_intermediary)
  by simp

lemma step_stmt_while_empty':
  assumes \<open>\<Delta>' \<noteq> \<Delta> \<or> w' \<noteq> w\<close>
    shows \<open>\<not>(\<Delta>,w \<turnstile> while e [] \<leadsto> \<Delta>',w')\<close>
  using assms(1) step_stmt_while_empty by blast
(*
lemma step_stmt_while_empty': \<open>\<Delta>\<^sub>1 \<turnstile> e \<leadsto>* true \<Longrightarrow> \<not>(\<Delta>,w \<turnstile> while e [] \<leadsto> \<Delta>,w)\<close>
  apply (rule notI)
  sledgehammer
*)

lemma step_stmt_if_empty:
  assumes \<open>\<Delta>,w \<turnstile> (If e [] []) \<leadsto> \<Delta>',w'\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding step_syntax_stmt_def apply (cases rule: step_pred_stmt.cases)
  by blast+



end
