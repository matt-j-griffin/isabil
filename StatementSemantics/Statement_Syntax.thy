theory Statement_Syntax
  imports "../ExpressionSemantics/Expression_Syntax"
begin

text \<open>If we include a while loop we must use an inductive predicate as the bil/stmt may not 
      terminate ie: while true {}.\<close> 

inductive
  eval_inf_stmt :: \<open>variables \<Rightarrow> word \<Rightarrow> stmt \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close> and
  eval_inf_bil :: \<open>variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close>
where
  \<open>\<lbrakk>true = eval_exp \<Delta>\<^sub>1 e; eval_inf_bil \<Delta>\<^sub>1 w\<^sub>1 seq \<Delta>\<^sub>2 w\<^sub>2; eval_inf_stmt \<Delta>\<^sub>2 w\<^sub>2 (While e seq) \<Delta>\<^sub>3 w\<^sub>3\<rbrakk> \<Longrightarrow> eval_inf_stmt \<Delta>\<^sub>1 w\<^sub>1 (While e seq) \<Delta>\<^sub>3 w\<^sub>3\<close> |

  \<open>\<lbrakk>false = eval_exp \<Delta> e\<rbrakk> \<Longrightarrow> eval_inf_stmt \<Delta> w (While e seq) \<Delta> w\<close> |
  \<open>\<lbrakk>true = eval_exp \<Delta> e;  eval_inf_bil \<Delta> w seq\<^sub>1 \<Delta>' w'\<rbrakk> \<Longrightarrow> eval_inf_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) \<Delta>' w'\<close> |
  \<open>\<lbrakk>false = eval_exp \<Delta> e; eval_inf_bil \<Delta> w seq\<^sub>2 \<Delta>' w'\<rbrakk> \<Longrightarrow> eval_inf_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) \<Delta>' w'\<close> |
  \<open>\<lbrakk>Immediate w' = eval_exp \<Delta> e\<rbrakk> \<Longrightarrow> eval_inf_stmt \<Delta> w (Jmp e) \<Delta> w'\<close> |
  \<open>eval_inf_stmt \<Delta> w (Move var e) (\<Delta>(var \<mapsto> eval_exp \<Delta> e)) w\<close> |
  \<open>eval_inf_stmt \<Delta> w (CpuExn num) \<Delta> w\<close> |
  \<open>eval_inf_stmt \<Delta> w (Special str) \<Delta> w\<close> |

  \<open>\<lbrakk>eval_inf_stmt \<Delta> w s\<^sub>1 \<Delta>' w'; eval_inf_bil \<Delta>' w' seq \<Delta>'' w''\<rbrakk> \<Longrightarrow> eval_inf_bil \<Delta> w (Stmt s\<^sub>1 seq) \<Delta>'' w''\<close> |
  \<open>eval_inf_bil \<Delta> w Empty \<Delta> w\<close>

lemma eval_inf_stmt_simps:
  assumes "eval_inf_stmt \<Delta> w s \<Delta>' w'"
    shows "((\<exists>num.
     s = CpuExn num \<and> \<Delta>' = \<Delta> \<and> w' = w) \<or>
 (\<exists>str.
     s = Special str \<and> \<Delta>' = \<Delta> \<and> w' = w) \<or>
 (\<exists>v e var.
     s = Move var e \<and>
     \<Delta>' = \<Delta>(var \<mapsto> v) \<and> w' = w \<and> v = eval_exp \<Delta> e) \<or>
 (\<exists>e.
     s = Jmp e \<and>
     \<Delta>' = \<Delta> \<and> w' = w' \<and> Immediate w' = eval_exp \<Delta> e) \<or>
 (\<exists>e seq\<^sub>1 seq\<^sub>2.
     s = stmt.If e seq\<^sub>1 seq\<^sub>2 \<and>
     true = eval_exp \<Delta> e \<and> 
     eval_inf_bil \<Delta> w seq\<^sub>1 \<Delta>' w') \<or>
 (\<exists>e seq\<^sub>2 seq\<^sub>1.
     s = stmt.If e seq\<^sub>1 seq\<^sub>2 \<and>
     false = eval_exp \<Delta> e \<and>
     eval_inf_bil \<Delta> w seq\<^sub>2 \<Delta>' w') \<or>
 (\<exists>e seq \<Delta>\<^sub>2 w\<^sub>2.
     s = While e seq \<and>
     true = eval_exp \<Delta> e \<and>
     eval_inf_bil \<Delta> w seq \<Delta>\<^sub>2 w\<^sub>2 \<and>
     eval_inf_stmt \<Delta>\<^sub>2 w\<^sub>2 (While e seq) \<Delta>' w') \<or>
 (\<exists>e seq.
     s = While e seq \<and>
     \<Delta>' = \<Delta> \<and> w' = w \<and> false = eval_exp \<Delta> e))"
  using assms apply (simp add: eval_inf_stmt.simps[where ?a1.0=\<Delta> and ?a2.0=w and ?a3.0=s and ?a4.0=\<Delta>' and ?a5.0=w'])
  apply (elim exE disjE conjE)
  apply simp_all
  by blast+

lemma eval_inf_stmt_cases[consumes 1]:
  assumes \<open>eval_inf_stmt \<Delta> w s\<^sub>1 \<Delta>' w'\<close>
  obtains
    (CpuExn) num where
      "s\<^sub>1 = CpuExn num"
      "\<Delta>' = \<Delta>"
      "w' = w"
  | (Special) str where
      "s\<^sub>1 = Special str"
      "\<Delta>' = \<Delta>"
      "w' = w"
  | (Move) var e where
      "s\<^sub>1 = Move var e"
      "\<Delta>' = \<Delta>(var \<mapsto> eval_exp \<Delta> e)"
      "w' = w"
  | (Jmp) e where
      "s\<^sub>1 = Jmp e"
      "\<Delta>' = \<Delta>"
      "Immediate w' = eval_exp \<Delta> e"
  | (IfTrue) e seq\<^sub>1 seq\<^sub>2 where
      "s\<^sub>1 = If e seq\<^sub>1 seq\<^sub>2"
      "eval_inf_bil \<Delta> w seq\<^sub>1 \<Delta>' w'"
      "true = eval_exp \<Delta> e"
  | (IfFalse) e seq\<^sub>1 seq\<^sub>2 where
      "s\<^sub>1 = If e seq\<^sub>1 seq\<^sub>2"
      "eval_inf_bil \<Delta> w seq\<^sub>2 \<Delta>' w'"
      "false = eval_exp \<Delta> e"
  | (WhileTrue) e seq \<Delta>\<^sub>2 w\<^sub>2 where
      "s\<^sub>1 = While e seq"
      "eval_inf_bil \<Delta> w seq \<Delta>\<^sub>2 w\<^sub>2"
      "eval_inf_stmt \<Delta>\<^sub>2 w\<^sub>2 (While e seq) \<Delta>' w'"
      "true = eval_exp \<Delta> e"
  | (WhileFalse) e seq where
      "s\<^sub>1 = While e seq"
      "\<Delta>' = \<Delta>"
      "w' = w"
      "false = eval_exp \<Delta> e"
  using assms apply (drule_tac eval_inf_stmt_simps) 
  by auto

lemma eval_inf_bil_simps:
  assumes "eval_inf_bil \<Delta> w bil \<Delta>' w'"
    shows "((\<exists>stmt seq \<Delta>'' w''.
      bil = Stmt stmt seq \<and>
      eval_inf_stmt \<Delta> w stmt \<Delta>'' w'' \<and> 
      eval_inf_bil \<Delta>'' w'' seq \<Delta>' w') \<or>
 (bil = Empty \<and> \<Delta>' = \<Delta> \<and> w' = w))"
  using assms apply (simp add: eval_inf_bil.simps[where ?a1.0=\<Delta> and ?a2.0=w and ?a3.0=bil and ?a4.0=\<Delta>' and ?a5.0=w'])
  by auto

lemma eval_inf_bil_cases[consumes 1]:
  assumes \<open>eval_inf_bil \<Delta> w bil \<Delta>' w'\<close>
  obtains
    (Stmt) stmt seq \<Delta>'' w'' where
      "bil = Stmt stmt seq"
      "eval_inf_stmt \<Delta> w stmt \<Delta>'' w''"
      "eval_inf_bil \<Delta>'' w'' seq \<Delta>' w'"
  | (Empty)
      "bil = Empty"
      "\<Delta>' = \<Delta>"
      "w' = w"
  using assms apply (drule_tac eval_inf_bil_simps) 
  by auto

definition
  step_pred_bil :: \<open>variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> bool\<close> (\<open>_,_ \<turnstile> _ \<leadsto> _,_,_\<close>)
where
  \<open>(\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>',w',seq') = (\<forall>\<Delta>'' w''.
      eval_inf_bil \<Delta>' w' seq' \<Delta>'' w'' \<longrightarrow>
        eval_inf_bil \<Delta> w seq \<Delta>'' w''
  )\<close>

lemma step_pred_bil_empty_equiv: \<open>(\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>',w',Empty) \<longleftrightarrow> eval_inf_bil \<Delta> w seq \<Delta>' w'\<close>
  apply (auto simp add: step_pred_bil_def)  
  apply (simp add: eval_inf_stmt_eval_inf_bil.intros(10))
  using eval_inf_bil_cases by blast

definition
  eval_pred_stmt :: \<open>variables \<Rightarrow> word \<Rightarrow> stmt \<Rightarrow> variables \<Rightarrow> word \<Rightarrow> bool\<close> (\<open>_,_ \<turnstile> _ \<leadsto> _,_\<close>)
where                           
  \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w' = (eval_inf_stmt \<Delta> w s\<^sub>1 \<Delta>' w')\<close>


end
