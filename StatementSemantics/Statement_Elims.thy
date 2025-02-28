theory Statement_Elims
  imports Statement_Syntax "../ExpressionSemantics/Expressions_Elims"
begin                  

subsection \<open>Sequences\<close>

lemmas step_bil_emptyE = EmptyE[unfolded step_syntax_list_def[symmetric]]
lemmas step_bil_seqE = NextE[unfolded step_syntax_list_def[symmetric] step_syntax_stmt_def[symmetric]]

lemma step_bil_singleE: 
    fixes s :: stmt
  assumes minor: \<open>\<Delta>,w \<turnstile> [s] \<leadsto> \<Delta>',w'\<close>
      and major: \<open>\<Delta>,w \<turnstile> s \<leadsto> \<Delta>',w' \<Longrightarrow> P\<close> 
    shows P
  using minor apply (rule step_bil_seqE)
  apply (erule step_bil_emptyE)
  apply (rule major)
  by clarify

subsection \<open>Statements\<close>

lemmas step_stmt_specialE = SpecialE[unfolded step_syntax_stmt_def[symmetric]]
lemmas step_stmt_cpuexnE = CpuExnE[unfolded step_syntax_stmt_def[symmetric]]
lemmas step_stmt_moveE = MoveE[unfolded step_syntax_stmt_def[symmetric]]

(*
interpretation exp_val_syntax \<open>\<lambda>e' v'. 
  (\<And>\<Delta> w var e \<Delta>' w' P. \<lbrakk>
      \<Delta>,w \<turnstile> var := e \<leadsto> \<Delta>',w'; 
      (\<And>v. \<lbrakk>\<Delta>' = \<Delta>(var \<mapsto> v'); w' = w; \<Delta> \<turnstile> e \<leadsto>* e'\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
*)

lemmas step_stmt_jmpE = JmpE[unfolded step_syntax_stmt_def[symmetric]]

subsubsection \<open>If\<close>

lemma step_stmt_if_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> (If e [] []) \<leadsto> \<Delta>',w'\<close>
      and E: \<open>\<lbrakk>\<Delta>' = \<Delta>; w' = w\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using E assms(1) step_stmt_if_empty by blast

lemmas step_stmt_ifE = IfE[unfolded step_syntax_stmt_def[symmetric] step_syntax_list_def[symmetric]]

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

subsubsection \<open>While\<close>

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

subsection \<open>Symbolic Execution\<close>

method solve_bilE_scaffold methods recurs solve_exps uses add = (
  (erule step_stmt_cpuexnE step_stmt_specialE step_stmt_if_emptyE) |

  (erule step_stmt_moveE, solve_exps?) |

  (erule step_stmt_jmpE, solve_exps?) |

  (erule step_stmt_if_emptyE, clarify) |
  (erule step_stmt_if_thenE; solve_expsE?, recurs?) |
  (erule step_stmt_if_elseE; solve_expsE?, prefer_last, recurs?) |
  (erule step_stmt_ifE; solve_expsE?, recurs?) |

  (erule step_stmt_while_emptyE, solve_exps) |

  (erule step_stmt_while_emptyE) |
  (erule step_stmt_whileE) |

  erule step_bil_emptyE | 

  (erule step_bil_singleE, recurs?) | 
  (erule step_bil_seqE, recurs?, (recurs)?)
)

method solve_bilE uses add = (
  solve_bilE_scaffold \<open>solve_bilE add: add\<close> \<open>solve_expsE add: add\<close> add: add
)

end
