theory Statement_Intros
  imports Statement_Syntax
          "../ExpressionSemantics/Expressions_Intros"
begin

subsection \<open>Sequences\<close>

lemmas step_bil_emptyI[simp] = Empty[unfolded step_syntax_list_def[symmetric]]

lemma step_bil_empty_eqI[intro!]: assumes \<open>\<Delta>' = \<Delta>\<close> and \<open>w' = w\<close> shows \<open>\<Delta>,w \<turnstile> ([]::bil) \<leadsto> \<Delta>',w'\<close>
  unfolding assms by (rule step_bil_emptyI)

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


subsection \<open>Statements\<close>

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

lemma step_stmt_if_else_trueI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>,w \<turnstile> (If e [] seq\<^sub>2) \<leadsto> \<Delta>, w\<close>
  using assms apply (rule step_stmt_if_trueI)
  by (rule step_bil_emptyI)

lemma step_stmt_if_then_falseI:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>, w\<close>
  using assms apply (rule step_stmt_if_falseI)
  by (rule step_bil_emptyI)


lemma step_stmt_if_emptyI: \<open>\<Delta>,w \<turnstile> (If e [] []) \<leadsto> \<Delta>,w\<close> (* TODO *)
  apply (cases \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>)
  subgoal by (intro step_stmt_if_else_trueI)
  apply (cases \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>)
  subgoal by (intro step_stmt_if_then_falseI)
  subgoal oops


lemmas step_stmt_jmpI = Jmp[unfolded step_syntax_stmt_def[symmetric]]
interpretation step_stmt_jmpI: exp_val_word_sz_syntax \<open>\<lambda>e' _ w' _. (\<And>\<Delta> e w. (\<Delta> \<turnstile> e \<leadsto>* e') \<Longrightarrow> (\<Delta>,w \<turnstile> jmp e \<leadsto> \<Delta>,w'))\<close>
  apply standard
  using step_stmt_jmpI by blast

lemma step_stmt_jmpI':
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (num \<Colon> sz)\<close> and \<Delta>': \<open>\<Delta>' = \<Delta>\<close>
    shows \<open>\<Delta>,w \<turnstile> jmp e \<leadsto> \<Delta>',(num \<Colon> sz)\<close>
  unfolding \<Delta>' using assms(1) by (rule step_stmt_jmpI)

interpretation step_stmt_jmpI': exp_val_word_sz_syntax \<open>\<lambda>e' _ w' _. (\<And>\<Delta> \<Delta>' e w. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* e'; \<Delta>' = \<Delta>\<rbrakk> \<Longrightarrow> (\<Delta>,w \<turnstile> jmp e \<leadsto> \<Delta>',w'))\<close>
  apply standard
  using step_stmt_jmpI' by blast

lemmas step_stmt_moveI = Move[unfolded step_syntax_stmt_def[symmetric]]
interpretation step_stmt_moveI: exp_val_syntax \<open>\<lambda>e' v. (\<And>\<Delta> e w var. \<Delta> \<turnstile> e \<leadsto>* e' \<Longrightarrow> \<Delta>,w \<turnstile> (var := e) \<leadsto> (\<Delta>(var \<mapsto> v)),w)\<close>
  apply standard
  using step_stmt_moveI by blast

(*
lemma step_stmt_moveI': 
  assumes step: \<open>\<Delta> \<turnstile> e \<leadsto>* Val v'\<close> and v': \<open>v' = v\<close>
    shows \<open>\<Delta>,w \<turnstile> var := e \<leadsto> \<Delta>(var \<mapsto> v),w\<close>
  by (intro step_stmt_moveI step[unfolded v'])

interpretation step_stmt_moveI': exp2_val_syntax \<open>\<lambda>e\<^sub>1 _ v\<^sub>1 v\<^sub>2. (\<And>\<Delta> e w var. \<lbrakk>\<Delta> \<turnstile> e \<leadsto>* e\<^sub>1; v\<^sub>1 = v\<^sub>2\<rbrakk> \<Longrightarrow> \<Delta>,w \<turnstile> (var := e) \<leadsto> (\<Delta>(var \<mapsto> v\<^sub>2)),w)\<close>
  by (standard, rule step_stmt_moveI')
*)

lemmas step_stmt_cpuexnI = CpuExn[unfolded step_syntax_stmt_def[symmetric]]
lemmas step_stmt_specialI = Special[unfolded step_syntax_stmt_def[symmetric]]

method solve_bilI_scaffold methods recurs solve_exps uses add = (
  (rule step_stmt_cpuexnI step_stmt_specialI) |

  \<comment> \<open>Specific states may be irrecoverable so fail these\<close>
  (rule step_stmt_moveI.leq, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.lt, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.minus, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.lor, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.land, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.lsl, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.lsr, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.plus, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.storage, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.unknown, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.xtract2_plus, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.xtract2, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.xtract, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.false, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.true, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.word, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI, (solve_exps | succeed)) |

  \<comment> \<open>Specific states may be irrecoverable so fail these\<close>
  (rule step_stmt_jmpI.plus, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.xtract2, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.xtract, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.word, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI'.word, solves \<open>solve_exps\<close>, (unfold add, rule refl)) |
  (rule step_stmt_jmpI, (solve_exps | succeed)) |

  \<comment> \<open>More complicated - requires a choice\<close>
  (rule step_stmt_if_then_falseI, solve_exps) |
  (rule step_stmt_if_else_trueI, solve_exps) |

  (rule step_stmt_if_trueI, solve_exps, (recurs | succeed)) |
  (rule step_stmt_if_falseI, solve_exps, (recurs | succeed)) |

  (rule step_stmt_while_falseI, solve_exps) |

  \<comment> \<open>Even more complicated - need mutually recursive solve method\<close>
  (rule step_stmt_whileI, solve_exps, (recurs | succeed)) |

  rule step_bil_emptyI | 
  (rule step_bil_empty_eqI; (simp (no_asm) only: add; fail)) |

  (rule step_bil_singleI, (recurs | succeed)) | 
  (rule step_bil_seqI, (recurs | succeed), (recurs | succeed))
)

(*  (rule step_stmt_moveI.succ2, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ3, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ4, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ5, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ6, solves \<open>solve_exps\<close>) |
  (rule step_stmt_moveI.succ7, solves \<open>solve_exps\<close>) |*)
(*  (rule step_stmt_jmpI.succ2, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ3, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ4, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ5, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ6, solves \<open>solve_exps\<close>) |
  (rule step_stmt_jmpI.succ7, solves \<open>solve_exps\<close>) |*)

method solve_bilI uses add = (
  solve_bilI_scaffold \<open>solve_bilI add: add\<close> \<open>solve_expsI add: add\<close> add: add
)



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
