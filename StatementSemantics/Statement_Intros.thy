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
  by (standard, rule step_stmt_jmpI)


lemmas step_stmt_moveI = Move[unfolded step_syntax_stmt_def[symmetric]]
interpretation step_stmt_moveI: exp_val_syntax \<open>\<lambda>e' v. (\<And>\<Delta> e w var. \<Delta> \<turnstile> e \<leadsto>* e' \<Longrightarrow> \<Delta>,w \<turnstile> (var := e) \<leadsto> (\<Delta>(var \<mapsto> v)),w)\<close>
  by (standard, rule step_stmt_moveI)

lemmas step_stmt_cpuexnI = CpuExn[unfolded step_syntax_stmt_def[symmetric]]
lemmas step_stmt_specialI = Special[unfolded step_syntax_stmt_def[symmetric]]






(* TODO 

lemma stmt_ifI:
  assumes \<open>((\<Delta> \<turnstile> e \<leadsto>* true) \<and> (\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w')) \<or> ((\<Delta> \<turnstile> e \<leadsto>* false) \<and> (\<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w'))\<close>
    shows \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
  using assms apply (elim disjE conjE)
  subgoal by (rule step_stmt_if_trueI)
  subgoal by (rule step_stmt_if_falseI)
  .

lemma stmt_if_thenI:
  assumes \<open>((\<Delta> \<turnstile> e \<leadsto>* true) \<and> (\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w')) \<or> (\<Delta> \<turnstile> e \<leadsto>* false \<and> \<Delta>' = \<Delta> \<and> w' = w)\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>',w'\<close>
  using assms apply (elim disjE conjE)
  subgoal by (rule IF_TRUE)
  subgoal by (clarify, rule IFTHEN_FALSE)
  .
*)
(* TODO *)
(*
method solve_stmtI = (
  (intro step_stmt_cpuexnI step_stmt_specialI) |

  (rule step_stmt_moveI.bv_plus, solve_expsI) |
  (rule step_stmt_moveI.storage, solve_expsI) |
  (rule step_stmt_moveI.unknown, solve_expsI) |
  (rule step_stmt_moveI.succ, solve_expsI) |
  (rule step_stmt_moveI.succ2, solve_expsI) |
  (rule step_stmt_moveI.succ3, solve_expsI) |
  (rule step_stmt_moveI.succ4, solve_expsI) |
  (rule step_stmt_moveI.succ5, solve_expsI) |
  (rule step_stmt_moveI.succ6, solve_expsI) |
  (rule step_stmt_moveI.succ7, solve_expsI) |
  (rule step_stmt_moveI.xtract2, solve_expsI) |
  (rule step_stmt_moveI.xtract, solve_expsI) |
  (rule step_stmt_moveI.false, solve_expsI) |
  (rule step_stmt_moveI.true, solve_expsI) |
  (rule step_stmt_moveI.word, solve_expsI) |
  (rule step_stmt_moveI, (solve_expsI | succeed)) |

  (rule step_stmt_jmpI, (solve_expsI | succeed)) |

  \<comment> \<open>More complicated - requires a choice\<close>
  (rule step_stmt_if_then_falseI, solve_expsI) |
  (rule step_stmt_if_else_trueI, solve_expsI) |

  (rule step_stmt_if_trueI, solve_expsI, (solve_stmtI | succeed)) |
  (rule step_stmt_if_falseI, solve_expsI, (solve_stmtI | succeed)) |

  (rule step_stmt_while_falseI, solve_expsI) |

  \<comment> \<open>Even more complicated - need mutually recursive solve method\<close>
  (rule step_stmt_whileI, solve_expsI, (solve_stmtI | succeed))
)

subsection \<open>Eisbach Sequences\<close>

method solve_bilI = (
  rule step_bil_emptyI | 
  (rule step_bil_singleI, (solve_stmtI | succeed)) | 
  (rule step_bil_seqI, (solve_stmtI | succeed), (solve_bilI | succeed))
)
*)

method solve_bil_intI methods m uses simp = (
  ((unfold simp)?), (
  m |
  (intro step_stmt_cpuexnI step_stmt_specialI) |

  \<comment> \<open>Specific states may be irrecoverable so fail these\<close>
  (rule step_stmt_moveI.bv_leq, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.bv_plus, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.storage, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.unknown, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ2, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ3, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ4, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ5, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ6, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.succ7, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.xtract2, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.xtract, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.false, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.true, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI.word, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_moveI, (solve_exps_intI m simp: simp | succeed)) |

  \<comment> \<open>Specific states may be irrecoverable so fail these\<close>
  (rule step_stmt_jmpI.bv_leq, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.bv_plus, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ2, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ3, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ4, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ5, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ6, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.succ7, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.xtract2, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.xtract, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.false, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.true, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI.word, (solve_exps_intI m simp: simp; fail)) |
  (rule step_stmt_jmpI, (solve_exps_intI m simp: simp | succeed)) |

  \<comment> \<open>More complicated - requires a choice\<close>
  (rule step_stmt_if_then_falseI, solve_exps_intI m simp: simp) |
  (rule step_stmt_if_else_trueI, solve_exps_intI m simp: simp) |

  (rule step_stmt_if_trueI, solve_exps_intI m simp: simp, (solve_bil_intI m simp: simp | succeed)) |
  (rule step_stmt_if_falseI, solve_exps_intI m simp: simp, (solve_bil_intI m simp: simp | succeed)) |

  (rule step_stmt_while_falseI, solve_exps_intI m simp: simp) |

  \<comment> \<open>Even more complicated - need mutually recursive solve method\<close>
  (rule step_stmt_whileI, solve_exps_intI m simp: simp, (solve_bil_intI m simp: simp | succeed)) |

  rule step_bil_emptyI | 
  (rule step_bil_empty_eqI; (simp; fail)) |

  (rule step_bil_singleI, (solve_bil_intI m simp: simp | succeed)) | 
  (rule step_bil_seqI, (solve_bil_intI m simp: simp | succeed), (solve_bil_intI m simp: simp | succeed))
)
)

method solve_bilI = solve_bil_intI assumption



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
