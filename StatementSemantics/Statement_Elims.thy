theory Statement_Elims
  imports Statement_Syntax
          "../ExpressionSemantics/Expression_Elims"
begin

lemma step_seq_emptyE:
  assumes \<open>\<Delta>,w \<turnstile> Empty \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms using eval_inf_bil.cases step_pred_bil_empty_equiv by fastforce

lemma step_seq_nextE:
  assumes \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>'',w'',Empty\<close>
    shows \<open>\<exists>\<Delta>' w'. \<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w' \<and> \<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>'',w'',Empty\<close>
  using assms apply (auto simp add: SEQ_TOTAL_REC eval_pred_stmt_def)
  apply (cases rule: eval_inf_bil_cases)
  by auto

lemma step_seq_oneE:
  assumes \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 Empty \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w'\<close>
  using assms apply (drule_tac step_seq_nextE)
  apply (elim exE conjE)
  apply (drule step_seq_emptyE)
  by clarify


text \<open>Without a while loop the evaluation becomes a total recursive function\<close>

fun
  stmt_finite :: \<open>stmt \<Rightarrow> bool\<close> and
  bil_finite :: \<open>bil \<Rightarrow> bool\<close>
where
  \<open>stmt_finite (While _ _) = False\<close> |
  \<open>stmt_finite (If e seq\<^sub>1 seq\<^sub>2) = (bil_finite seq\<^sub>1 \<and> bil_finite seq\<^sub>2)\<close> |
  \<open>stmt_finite _ = True\<close> |
  \<open>bil_finite (Stmt s\<^sub>1 seq) = (stmt_finite s\<^sub>1 \<and> bil_finite seq)\<close> |
  \<open>bil_finite Empty = True\<close>
  
  
fun
  eval_stmt :: \<open>variables \<Rightarrow> word \<Rightarrow> stmt \<Rightarrow> (variables \<times> word)\<close> and
  eval_bil :: \<open>variables \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> (variables \<times> word)\<close>
where
  \<open>eval_stmt \<Delta> w (cpuexn _) = (\<Delta>,w)\<close> |
  \<open>eval_stmt \<Delta> w (special[_]) = (\<Delta>,w)\<close> |
  \<open>eval_stmt _ _ (While _ _) = undefined\<close> |
  \<open>eval_stmt \<Delta> w (If e seq\<^sub>1 seq\<^sub>2) = (
    let v = eval_exp \<Delta> e in
      case v of Immediate w' \<Rightarrow> (
        if w' = true then eval_bil \<Delta> w seq\<^sub>1          
        else eval_bil \<Delta> w seq\<^sub>2)
      | Unknown str t \<Rightarrow> (\<Delta>, (undefined \<Colon> (bits w)))
  )\<close> |
  \<open>eval_stmt \<Delta> w (Move var e) = (\<Delta>(var \<mapsto> eval_exp \<Delta> e), w)\<close> |
  \<open>eval_stmt \<Delta> _ (Jmp e) = (
    case (eval_exp \<Delta> e) of Immediate w' \<Rightarrow> (\<Delta>, w')
      | Unknown str imm\<langle>sz\<rangle> \<Rightarrow> (\<Delta>, (undefined \<Colon> sz))
  )\<close> |
  \<open>eval_bil \<Delta> w (Stmt s\<^sub>1 seq) = (
    let (\<Delta>',w') = eval_stmt \<Delta> w s\<^sub>1 in eval_bil \<Delta>' w' seq
  )\<close> |
  \<open>eval_bil \<Delta> w Empty = (\<Delta>,w)\<close>


lemma finite_eval_inf_impiles_eval:
  \<open>eval_inf_stmt \<Delta> w stmt \<Delta>' w' \<Longrightarrow> stmt_finite stmt \<Longrightarrow> (\<Delta>',w') = eval_stmt \<Delta> w stmt\<close>
  \<open>eval_inf_bil \<Delta> w bil \<Delta>' w' \<Longrightarrow> bil_finite bil \<Longrightarrow> (\<Delta>',w') = eval_bil \<Delta> w bil\<close>
  apply (induct rule: eval_inf_stmt_eval_inf_bil.inducts)
  apply (auto simp add: true_val_def false_val_def)
  apply (smt (verit, ccfv_SIG) val.simps(10))
  apply (smt (verit, best) not_true_eq_false val.simps(10))
  apply (metis val.simps(10))
  by (metis case_prod_conv)

lemma step_pred_bil_finite_empty:
  assumes \<open>\<Delta>,w \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>bil_finite bil\<close>
    shows \<open>(\<Delta>',w') = eval_bil \<Delta> w bil\<close>
  using assms finite_eval_inf_impiles_eval(2) step_pred_bil_empty_equiv by auto


(*
fun
  conformant_stmt :: \<open>variables \<Rightarrow> stmt \<Rightarrow> bool\<close> and 
  conformant_bil :: \<open>variables \<Rightarrow> bil \<Rightarrow> bool\<close>
where
  \<open>conformant_stmt \<Delta> (While e seq) = (
    case eval_exp \<Delta> e of Immediate w' \<Rightarrow> (w' = true \<or> w' = false)
      | _ \<Rightarrow> False
  )\<close> |
  \<open>conformant_stmt \<Delta> (If e seq\<^sub>1 seq\<^sub>2) = (
    case eval_exp \<Delta> e of Immediate w' \<Rightarrow> ((w' = true \<or> w' = false) \<and> conformant_bil \<Delta> seq\<^sub>1 \<and> conformant_bil \<Delta> seq\<^sub>2)
      | _ \<Rightarrow> False
  )\<close> |
  \<open>conformant_stmt \<Delta> (Jmp e) = (
    case eval_exp \<Delta> e of Immediate w' \<Rightarrow> True
      | _ \<Rightarrow> False
  )\<close> |
  \<open>conformant_stmt _ _ = True\<close> |
  \<open>conformant_bil \<Delta> (Stmt s\<^sub>1 seq) = (conformant_stmt \<Delta> s\<^sub>1 \<and> conformant_bil \<Delta> seq)\<close> |
  \<open>conformant_bil _ Empty = True\<close>

lemma finite_eval_inf_impiles_eval:
  \<open>conformant_stmt \<Delta> stmt \<Longrightarrow> stmt_finite stmt \<Longrightarrow> (\<Delta>',w') = eval_stmt \<Delta> w stmt \<Longrightarrow> eval_inf_stmt \<Delta> w stmt \<Delta>' w'\<close>
  \<open>conformant_bil \<Delta> bil \<Longrightarrow> bil_finite bil \<Longrightarrow> (\<Delta>',w') = eval_bil \<Delta> w bil \<Longrightarrow> eval_inf_bil \<Delta> w bil \<Delta>' w'\<close>
  apply (induct rule: eval_stmt_eval_bil.induct)
  apply auto
  apply (simp_all add: eval_inf_stmt_eval_inf_bil.intros)
    defer
  apply (case_tac \<open>eval_exp \<Delta> e\<close>, auto)
  apply (simp add: eval_inf_stmt_eval_inf_bil.intros(5))
  sledgehammer
  apply simp

     defer (*unknown*)
  apply simp

    apply (simp add: eval_inf_stmt_eval_inf_bil.intros(8))

       apply (smt (verit, ccfv_SIG) One_nat_def val.simps(10))
  apply (smt (verit, ccfv_SIG) Bitvector_Syntax.word.inject One_nat_def val.simps(10) zero_neq_one)
  apply (metis val.simps(10))
  by (metis case_prod_conv)


*)

end
