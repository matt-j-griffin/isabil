theory Statement_Semantics
  imports Expression_Semantics "Typing/Typing"
begin

type_synonym reduction_state = \<open>(variables \<times> word)\<close>

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

thm eval_inf_bil.simps
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



lemma SEQ_NEXT_REV:
  assumes \<open>\<Delta>,w \<turnstile> Stmt s\<^sub>1 seq \<leadsto> \<Delta>'',w'',Empty\<close>
    shows \<open>\<exists>\<Delta>' w'. \<Delta>,w \<turnstile> s\<^sub>1 \<leadsto> \<Delta>',w' \<and> \<Delta>',w' \<turnstile> seq \<leadsto> \<Delta>'',w'',Empty\<close>
  using assms apply (auto simp add: SEQ_TOTAL_REC eval_pred_stmt_def)
  apply (cases rule: eval_inf_bil_cases)
  by auto


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

lemma IFTHEN_TRUE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
      and \<open>\<Delta>,w \<turnstile> seq \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq) \<leadsto> \<Delta>',w'\<close>
  using assms by (rule IF_TRUE)

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
