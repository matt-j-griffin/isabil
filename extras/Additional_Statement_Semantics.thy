
section \<open>Additional Statement Semantics\<close>

text \<open>Additional big step semantics for statements, designed to reduce the proof burden. 
      This theory is in development and subject to change.\<close>

theory Additional_Statement_Semantics
  imports "../StatementSemantics/Statement_Intros"
          Additional_Expression_Semantics
begin

no_notation HOL.Not (\<open>~ _\<close> [40] 40)
no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)


declare eval_exps_pred_exp.simps[simp del]
declare xtract.simps[simp del]
declare step_pred_exp.simps[simp del]
lemma MOVE_AUX:
  \<open>\<Delta> \<turnstile> e \<leadsto>* v \<Longrightarrow> w' = w \<Longrightarrow> \<Delta>' = \<Delta>(var \<mapsto> v) \<Longrightarrow>
  \<Delta>,w \<turnstile> var := e \<leadsto> \<Delta>',w'\<close>
  using MOVE by simp

lemma stmt_ifI:
  assumes \<open>((\<Delta> \<turnstile> e \<leadsto>* true) \<and> (\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w',Empty)) \<or> ((\<Delta> \<turnstile> e \<leadsto>* false) \<and> (\<Delta>,w \<turnstile> seq\<^sub>2 \<leadsto> \<Delta>',w',Empty))\<close>
    shows \<open>\<Delta>,w \<turnstile> (If e seq\<^sub>1 seq\<^sub>2) \<leadsto> \<Delta>',w'\<close>
  using assms apply (elim disjE conjE)
  subgoal by (rule IF_TRUE)
  subgoal by (rule IF_FALSE)
  .

lemma stmt_if_thenI:
  assumes \<open>((\<Delta> \<turnstile> e \<leadsto>* true) \<and> (\<Delta>,w \<turnstile> seq\<^sub>1 \<leadsto> \<Delta>',w',Empty)) \<or> (\<Delta> \<turnstile> e \<leadsto>* false \<and> \<Delta>' = \<Delta> \<and> w' = w)\<close>
    shows \<open>\<Delta>,w \<turnstile> (IfThen e seq\<^sub>1) \<leadsto> \<Delta>',w'\<close>
  using assms apply (elim disjE conjE)
  subgoal by (rule IF_TRUE)
  subgoal by (clarify, rule IFTHEN_FALSE)
  .


method solve_stmt = (
  match conclusion in
    \<comment> \<open>Move\<close>
    \<open>_,_ \<turnstile> (_ := _) \<leadsto> (_(_ \<mapsto> _)),_\<close> \<Rightarrow> \<open>rule MOVE, solve_exps\<close>
  \<bar> \<open>_,_ \<turnstile> (_ := _) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule MOVE_AUX, solve_exps\<close>

    \<comment> \<open>Jmp\<close>
  \<bar> \<open>_,_ \<turnstile> (jmp _) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule JMP, solve_exps\<close>

    \<comment> \<open>If - disjunct, hand over to caller to solve\<close>
  \<bar> \<open>_,_ \<turnstile> (IfThen _ _) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule stmt_if_thenI\<close>
  \<bar> \<open>_,_ \<turnstile> (If _ _ _ ) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule stmt_ifI\<close>

  \<bar> _ \<Rightarrow> \<open>succeed\<close>
(* Attempt to fix any unfixed vars *)
  ; fastforce?
)

method solve_bil = (
  match conclusion in
    \<comment> \<open>Reducible values\<close>
    \<open>_,_ \<turnstile> Empty \<leadsto> _,_,Empty\<close> \<Rightarrow> \<open>rule SEQ_NIL\<close>           
  \<bar> \<open>_,_ \<turnstile> Stmt _ Empty \<leadsto> _,_,Empty\<close> \<Rightarrow> \<open>rule SEQ_ONE; solve_stmt\<close>
  \<bar> \<open>_,_ \<turnstile> Stmt _ _ \<leadsto> _,_,Empty\<close> \<Rightarrow> \<open>rule SEQ_NEXT, solve_stmt, solve_bil\<close>

  \<bar> _ \<Rightarrow> \<open>succeed\<close>
)

end
