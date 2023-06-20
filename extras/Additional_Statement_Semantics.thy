
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
declare step_pred_exp.simps[simp del]

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


(* Can't use match conclusion as it will not instantiate schematic variables *)
method solve_stmt = (
  (rule MOVE, solve_exps) |
  (rule JMP, solve_exps) |
  (rule CPUEXN) |
  (rule SPECIAL) |
  match conclusion in
    \<comment> \<open>If - disjunct, hand over to caller to solve\<close>
    \<open>_,_ \<turnstile> (IfThen _ _) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule stmt_if_thenI\<close>
  \<bar> \<open>_,_ \<turnstile> (If _ _ _ ) \<leadsto> _,_\<close> \<Rightarrow> \<open>rule stmt_ifI\<close>

  \<bar> _ \<Rightarrow> \<open>succeed\<close>
)

method solve_bil = (
  rule SEQ_NIL | 
  (rule SEQ_ONE, solve_stmt) | 
  (rule step_bil_nextI[rotated, rotated], rule bil.distinct(2), solve_stmt, solve_bil?)
)

end
