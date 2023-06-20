
section \<open>Additional Program Semantics\<close>

text \<open>Additional big step semantics for programs, designed to reduce the proof burden. 
      This theory is in development and subject to change.\<close>

theory Additional_Program_Semantics
  imports "../BIL_Parse"
          "../OperationalSemantics/Program_Intros"
          Additional_Statement_Semantics
begin

no_notation HOL.Not (\<open>~ _\<close> [40] 40)
no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)


declare eval_exps_pred_exp.simps[simp del]
declare step_pred_exp.simps[simp del]

lemma bv_plus_less: \<open>a + b < 2 ^ sz \<Longrightarrow> (a \<Colon> sz) +\<^sub>b\<^sub>v (b \<Colon> sz) = (a + b \<Colon> sz)\<close>
  unfolding bv_plus.simps by simp

text \<open>Attempt to solve a program step\<close>

context bil_syntax
begin

method solve_prog uses decoder = (
    rule step_progI, 

 \<comment> \<open>Unfold make definition to a conventional record - this is an issue with Isabelle/ML and
     constructing record types\<close>
    unfold insn.make_def[symmetric],
    rule decoder,

 \<comment> \<open>Attempt to tidy any syntax mess left by the parser\<close>
    (unfold syntax_simps)?,
    solve_bil
)

end

end
