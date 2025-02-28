theory Program_Elims
  imports Program_Model
          "../StatementSemantics/Statement_Elims"
begin

context bil_syntax
begin

lemma step_progE:
  assumes major: \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem')\<close>
      and caveat: \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
  obtains (StepProg) \<open>\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3\<close> \<open>mem' = mem\<close>
using major proof (rule StepE)
  fix w\<^sub>2' :: word
    and bila :: "stmt list"
  assume "mem' = mem"
    and "(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr>addr = w\<^sub>1, size = w\<^sub>2', code = bila\<rparr>"
    and "\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2' \<turnstile> bila \<leadsto> \<Delta>',w\<^sub>3"
  thus thesis
    using StepProg
    using decode_detE[OF caveat] by blast
qed

method solve_progE_scaffold methods solve_bil uses decoder = (
  (erule step_progE, rule decoder, solve_bil)
)

method solve_progE uses add decoder = (
  solve_progE_scaffold \<open>solve_bilE add: add\<close> decoder: decoder
)

end

end
