theory Program_Elims
  imports Program_Model
          "../StatementSemantics/Statement_Elims"
begin

context bil_syntax
begin

lemma step_progE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem')\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and E: \<open>\<lbrakk>\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (rule StepE)
  apply (rule E)
  using assms(2) decode_detE by blast

end

end
