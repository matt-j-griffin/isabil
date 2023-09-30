theory Program_Elims
  imports Program_Model
          "../StatementSemantics/Statement_Elims"
begin

context bil_syntax
begin

lemma step_progE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem')\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
    shows \<open>\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3\<close>
  using assms apply (elim StepE) 
  using decode_deterministic by blast

lemma step_prog_deterministic:
  assumes \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>\<^sub>1, w\<^sub>1, mem\<^sub>1)\<close>
      and \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>\<^sub>2, w\<^sub>2, mem\<^sub>2)\<close>
    shows \<open>(\<Delta>\<^sub>1, w\<^sub>1, mem\<^sub>1) = (\<Delta>\<^sub>2, w\<^sub>2, mem\<^sub>2)\<close>
  using assms by (metis StepE decode_deterministic ext_inject step_bil_deterministic)

end

end
