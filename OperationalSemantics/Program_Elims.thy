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
proof (cases \<open>mem = mem'\<close>)
  case True
  then show ?thesis 
    using assms apply auto 
    using decode_deterministic by blast
next
  case False
  then show ?thesis 
    using assms bil_syntax.step_pred.simps(2) by auto
qed

lemma step_prog_deterministic:
  assumes \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>\<^sub>1, w\<^sub>1, mem\<^sub>1)\<close>
      and \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>\<^sub>2, w\<^sub>2, mem\<^sub>2)\<close>
    shows \<open>(\<Delta>\<^sub>1, w\<^sub>1, mem\<^sub>1) = (\<Delta>\<^sub>2, w\<^sub>2, mem\<^sub>2)\<close>
using assms(1) proof (cases \<open>mem = mem\<^sub>1\<close>)
  case mem1: True
  show ?thesis 
  using assms(2) proof (cases \<open>mem = mem\<^sub>2\<close>)
    case True
    then show ?thesis 
      using assms using mem1 apply simp
      apply (elim exE conjE)
      apply (drule decode_deterministic, blast)
      apply simp
      by (rule step_bil_deterministic)
  qed auto
qed auto


end

end
