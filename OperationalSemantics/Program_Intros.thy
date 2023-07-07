theory Program_Intros
  imports Program_Model
          "../StatementSemantics/Statement_Intros"
begin

context bil_syntax
begin

lemma step_progI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> bil \<leadsto> \<Delta>',w'\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
  unfolding step_pred.simps
  apply (rule exI[of _ w\<^sub>2])
  apply (rule exI[of _ bil])
  apply (intro conjI)
  apply (rule assms(1))  
  by (rule assms(2))

lemma step_prog_noinsnI:
  assumes \<open>(\<Delta>, (num \<Colon> sz), mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l no_insn (num \<Colon> sz)\<close> and \<open>num < 2 ^ sz\<close>
    shows \<open>(\<Delta>, (num \<Colon> sz), mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (num \<Colon> sz), mem)\<close>
  apply (rule step_progI[of _ _ _ \<open>(0 \<Colon> sz)\<close> \<open>[]\<close>])
  subgoal 
    using assms(1) by simp
  subgoal
    unfolding bv_plus.simps apply simp
    using assms(2) by auto
  .

end

end
