theory Program_Intros
  imports Program_Model
          "../StatementSemantics/Statement_Intros"
begin

context bil_syntax
begin

lemmas step_progI = Step

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
