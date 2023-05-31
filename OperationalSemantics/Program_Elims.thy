context bil_syntax
begin

lemma step_progI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
  unfolding step_pred.simps
  apply (rule exI[of _ w\<^sub>2])
  apply (rule exI[of _ bil])
  apply (intro conjI)
  apply (rule assms(1))  
  by (rule assms(2))

lemma step_prog_noinsnI:
  assumes \<open>(\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l no_insn w\<close> and \<open>w is ok\<close>
    shows \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w, mem)\<close>
proof (cases w rule: word_exhaust)
  case (1 num sz)
  thus ?thesis
    apply clarify
    apply (rule step_progI[of _ _ _ \<open>(0 \<Colon> sz)\<close> Empty])
    subgoal 
      using assms(1) by simp
    subgoal
      unfolding bv_plus.simps apply simp
      using assms(2) apply auto
      by (rule SEQ_NIL)
    .
qed

lemma step_progE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem')\<close>
    shows \<open>(\<exists>w\<^sub>2 bil. (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> \<and> (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty))\<close>
proof (cases \<open>mem = mem'\<close>)
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  then show ?thesis 
    using assms bil_syntax.step_pred.simps(2) by auto
qed

end