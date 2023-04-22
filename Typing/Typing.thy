theory Typing
  imports Typing_BIL_Is_Ok
begin


lemma set_not_\<Gamma>_is_ok:
    fixes \<Gamma> :: TypingContext
  assumes \<open>(x :\<^sub>t sz\<^sub>1) \<in> set \<Gamma>\<close>
      and \<open>(x :\<^sub>t sz\<^sub>2) \<in> set \<Gamma>\<close>
      and \<open>sz\<^sub>1 \<noteq> sz\<^sub>2\<close>
    shows \<open>\<not>(\<Gamma> is ok)\<close>
  using assms apply (induct \<Gamma>, auto)
  unfolding dom\<^sub>\<Gamma>_def 
  apply (drule_tac f=name and A=\<open>set \<Gamma>'\<close> in imageI)
  using var_constructor_var_def apply force
  apply (drule_tac f=name and A=\<open>set \<Gamma>'\<close> in imageI)
  using var_constructor_var_def apply force
  using is_ok_list.elims(2) by auto




(* COMMON *)

lemma T_CAST_WIDEN_NARROW: 
  assumes \<open>0 < sz\<^sub>n\<^sub>a\<^sub>r\<^sub>r\<^sub>o\<^sub>w\<close> and \<open>sz\<^sub>n\<^sub>a\<^sub>r\<^sub>r\<^sub>o\<^sub>w \<le> sz\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<close> and \<open>sz\<^sub>n\<^sub>a\<^sub>r\<^sub>r\<^sub>o\<^sub>w \<le> sz\<close> and \<open>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>\<close>
      and \<open>widen = extend \<or> widen = pad\<close> and \<open>narrow = high \<or> narrow = low\<close>
    shows \<open>\<Gamma> \<turnstile> widen:sz\<^sub>w\<^sub>i\<^sub>d\<^sub>e[narrow:sz\<^sub>n\<^sub>a\<^sub>r\<^sub>r\<^sub>o\<^sub>w[e]] :: imm\<langle>sz\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<rangle>\<close>
  apply (rule T_CAST_WIDEN[of _ sz\<^sub>n\<^sub>a\<^sub>r\<^sub>r\<^sub>o\<^sub>w])
  using assms apply simp
  using assms apply presburger
  subgoal
    apply (rule T_CAST_NARROW[of _ sz])
    using assms by presburger+
  by (rule assms(5))

end
