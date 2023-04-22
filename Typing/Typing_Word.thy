theory Typing_Word
  imports "../Bitvector_Instance" 
          Typing_Syntax
begin         

subsection \<open>(num \<Colon> sz) is ok\<close>
                                    
class word_is_ok = is_ok + word_constructor +
  assumes word_is_ok_def: \<open>\<And>num sz. (num \<Colon> sz) is ok \<longleftrightarrow> sz > 0 \<and> num < 2 ^ sz\<close>
begin

lemma word_is_okI: 
  assumes \<open>sz > 0\<close> and \<open>num < 2 ^ sz\<close>
    shows \<open>(num \<Colon> sz) is ok\<close>
  using assms unfolding word_is_ok_def by blast

lemma word_is_okE: 
  assumes \<open>(num \<Colon> sz) is ok\<close>
    shows \<open>sz > 0 \<and> num < 2 ^ sz\<close>
  using assms unfolding word_is_ok_def by blast

lemma bv_plus_ok: 
  assumes \<open>0 < sz\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  unfolding bv_plus.simps using assms apply (rule word_is_okI)
  by simp

lemma bv_minus_ok: 
  assumes \<open>0 < sz\<close> and \<open>num\<^sub>1 < 2 ^ sz\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  using assms apply (cases \<open>num\<^sub>2 \<le> num\<^sub>1\<close>)
  subgoal
    unfolding bv_minus.simps using assms(1) apply (rule word_is_okI)
    using assms(2) by simp
  subgoal
    apply (drule not_le_imp_less)
    unfolding bv_minus.simps using assms(1) apply (rule word_is_okI)
    by simp
  .

lemma bool_is_ok_exhaust: 
  assumes \<open>(num \<Colon> 1) is ok\<close>
  obtains 
    (True) \<open>(num \<Colon> 1) = true\<close> 
  | (False) \<open>(num \<Colon> 1) = false\<close>
  using assms apply (rule_tac word_syntax_exhaust[of \<open>(num \<Colon> 1)\<close>])
  apply (drule word_is_okE[of num 1])
  unfolding false_word true_word apply auto    
  by fastforce

lemma bv_times_ok:
  assumes \<open>0 < sz\<close>                       
    shows \<open>((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  unfolding bv_times.simps using assms apply (rule word_is_okI) 
  by simp

lemma bv_divide_ok:
  assumes \<open>0 < sz\<close> and \<open>num\<^sub>1 < 2 ^ sz\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  unfolding bv_divide.simps using assms(1) apply (rule word_is_okI)
  using assms(2) div_le_dividend le_trans verit_comp_simplify1(3)
  by (meson)

\<comment> \<open>BIL formalisation lemma\<close>

lemmas TWF_WORD = word_is_okI

end

end
