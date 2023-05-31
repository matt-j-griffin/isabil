theory Typing_Word_Typed_Ok
  imports Typing_Typed_Ok
          Typing_Word
          Typing_Context
begin

class word_typed_ok = word_is_ok + typed_ok +
  assumes word_typed_def: \<open>\<And>\<Gamma> num sz. (\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz\<rangle>) \<longleftrightarrow> \<Gamma> is ok \<and> (num \<Colon> sz) is ok\<close>
      and word_typed_diff: \<open>\<And>\<Gamma> num sz sz'. \<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz'\<rangle> \<Longrightarrow> sz = sz'\<close>
      and word_not_mem: \<open>\<And>\<Gamma> num sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<not>(\<Gamma> \<turnstile> (num \<Colon> sz) :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)\<close>
begin


lemma word_typed_okI:
  assumes \<open>\<Gamma> is ok\<close> and \<open>(num \<Colon> sz) is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  using assms unfolding word_typed_def by blast

lemma word_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> is ok \<and> (num \<Colon> sz) is ok\<close>
  using assms unfolding word_typed_def by blast

lemma bv_uminus_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> num \<Colon> sz :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> -\<^sub>b\<^sub>v (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  using assms unfolding bv_uminus.simps by auto

lemma bv_negation_typed_okI:
  assumes \<open>\<Gamma> is ok\<close> and \<open>0 < sz\<close>
    shows \<open>\<Gamma> \<turnstile> ~\<^sub>b\<^sub>v (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  unfolding bv_negation.simps using assms(1) apply (rule word_typed_okI) 
  using assms(2) apply (rule TWF_WORD)
  by simp

lemma bool_word_is_ok_exhaust:
  assumes \<open>\<Gamma> \<turnstile> w :: imm\<langle>1\<rangle>\<close>
  obtains 
    (True) \<open>w = true\<close>
  | (False) \<open>w = false\<close>
  | (NotWord) \<open>\<forall>nat sz. w \<noteq> (nat \<Colon> sz)\<close>
  using assms apply (rule_tac word_syntax_exhaust[of w])
  subgoal for nat sz
    apply clarify
    apply (frule word_typed_diff, clarify)
    apply (frule word_typed_okE)
    apply (rule bool_is_ok_exhaust)
    by blast+
  by simp

lemma concat_word_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> num\<^sub>1 \<Colon> sz\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> num\<^sub>2 \<Colon> sz\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  apply (insert assms) 
  apply (drule word_typed_okE)+
  apply (elim conjE)
  unfolding bv_concat.simps apply (rule word_typed_okI)
  subgoal by blast
  subgoal
    unfolding bv_concat.simps[symmetric] by (rule concat_word_is_okI)
  .

lemmas T_INT = word_typed_okI
end

instantiation word :: word_typed_ok
begin                      

function
  is_ok_word :: \<open>word \<Rightarrow> bool\<close>
where 
  \<open>is_ok_word (num \<Colon> sz) = (0 < sz \<and> num < 2 ^ sz)\<close>
  subgoal for P x
    by (rule word_exhaust[of x], blast)
  by simp 
termination by (standard, auto)

function 
  typed_ok_word :: \<open>TypingContext \<Rightarrow> word \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typed_ok_word \<Gamma> (num \<Colon> sz) imm\<langle>sz\<rangle> = (((num \<Colon> sz)::word) is ok \<and> \<Gamma> is ok)\<close> |
  \<open>\<lbrakk>sz \<noteq> sz'\<rbrakk> \<Longrightarrow> typed_ok_word _ (_ \<Colon> sz) imm\<langle>sz'\<rangle> = False\<close> |
  \<open>typed_ok_word _ _ mem\<langle>_, _\<rangle> = False\<close>
  apply auto
  subgoal for P w t
    apply (rule Type.exhaust[of t], simp)
    subgoal for sz'
      apply (cases w rule: word_exhaust)
      by auto
    by auto
  .
termination by (standard, auto)

instance 
  apply (standard, auto)
  subgoal
    by (metis is_ok_Type.simps(1) is_ok_word.simps typed_ok_word.elims(2))
  using typed_ok_word.simps(2) by blast


method solve_T_WORD = (
  rule T_INT, solve_TG, rule TWF_WORD, linarith, fastforce
)

end

end
