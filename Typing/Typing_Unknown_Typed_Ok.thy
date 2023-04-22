theory Typing_Unknown_Typed_Ok
  imports Typing_Typed_Ok
          Typing_Context
begin

class unknown_typed_ok = unknown_constructor + typed_ok + 
  assumes T_UNKNOWN: \<open>\<And>\<Gamma> str t. \<lbrakk>t is ok; \<Gamma> is ok\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (unknown[str]: t) :: t\<close>
      and unknown_typed_diff: \<open>\<And>\<Gamma> str t t'. \<Gamma> \<turnstile> (unknown[str]: t') :: t \<Longrightarrow> t' = t\<close>
begin

lemma unknown_imm_typed_diff:
  assumes \<open>\<Gamma> \<turnstile> (unknown[str]: imm\<langle>sz\<rangle>) :: imm\<langle>sz'\<rangle>\<close> 
    shows \<open>sz = sz'\<close>
  using assms by (frule_tac unknown_typed_diff, blast)

lemma unknown_mem_typed_diff:
  assumes \<open>\<Gamma> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r', sz\<^sub>m\<^sub>e\<^sub>m'\<rangle>\<close>
    shows \<open>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<and> sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>m\<^sub>e\<^sub>m'\<close>
  using assms by (frule_tac unknown_typed_diff, blast)

lemma unknown_mem_typed_diff':
  assumes \<open>\<Gamma> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r', sz\<^sub>m\<^sub>e\<^sub>m'\<rangle>\<close>
    shows \<open>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r' = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<and> sz\<^sub>m\<^sub>e\<^sub>m' = sz\<^sub>m\<^sub>e\<^sub>m\<close>
  using assms by (frule_tac unknown_typed_diff, blast)

end

end
