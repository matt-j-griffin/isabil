theory Expressions_Rules
  imports Expression_Rules
begin

inductive
  step_exps :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close> [400, 400, 400] 401)
where
  Reduce: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> |
  Refl: \<open>\<Delta> \<turnstile> e \<leadsto>* e\<close>

inductive_cases ReduceE: \<open>\<Delta> \<turnstile> e \<leadsto>* e'\<close>

text \<open>Improved induction rule for step_exps\<close>

lemma step_exps_induct[consumes 1, case_names Reduce Refl]:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> 
      and \<open>(\<And>e\<^sub>1 e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3 \<Longrightarrow> P e\<^sub>2 \<Longrightarrow> P e\<^sub>1)\<close> 
      and \<open>P e\<^sub>3\<close>
    shows \<open>P e\<^sub>1\<close>
  using assms by (induct \<Delta> e\<^sub>1 e\<^sub>3 rule: step_exps.induct, blast+)

end