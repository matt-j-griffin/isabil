theory Expressions_Rules
  imports Expression_Rules
begin

thm rtranclp_def

definition
  step_exps :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close> [400, 400, 400] 401)
where
  \<open>step_exps \<Delta> \<equiv> (step_exp \<Delta>)\<^sup>*\<^sup>*\<close>

lemma rtranclpE[cases set: rtranclp]:
  fixes a b :: 'a
  assumes major: "r\<^sup>*\<^sup>* a b"
  obtains
    (base) "a = b"
  | (step) y where "r\<^sup>*\<^sup>* a y" and "r y b"
  \<comment> \<open>elimination of \<open>rtrancl\<close> -- by induction on a special formula\<close>
proof -
  have "a = b \<or> (\<exists>y. r\<^sup>*\<^sup>* a y \<and> r y b)"
    by (rule major [THEN rtranclp_induct]) blast+
  then show ?thesis
    by (auto intro: base step)
qed

thm converse_rtranclpE

thm rtranclp.induct[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]

text \<open>Improved induction rule for step_exps\<close>
(*
lemma step_exps_induct[consumes 1, case_names Reduce Refl]:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> 
      and \<open>(\<And>e\<^sub>1 e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3 \<Longrightarrow> P e\<^sub>2 \<Longrightarrow> P e\<^sub>1)\<close> 
      and \<open>P e\<^sub>3\<close>
    shows \<open>P e\<^sub>1\<close>
  using assms by (induct \<Delta> e\<^sub>1 e\<^sub>3 rule: step_exps.induct, blast+)
*)
end