theory Expressions_Rules
  imports Expression_Rules
begin

definition "deterministic r \<longleftrightarrow> (\<forall>(a,b) \<in> r. \<forall>c. (a,c) \<in> r \<longrightarrow> b = c)"
definition "deterministicp r \<longleftrightarrow> (\<forall>a b c. r a b \<longrightarrow> r a c \<longrightarrow> b = c)"



lemma rtranclpE[cases set: rtranclp]:
  fixes a b :: 'a
  assumes major: "r\<^sup>*\<^sup>* a b"
  obtains
    (base) "a = b"
  | (step) y where "r\<^sup>*\<^sup>* a y" and "r y b" and "a \<noteq> b"
  \<comment> \<open>elimination of \<open>rtrancl\<close> -- by induction on a special formula\<close>
proof -
  have "a = b \<or> (\<exists>y. r\<^sup>*\<^sup>* a y \<and> r y b)"
    by (rule major [THEN rtranclp_induct]) blast+
  then show ?thesis
    by (auto intro: base step)
qed

lemma rtranclp_detD:
  assumes major: "r\<^sup>*\<^sup>* a c" and caveat: \<open>deterministicp r\<close>
      and "r a b" and "a \<noteq> c"
    shows "r\<^sup>*\<^sup>* b c"
  by (metis assms(3) assms(4) caveat converse_rtranclpE deterministicp_def major)
(*
lemma det_rtranclpE[cases set: rtranclp]:
  fixes a b :: 'a
  assumes major: \<open>r\<^sup>*\<^sup>* a c\<close> and caveat: \<open>deterministicp r\<close> and \<open>r a b\<close>
  obtains
    (base) \<open>a = c\<close>
  | (step) \<open>a \<noteq> c\<close> \<open>r\<^sup>*\<^sup>* b c\<close>
using major proof (rule converse_rtranclpE)
  fix y :: 'a
  assume "r a y" "r\<^sup>*\<^sup>* y c"
  show thesis
    using step
    by (meson GGGG assms(3) base caveat major)
qed auto
*)

definition
  step_exps :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close> [400, 400, 400] 401)
where
  \<open>step_exps \<Delta> \<equiv> (step_exp \<Delta>)\<^sup>*\<^sup>*\<close>

lemmas step_exps_induct = rtranclp_induct[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric], consumes 1, case_names base step, induct set: rtranclp]
lemmas step_exps_converse_induct = converse_rtranclp_induct[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric], consumes 1, case_names base step]
lemmas step_exps_trans = rtranclp_trans[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]
lemmas step_exps_reduceI = converse_rtranclp_into_rtranclp[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]
lemmas step_exps_reflI = rtranclp.rtrancl_refl[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]
lemmas step_exps_tranclpE = rtranclpE[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]
lemmas step_exps_converse_tranclpE = converse_rtranclpE[where r = \<open>step_exp _\<close>, unfolded step_exps_def[symmetric]]

lemma step_exps_total_reduceI:
  assumes major: "\<Delta> \<turnstile> e \<leadsto>* e'"
      and minor: "\<Delta> \<turnstile> E e' \<leadsto>* e''"
      and rule: \<open>\<And>\<Delta> e e' e''. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> E e' \<leadsto>* e'' \<Longrightarrow> \<Delta> \<turnstile> E e \<leadsto>* e''\<close>
    shows "\<Delta> \<turnstile> E e \<leadsto>* e''"
proof (rule step_exps_trans [OF _ minor])
  show "\<Delta> \<turnstile> E e \<leadsto>* (E e')"
    using major 
    apply (induct e rule: step_exps_converse_induct)
    apply (rule step_exps_reflI)
    using rule by blast
qed

end
