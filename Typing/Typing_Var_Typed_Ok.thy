theory Typing_Var_Typed_Ok
  imports Typing_Typed_Ok
          Typing_Context
begin

class var_typed_ok = var_syntax + typed_ok +
  assumes var_typed_ok: \<open>\<And>\<Gamma> id t t'. (\<Gamma> \<turnstile> (id :\<^sub>t t) :: t') \<longleftrightarrow> 
                      ((id :\<^sub>t t) \<in> set \<Gamma> \<and> \<Gamma> is ok \<and> t is ok \<and> t' = t)\<close>
begin

lemma var_typed_okI:
  assumes \<open>(name :\<^sub>t t) \<in> set \<Gamma>\<close> \<open>\<Gamma> is ok\<close> \<open>t is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (name :\<^sub>t t) :: t\<close>
  using assms var_typed_ok by auto

lemma var_typed_okE:
  fixes id
  assumes \<open>\<Gamma> \<turnstile> (id :\<^sub>t t) :: t'\<close>
  obtains \<open>(id :\<^sub>t t) \<in> set \<Gamma>\<close> \<open>\<Gamma> is ok\<close> \<open>t is ok\<close> \<open>t' = t\<close>
  using assms var_typed_ok by auto

lemmas T_VAR = var_typed_okI

method typec_var = (
  rule var_typed_okI, simp, typec_context, solve_type_is_ok (* TODO wayward simp*)
)



end

end
