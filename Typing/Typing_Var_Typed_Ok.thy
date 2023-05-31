theory Typing_Var_Typed_Ok
  imports Typing_Typed_Ok
          Typing_Context
begin

class var_typed_ok = var_syntax + typed_ok +
  assumes var_typed_okI: \<open>\<And>\<Gamma> id t. \<lbrakk>(id :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; t is ok\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (id :\<^sub>t t) :: t\<close>
      and var_typed_okE: \<open>\<And>\<Gamma> id t. \<Gamma> \<turnstile> (id :\<^sub>t t) :: t \<Longrightarrow> (id :\<^sub>t t) \<in> set \<Gamma> \<and> \<Gamma> is ok \<and> t is ok\<close>
      and var_typed_diff: \<open>\<And>\<Gamma> id t t'. \<Gamma> \<turnstile> (id :\<^sub>t t') :: t \<Longrightarrow> t' = t\<close>
begin


lemmas T_VAR = var_typed_okI

method solve_T_VAR = (
  rule T_VAR, simp, solve_TG, solve_TWF (* TODO wayward simp*)
)

end

end
