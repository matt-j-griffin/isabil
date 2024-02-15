theory Formula_Syntax
  imports BIL_Syntax 
          "HOL-Eisbach.Eisbach"
begin

type_synonym variables = \<open>var \<rightharpoonup> val\<close>

fun 
  val_var_in_vars :: \<open>(var \<times> val) \<Rightarrow> variables \<Rightarrow> bool\<close> (infixl \<open>\<in>\<^sub>\<Delta>\<close> 160)
where
  \<open>((var, val) \<in>\<^sub>\<Delta> \<Delta>) = (var \<in> dom \<Delta> \<and> the (\<Delta> var) = val)\<close>  

declare val_var_in_vars.simps[simp del]

lemma val_the_var[simp]: 
  assumes \<open>var \<in> dom \<Delta>\<close>
    shows \<open>(var, the (\<Delta> var)) \<in>\<^sub>\<Delta> \<Delta>\<close>
  unfolding val_var_in_vars.simps using assms by simp

lemma var_in_val_the_var[simp]: 
  assumes \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(var, the (\<Delta> var)) \<in>\<^sub>\<Delta> \<Delta>\<close>
  apply (rule val_the_var)
  using assms(1) unfolding val_var_in_vars.simps by blast

lemma var_in_dropI:
  assumes \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>var \<noteq> var'\<close>
    shows \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta>(var' \<mapsto> val')\<close>
  using assms unfolding val_var_in_vars.simps by simp

lemma in_vars_the_simp: 
  assumes \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>the (\<Delta> var) = val\<close>
  using assms unfolding val_var_in_vars.simps by simp 

lemma var_in_addI[simp]: \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta> (var \<mapsto> val)\<close>
  unfolding val_var_in_vars.simps by simp

lemma var_in_add_eqI: assumes \<open>val = val'\<close> shows \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta> (var \<mapsto> val')\<close>
  unfolding assms by simp

lemma var_in_deterministic:
  assumes \<open>(var, val\<^sub>1) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(var, val\<^sub>2) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>val\<^sub>1 = val\<^sub>2\<close>
  using assms unfolding val_var_in_vars.simps by simp

lemma var_in_dom_\<Delta>[intro]: \<open>(var, val) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> var \<in> dom \<Delta>\<close> 
  unfolding val_var_in_vars.simps by blast


text \<open>Attempt to solve a proof of the form (var, val) \<in> \<Delta>\<close>

method solve_in_var = (
    ((assumption | rule var_in_addI | (rule var_in_add_eqI, (simp; fail)) | (rule var_in_dropI))+);
    (assumption | (unfold var_syntax_class.var_eq List.list.inject String.char.inject Type.inject, blast)[1])
)

end
