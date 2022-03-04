theory Formula_Syntax
  imports Context_Syntax
begin

type_synonym variables = \<open>var \<rightharpoonup> val\<close>

fun 
  val_var_in_vars :: \<open>(var \<times> val) \<Rightarrow> variables \<Rightarrow> bool\<close> (\<open>_ \<in>\<^sub>\<Delta> _\<close>)
where
  \<open>((var, val) \<in>\<^sub>\<Delta> \<Delta>) = (var \<in> dom \<Delta> \<and> the (\<Delta> var) = val)\<close>

end
