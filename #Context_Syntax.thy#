theory Context_Syntax
  imports Main BIL_Syntax
begin

section \<open>Context syntax\<close>

text \<open>Contexts are used in the typing judgments to specify the types of all variables. While each 
      variable is annotated with its type, the context ensures that all uses of a given variable 
      have the same type.\<close>

type_synonym TypingContext = \<open>var list\<close>

definition 
  dom\<^sub>\<Gamma> :: \<open>TypingContext \<Rightarrow> Id set\<close>
where
  \<open>dom\<^sub>\<Gamma> \<Gamma> = fst ` (set \<Gamma>)\<close>

lemma tg_set_nil: \<open>dom\<^sub>\<Gamma> [] = {}\<close>
  by (simp add: dom\<^sub>\<Gamma>_def)
  

end
