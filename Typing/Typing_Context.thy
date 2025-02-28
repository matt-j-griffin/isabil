theory Typing_Context
  imports Typing_Type 
          "../Var"
begin


section \<open>Context syntax\<close>

text \<open>Contexts are used in the typing judgments to specify the types of all variables. While each 
      variable is annotated with its type, the context ensures that all uses of a given variable 
      have the same type.\<close>

type_synonym TypingContext = \<open>var list\<close>

definition
  dom\<^sub>\<Gamma> :: \<open>TypingContext \<Rightarrow> string set\<close>
where
  \<open>dom\<^sub>\<Gamma> \<Gamma> = var_name ` (set \<Gamma>)\<close>

lemma dom\<^sub>\<Gamma>_nil[simp]: \<open>dom\<^sub>\<Gamma> [] = {}\<close>
  by (simp add: dom\<^sub>\<Gamma>_def)

lemma dom\<^sub>\<Gamma>_Cons[simp]: \<open>dom\<^sub>\<Gamma> ((name :\<^sub>t t) # \<Gamma>) = insert name (dom\<^sub>\<Gamma> \<Gamma>)\<close>
  unfolding dom\<^sub>\<Gamma>_def by auto

subsection \<open>\<Gamma> is ok\<close>

instantiation list :: (var_syntax) is_ok
begin

function
  is_ok_list :: \<open>TypingContext \<Rightarrow> bool\<close>
where 
  \<open>is_ok_list [] = True\<close> |
  \<open>is_ok_list ((id' :\<^sub>t t) # \<Gamma>) = (id' \<notin> dom\<^sub>\<Gamma> \<Gamma> \<and> (t is ok) \<and> is_ok_list \<Gamma>)\<close>
  subgoal for P x
    apply (rule list.exhaust[of x], blast)
    subgoal for y ys
      apply (rule var_exhaust[of y])
      by blast
    .
  by auto
termination by lexicographic_order

instance ..

end

lemma TG_NIL: \<open>([]::TypingContext) is ok\<close>
  by auto

lemma TG_CONS: 
  assumes \<open>x \<notin> dom\<^sub>\<Gamma> \<Gamma>\<close> and \<open>t is ok\<close> and \<open>\<Gamma> is ok\<close>
    shows \<open>((x :\<^sub>t t) # \<Gamma>) is ok\<close>
  using assms by auto

lemma TG_SINGLE: 
  assumes \<open>t is ok\<close> shows \<open>(([(x :\<^sub>t t)])::TypingContext) is ok\<close>
  apply (rule TG_CONS[of _ \<open>[]\<close>])
  using assms by auto


method typec_context = (
    rule TG_NIL | 
    (rule TG_SINGLE, solve_type_is_ok) | 
    (rule TG_CONS, (unfold dom\<^sub>\<Gamma>_def, simp), solve_type_is_ok, typec_context) (* TODO simp *)
)

end
