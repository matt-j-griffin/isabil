theory Typing_Context
  imports Typing_Type
begin

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
termination
  apply (relation "(\<lambda>p. size_class.size p) <*mlex*> {}")
  apply (rule wf_mlex, blast)
  apply (rule mlex_less)
  by auto

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
  apply (simp add: tg_set_nil)
  using assms by auto


method solve_TG = (
  match conclusion in
    \<open>[] is ok\<close> \<Rightarrow> \<open>rule TG_NIL\<close>
  \<bar> \<open>[_] is ok\<close> \<Rightarrow> \<open>rule TG_SINGLE, solve_TWF\<close>
  \<bar> \<open>(Cons _ _) is ok\<close> \<Rightarrow> \<open>rule TG_CONS,
      (unfold dom\<^sub>\<Gamma>_def, simp),
      solve_TWF,
      solve_TG\<close>
)


end
