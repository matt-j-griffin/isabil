theory Typing_Type
  imports Typing_Syntax
          "HOL-Eisbach.Eisbach"
begin

subsection \<open>t is ok\<close>

instantiation Type :: is_ok
begin

primrec 
  is_ok_Type :: \<open>Type \<Rightarrow> bool\<close>
where 
  \<open>is_ok_Type imm\<langle>sz\<rangle> = (sz > 0)\<close> |
  \<open>is_ok_Type mem\<langle>sz\<^sub>1, sz\<^sub>2\<rangle> = (sz\<^sub>1 > 0 \<and> sz\<^sub>2 > 0)\<close>

instance ..

end

lemma TWF_IMM: 
  assumes \<open>sz > 0\<close> shows \<open>imm\<langle>sz\<rangle> is ok\<close>
  using assms by auto

lemma TWF_MEM: 
  assumes \<open>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> shows \<open>mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> is ok\<close>
  using assms by auto


method solve_TWF = (
  match conclusion in
    \<open>imm\<langle>_\<rangle> is ok\<close> \<Rightarrow> \<open>rule TWF_IMM, linarith\<close>
  \<bar> \<open>mem\<langle>_, _\<rangle> is ok\<close> \<Rightarrow> \<open>rule TWF_MEM, linarith, linarith\<close>
)


end