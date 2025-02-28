theory Typing_Type
  imports Typing_Syntax 
          Type_Syntax 
          "HOL-Eisbach.Eisbach"
begin

subsection \<open>t is ok\<close>

instantiation Type :: is_ok
begin

primrec 
  is_ok_Type :: \<open>Type \<Rightarrow> bool\<close>
where 
  imm_is_ok: \<open>is_ok_Type imm\<langle>sz\<rangle> = (sz > 0)\<close> |
  mem_is_ok: \<open>is_ok_Type mem\<langle>sz\<^sub>1, sz\<^sub>2\<rangle> = (sz\<^sub>1 > 0 \<and> sz\<^sub>2 > 0)\<close>

instance ..

end

lemma imm_is_okI: 
  assumes \<open>sz > 0\<close> shows \<open>imm\<langle>sz\<rangle> is ok\<close>
  using assms by auto

lemma mem_is_okI: 
  assumes \<open>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> shows \<open>mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> is ok\<close>
  using assms by auto

method solve_type_is_ok uses add = (rule imm_is_okI mem_is_okI add; (rule add | linarith))

\<comment> \<open>BIL manual names\<close>

lemmas TWF_IMM = imm_is_okI
lemmas TWF_MEM = mem_is_okI

end