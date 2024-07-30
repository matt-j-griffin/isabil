theory Program_Model
  imports "../StatementSemantics/Statement_Syntax"
          "../Instruction_Syntax"
begin

locale bil_syntax =
    fixes decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91)
  assumes (*decode_pc: \<open>\<And>\<Delta> w mem w' sz bil. (\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w', size = sz, code = bil \<rparr> \<Longrightarrow> w' = w\<close> (* TODO is needed *)
      and *)decode_detE: \<open>\<And>\<Delta> w\<^sub>1 mem prog prog' P. \<lbrakk>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog; (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog'; prog' = prog \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>
begin

inductive 
  step_pred :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  Step: \<open>\<lbrakk>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>; (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3)\<rbrakk> 
    \<Longrightarrow> (\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem)\<close>

inductive_cases StepE: \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem')\<close>

lemma step_neq_mem:
  assumes \<open>mem \<noteq> mem'\<close>
    shows \<open>\<not>((\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem'))\<close>
  using assms apply (intro notI)
  apply (elim StepE)
  by simp

end

end
