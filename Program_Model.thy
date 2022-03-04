theory Program_Model
  imports Statement_Semantics
begin              

type_synonym program = \<open>(variables \<times> word \<times> var)\<close>

consts decode :: \<open>program \<Rightarrow> insn\<close>

definition 
  decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (\<open>_ \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i _\<close>)
where
  \<open>(prog \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i instr) \<equiv> (instr = decode prog)\<close>

fun 
  step :: \<open>program \<Rightarrow> program\<close>
where
  \<open>step (\<Delta>, w, mem) = (
    let instr = decode (\<Delta>, w, mem) in
    let (\<Delta>', w\<^sub>3) = eval_bil \<Delta> (addr instr +\<^sub>b\<^sub>v size instr) (code instr) in
      (\<Delta>', w\<^sub>3, mem)
  )\<close>

inductive
  step_pred :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  \<open>\<lbrakk>
    (prog \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>); 
    (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty)
   \<rbrakk> \<Longrightarrow> ((\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem'))\<close>

lemma STEP: 
  assumes \<open>(\<Delta>, w, prog) \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty\<close>
    shows \<open>(\<Delta>, w, prog) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, prog)\<close>
  using assms by (simp add: step_pred.intros)

end