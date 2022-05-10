theory Program_Model
  imports Statement_Semantics
begin              


section \<open>A\<close>

text \<open>\<close>

type_synonym program = \<open>(variables \<times> word \<times> var)\<close>


section \<open>AAA\<close>

locale bil =
  fixes decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i\<close> 91) 
begin

inductive
  step_pred :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  \<open>\<lbrakk>
    ((\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>); 
    (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty)
   \<rbrakk> \<Longrightarrow> ((\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem))\<close>

lemma STEP: 
  assumes \<open>(\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty\<close>
    shows \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem)\<close>
  using assms by (simp add: step_pred.intros)

end 


section \<open>AAA\<close>


locale finite_bil = bil 
+  
    fixes decode :: \<open>program \<Rightarrow> insn\<close>
  assumes decode_pred_equiv: \<open>s \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i i \<longleftrightarrow> i = decode s\<close>
      and decode_insn_finite: \<open>s \<mapsto>\<^sub>b\<^sub>i\<^sub>r\<^sub>i \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> \<Longrightarrow> bil_finite bil\<close>
begin 

fun
  step :: \<open>program \<Rightarrow> program\<close>
where
  \<open>step (\<Delta>, w, mem) = (
    let instr = decode (\<Delta>, w, mem) in
    let (\<Delta>', w\<^sub>3) = eval_bil \<Delta> (addr instr +\<^sub>b\<^sub>v size instr) (code instr) in
      (\<Delta>', w\<^sub>3, mem)
  )\<close>

lemma \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem') \<Longrightarrow> (\<Delta>', w', mem') = step (\<Delta>, w, mem)\<close>
  apply (induct rule: step_pred.inducts)
  apply (drule_tac step_pred_bil_finite_empty)
  using decode_insn_finite finite_bil_axioms apply blast
  apply (simp add: decode_pred_equiv Let_def del: Bitvector_Syntax.add.simps)
  by (metis old.prod.case select_convs(1) select_convs(2) select_convs(3))

end


end