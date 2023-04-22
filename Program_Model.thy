theory Program_Model
  imports Statement_Semantics
begin              


section \<open>A\<close>

text \<open>Definition of a program\<close>

type_synonym program = \<open>(variables \<times> word \<times> var)\<close>

abbreviation 
  pc :: \<open>program \<Rightarrow> word\<close>
where
  \<open>pc prog \<equiv> fst (snd prog)\<close>

section \<open>AAA\<close>

locale bil_syntax =
    fixes decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91) 
(*  assumes decode_pc: \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog \<Longrightarrow> addr prog = w\<^sub>1\<close>
      and decode_deterministic: \<open>\<lbrakk>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog; (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog'\<rbrakk> \<Longrightarrow> prog' = prog\<close>*)
begin

function
  step_pred :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem) = (\<exists>w\<^sub>2 bil. 
    (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> \<and> 
    (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>', w\<^sub>3, Empty))\<close> |
  \<open>\<lbrakk>mem \<noteq> mem'\<rbrakk> \<Longrightarrow> (_, _, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (_, _, mem') = False\<close>
  subgoal for P x
    apply (cases x)
    subgoal for prog \<Delta>' w\<^sub>3 mem'
      apply (cases prog)
      subgoal for \<Delta> w mem
        by (cases \<open>mem \<noteq> mem'\<close>, auto)
      .
    .
  by auto
termination by (standard, auto)

end



(*
section \<open>AAA\<close>

locale finite_bil_syntax =
    fixes decode :: \<open>program \<Rightarrow> insn\<close>
  assumes decode_insn_finite: \<open>\<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> = decode s \<Longrightarrow> bil_finite bil\<close>
begin

definition
  decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91) 
where
  \<open>s \<mapsto>\<^sub>b\<^sub>i\<^sub>l i \<equiv> (i = decode s)\<close>

lemma decode_pred_insn_finite: 
  assumes \<open>s \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
    shows \<open>bil_finite bil\<close>
  using assms decode_insn_finite decode_pred_def by auto
  

fun
  step :: \<open>program \<Rightarrow> program\<close>
where
  \<open>step (\<Delta>, w, mem) = (
    let instr = decode (\<Delta>, w, mem) in
    let (\<Delta>', w\<^sub>3) = eval_bil \<Delta> (addr instr +\<^sub>b\<^sub>v size instr) (code instr) in
      (\<Delta>', w\<^sub>3, mem)
  )\<close>

definition
  step_pred :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  \<open>s \<leadsto>\<^sub>b\<^sub>i\<^sub>l i \<equiv> (i = step s)\<close>


lemma step: 
  assumes \<open>(\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr>addr = w\<^sub>1, size = w\<^sub>2, code = bil\<rparr>\<close>
      and \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> bil \<leadsto> \<Delta>',w\<^sub>3,Empty\<close>
    shows \<open>(\<Delta>, w, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w\<^sub>3, mem)\<close>
  using assms apply (drule_tac step_pred_bil_finite_empty)
  apply (simp add: decode_pred_insn_finite)
  by (metis decode_pred_def internal_case_prod_conv internal_case_prod_def select_convs(1-3) 
            step.simps step_pred_def) 

sublocale bil_syntax
  where decode_pred=decode_pred
    and step_pred=step_pred
  apply standard
  using step by simp

end
*)
end