theory Program_Model
  imports "../StatementSemantics/Statement_Syntax"
          "../Instruction_Syntax"
begin

locale bil_syntax =
    fixes decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91)
  assumes decode_pc: \<open>\<And>\<Delta> w mem w' sz bil. (\<Delta>, w, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w', size = sz, code = bil \<rparr> \<Longrightarrow> w' = w\<close>
      and decode_deterministic: \<open>\<And>\<Delta> w\<^sub>1 mem prog prog'. \<lbrakk>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog; (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog'\<rbrakk> \<Longrightarrow> prog' = prog\<close>
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

end
