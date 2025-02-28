theory Program_Model
  imports "../StatementSemantics/Statement_Syntax"
          "../Instruction_Syntax"
begin


lemma bool_simps: \<open>Immediate false = false\<close> \<open>Immediate true = true\<close> \<open>Val false = false\<close> \<open>Val true = true\<close>
  unfolding word_constructor_exp_def by auto

named_theorems syntax_simps 
lemmas standard_syntax_simps[syntax_simps] = plus_exp_def[symmetric]   minus_exp_def[symmetric]  
    divide_exp_def[symmetric]  modulo_exp_def[symmetric] times_exp_def[symmetric]
    lsr_exp_def[symmetric]     lsl_exp_def[symmetric]    asr_exp_def[symmetric] 
    land_exp_def[symmetric]    lor_exp_def[symmetric]    xor_exp_def[symmetric]
    sdivide_exp_def[symmetric] smod_exp_def[symmetric]   not_exp_def[symmetric]
    lt_exp_def[symmetric]      le_exp_def[symmetric]   slt_exp_def[symmetric]
    sle_exp_def[symmetric]   uminus_exp_def[symmetric]
    Word_simp insn.defs
    var_constructor_var_def[symmetric] var_constructor_exp_def[symmetric]
    Immediate_simp Val_simp_word Val_simp_storage Val_simp_unknown
    (*false_word[symmetric] true_word[symmetric] bool_simps*)
    unknown_constructor_val_def[symmetric] One_nat_def
  
locale bil_syntax =
    fixes decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91)
  assumes decode_detE: \<open>\<And>\<Delta> w\<^sub>1 mem prog prog' P. \<lbrakk>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog; (\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l prog'; prog' = prog \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>
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
