theory BIR_Syntax
  imports BIL HOL.String
begin

abbreviation
  reg :: \<open>nat \<Rightarrow> var \<Rightarrow> bool\<close>
where
  \<open>reg n r \<equiv> snd r = Imm n\<close>

abbreviation
  flag :: \<open>var \<Rightarrow> bool\<close>
where
  \<open>flag r \<equiv> reg 1 r\<close>

abbreviation
  reg64 :: \<open>var \<Rightarrow> bool\<close>
where
  \<open>reg64 r \<equiv> reg 64 r\<close>

abbreviation
  reg128 :: \<open>var \<Rightarrow> bool\<close>
where
  \<open>reg128 r \<equiv> reg 128 r\<close>

abbreviation
  reg256 :: \<open>var \<Rightarrow> bool\<close>
where
  \<open>reg256 r \<equiv> reg 256 r\<close>

abbreviation
  reg512 :: \<open>var \<Rightarrow> bool\<close>
where
  \<open>reg512 r \<equiv> reg 512 r\<close>

text \<open>Call statements either return to a specific address or revert to the call stack\<close> 

datatype ret =
      NoReturn (\<open>noreturn\<close>)
    | Return word (\<open>return _\<close>)

fun
  stack_ret_to_bil :: \<open>var \<Rightarrow> ret \<Rightarrow> bil\<close>
where
  \<open>stack_ret_to_bil RSP (return ret) = Stmt (stmt.Move RSP (Val (Immediate ret))) Empty\<close> | 
  \<open>stack_ret_to_bil _ _ = Empty\<close>


lemma stack_ret_to_bil_finite: \<open>bil_finite (stack_ret_to_bil RSP ret)\<close>
  by (cases ret, auto)

text \<open>Instructions in BIR\<close> 

datatype birinsn =
      NoOp (\<open>noop\<close>)
    | Move var exp (\<open>_ := _\<close>)
    | Call exp ret (\<open>call _ with _\<close>)
    | ConditionalGoto exp word (\<open>when _ goto _\<close>)
    | Goto word (\<open>goto _\<close>)
    | Sub Id (\<open>sub _\<close>)
    | Special string 

fun
  stack_bir_to_bil :: \<open>var \<Rightarrow> birinsn \<Rightarrow> bil\<close>
where
  \<open>stack_bir_to_bil _ noop = Empty\<close> |
  \<open>stack_bir_to_bil _ (var := exp) = Stmt (stmt.Move var exp) Empty\<close> |
  \<open>stack_bir_to_bil RSP (call exp with ret) = Stmt (Jmp exp) (stack_ret_to_bil RSP ret)\<close> |
  \<open>stack_bir_to_bil _ (when exp goto word) = Stmt (IfThen exp (Stmt (Jmp (Val (Immediate word))) Empty)) Empty\<close> |
  \<open>stack_bir_to_bil _ (goto word) = Stmt (Jmp (Val (Immediate word))) Empty\<close> |
  \<open>stack_bir_to_bil _ (sub _) = Empty\<close> |
  \<open>stack_bir_to_bil _ (Special string) = Stmt (stmt.Special string) Empty\<close>

lemma stack_bir_to_bil_finite: \<open>bil_finite (stack_bir_to_bil RSP birinsn)\<close>
  using stack_ret_to_bil_finite by (cases birinsn, auto)



locale bir = finite_bil
+
  fixes decode_bir :: \<open>program \<Rightarrow> birinsn\<close>
    and addr_size :: nat
    and label_exp :: \<open>Id \<Rightarrow> exp\<close> (\<open>@_\<close>)
    and mem 
        RAX RBX RCX RSP RBP RDI RSI
        R8 R9 R10 R11 R12 R13 R14 R15
        XMM0 XMM1 XMM2 XMM3 XMM4 XMM5 XMM6 XMM7
        YMM0 YMM1 YMM2 YMM3 YMM4 YMM5 YMM6 YMM7
        ZMM0 ZMM1 ZMM2 ZMM3 ZMM4 ZMM5 ZMM6 ZMM7
        CF OF AF PF SF ZF
        :: var
    and virtual_reg :: \<open>nat \<Rightarrow> var\<close> (\<open>#_\<close>)

assumes \<open>snd mem = Mem addr_size 8\<close>

    and \<open>reg64 RAX\<close> and \<open>reg64 RBX\<close> and \<open>reg64 RCX\<close> and \<open>reg64 RDX\<close>
    and \<open>reg64 RSP\<close> and \<open>reg64 RBP\<close> and \<open>reg64 RDI\<close> and \<open>reg64 RSI\<close>

    and \<open>reg64 R8\<close>  and \<open>reg64 R9\<close>  and \<open>reg64 R10\<close> and \<open>reg64 R11\<close>
    and \<open>reg64 R12\<close> and \<open>reg64 R13\<close> and \<open>reg64 R14\<close> and \<open>reg64 R15\<close>

    and \<open>reg128 XMM0\<close> and \<open>reg128 XMM1\<close> and \<open>reg128 XMM2\<close> and \<open>reg128 XMM3\<close>
    and \<open>reg128 XMM4\<close> and \<open>reg128 XMM5\<close> and \<open>reg128 XMM6\<close> and \<open>reg128 XMM7\<close>

    and \<open>reg256 YMM0\<close> and \<open>reg256 YMM1\<close> and \<open>reg256 YMM2\<close> and \<open>reg256 YMM3\<close>
    and \<open>reg256 YMM4\<close> and \<open>reg256 YMM5\<close> and \<open>reg256 YMM6\<close> and \<open>reg256 YMM7\<close>

    and \<open>reg512 ZMM0\<close> and \<open>reg512 ZMM1\<close> and \<open>reg512 ZMM2\<close> and \<open>reg512 ZMM3\<close>
    and \<open>reg512 ZMM4\<close> and \<open>reg512 ZMM5\<close> and \<open>reg512 ZMM6\<close> and \<open>reg512 ZMM7\<close>

    and \<open>flag CF\<close> and \<open>flag OF\<close> and \<open>flag AF\<close> and \<open>flag PF\<close> and \<open>flag SF\<close> and \<open>flag ZF\<close>

    and \<open>\<forall>n. reg64 (#n)\<close>

    and \<open>code (decode s) = stack_bir_to_bil RSP (decode_bir s)\<close>
begin

definition 
  bir_to_bil :: \<open>birinsn \<Rightarrow> bil\<close>
where
  \<open>bir_to_bil = stack_bir_to_bil RSP\<close>

lemma bir_to_bil_finite: \<open>bil_finite (bir_to_bil birinsn)\<close>
  using stack_bir_to_bil_finite bir_to_bil_def by simp


abbreviation
  address_word :: \<open>nat \<Rightarrow> word\<close> (\<open>%_\<close>)
where
  \<open>address_word n \<equiv> Word n addr_size\<close>

fun 
  wfe :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>wfe (Load e\<^sub>1 e\<^sub>2 en sz) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Load e\<^sub>1 e\<^sub>2 en sz))\<close> |
  \<open>wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3))\<close> |
  \<open>wfe e = BIL_Syntax.wfe e\<close>

abbreviation 
  virual_old :: \<open>nat \<Rightarrow> var\<close> (\<open>V_\<close>)
where
  \<open>V(x::nat) \<equiv> #x\<close>

definition
  wf_program_addr :: \<open>word \<Rightarrow> bool\<close>
where
  \<open>wf_program_addr w \<equiv> (wf_word w \<and> bits w = addr_size)\<close>

lemma wf_program_addr_simps: 
  assumes \<open>wf_program_addr w\<close>
    shows \<open>raw_val w < (2 ^ addr_size)\<close>
  using assms apply (cases w, auto)
  by (auto simp add: wf_program_addr_def)

lemma wf_program_addr_inj_on:
  assumes \<open>wf_program_addr w\<^sub>1\<close> and \<open>wf_program_addr w\<^sub>2\<close>
      and \<open>raw_val w\<^sub>1 = raw_val w\<^sub>2\<close>
    shows \<open>w\<^sub>1 = w\<^sub>2\<close>
  using assms by (auto simp add: wf_program_addr_def word.expand)

(*
definition 
  wf\<Delta> :: \<open>variables \<Rightarrow> bool\<close>
where
  \<open>wf\<Delta> \<Delta> \<equiv> (\<forall>var \<in> dom \<Delta>. snd var = type (the (\<Delta> var))) \<and>
            (\<forall>var \<in> dom \<Delta>. var \<noteq> mem \<longrightarrow> (\<exists>sz. snd var = Imm sz))\<close>
*)


end



text \<open>BIR will only commit stores and loads to the main memory (mem)\<close>



section \<open>\<close>








text \<open>BIR only allows for one memory in the variable set, ensure the variable type is a memory and 
      all other variables are registers (immediates)\<close>




definition "wfnew (\<Gamma>::TypingContext) (\<Delta>::variables) \<equiv> (\<forall>(name, t) \<in> dom \<Delta>. (\<Gamma> \<turnstile> the (\<Delta> (name, t)) :: t))"

lemma wf\<Delta>_extend:
  assumes \<open>wfnew \<Gamma> \<Delta>\<close> 
      and \<open>name \<notin> dom\<^sub>\<Gamma> \<Gamma>\<close>
      and \<open>\<Gamma> \<turnstile> v :: t\<close>
    shows \<open>wfnew ((name, t) # \<Gamma>) (\<Delta>((name, t) \<mapsto> v))\<close>
  using assms apply (subgoal_tac \<open>((name, t) # \<Gamma>) is ok\<close>)
  apply (auto simp add: wfnew_def typing_expression_\<Gamma>_implies_\<Gamma>_extend)[1]
  apply (metis (mono_tags, lifting) TG_CONS case_prod_conv domI option.sel typing_expression_\<Gamma>_implies_\<Gamma>_extend)
  apply (metis (mono_tags, lifting) TG_CONS case_prod_conv domI option.sel typing_expression_\<Gamma>_implies_\<Gamma>_extend)
  by (auto simp add: typing_val_implies_valid_t typing_val_implies_valid_context)

lemma typing_expression_exp_implies_eval_exp:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>\<Gamma> \<turnstile> (eval_exp \<Delta> e) :: t\<close>
using assms proof (induct arbitrary: \<Delta> rule: typing_expression_exp_induct)
  case (Val \<Gamma> v t)
  then show ?case by auto
next
  case (Var \<Gamma> name t)
  then show ?case 
    using \<Gamma>_is_ok_implies_t_is_ok wfnew_def by auto
next
  case (Load \<Gamma> e\<^sub>1 e\<^sub>2 ed sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m t)
  then show ?case
    using \<Gamma>_val_mem_not_immediate \<Gamma>_val_imm_not_storage apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, auto)
    apply blast
    using typing_val_implies_valid_context apply blast
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>)
    defer defer
    apply blast
    defer
    apply fastforce
    apply (simp_all del: load.simps)
    sorry
next
  case (Store \<Gamma> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l e\<^sub>1 e\<^sub>2 ed e\<^sub>3 t)
  then show ?case 
    sorry
next
  case (BinAOp \<Gamma> e\<^sub>1 aop e\<^sub>2 sz t)
  then show ?case 
    using \<Gamma>_val_imm_not_storage apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>)
    using typing_val_immediate apply (case_tac aop, simp_all)
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply (metis typing_expression_val.simps(2))
    apply blast
    apply (metis typing_expression_val.simps(2))
    by blast
next
  case (BinLOp \<Gamma> e\<^sub>1 lop e\<^sub>2 sz t)
  then show ?case 
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>)
    using typing_val_immediate apply (case_tac lop, simp_all)
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    using typing_val_implies_valid_context \<Gamma>_val_imm_not_storage by blast+
next
  case (UOp \<Gamma> uop e sz t)
  then show ?case 
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    using typing_val_immediate apply (case_tac uop, simp_all)
    apply metis
    apply metis
    apply (metis typing_expression_val.simps(2))
    using \<Gamma>_val_imm_not_storage by blast
next
  case (UnsignedCast \<Gamma> e sz sz' t)
  then show ?case 
    using typing_val_implies_valid_context apply (cases \<open>eval_exp \<Delta> e\<close>, auto)
    using \<Gamma>_val_imm_not_storage by blast
next
  case (SignedCast \<Gamma> e sz sz' t)
  then show ?case 
    using typing_val_implies_valid_context apply (cases \<open>eval_exp \<Delta> e\<close>, auto)
    using \<Gamma>_val_imm_not_storage by blast
next
  case (HighCast \<Gamma> e sz sz' t)
  then show ?case 
    using typing_val_implies_valid_context apply (cases \<open>eval_exp \<Delta> e\<close>, auto)
    apply (metis diff_Suc diff_diff_cancel gr0_implies_Suc old.nat.simps(5) typing_val_immediate)
    using \<Gamma>_val_imm_not_storage by blast
next
  case (LowCast \<Gamma> e sz sz' t)
  then show ?case 
    using typing_val_implies_valid_context apply (cases \<open>eval_exp \<Delta> e\<close>, auto)
    using \<Gamma>_val_imm_not_storage by blast
next
  case (Let \<Gamma> name t' e\<^sub>1 e\<^sub>2 t)
  then show ?case 
    apply auto
    apply (subgoal_tac \<open>\<Gamma> \<turnstile> eval_exp \<Delta> e\<^sub>1 :: t'\<close>) defer
    apply blast  
    apply (drule_tac name=name and t=t' and v=\<open>eval_exp \<Delta> e\<^sub>1\<close> in wf\<Delta>_extend)
    apply simp_all
    using typing_expression_\<Gamma>_extend_implies_\<Gamma> by blast
next
  case (Ite \<Gamma> e\<^sub>1 e\<^sub>2 e\<^sub>3 t)
  then show ?case 
    apply (auto simp add: Let_def)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, auto)
    using \<Gamma>_val_type apply blast
    apply (metis \<Gamma>_val_type typing_val_implies_valid_t)
    using typing_val_implies_valid_context apply blast
    by (metis typing_expression_val.simps(4))
next
  case (Extract \<Gamma> sz\<^sub>1 sz\<^sub>2 sz\<^sub>e\<^sub>x\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>t sz e t)
  then show ?case 
    using typing_val_implies_valid_context apply (cases \<open>eval_exp \<Delta> e\<close>, auto)
    using \<Gamma>_val_imm_not_storage by blast
next
  case (Concat \<Gamma> e\<^sub>1 e\<^sub>2 sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t sz\<^sub>1 sz\<^sub>2 t)
  then show ?case 
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, auto)
    using typing_val_immediate apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>, auto)
    apply metis
    apply metis
    apply metis
    apply (metis Type.simps(5) add_gr_0 is_ok_Type.simps(1) typing_expression_val.simps(2))
    using \<Gamma>_val_imm_not_storage apply blast
    apply (metis TWF_IMM Type.simps(5) \<Gamma>_val_type add_is_0 not_gr_zero typing_expression_val.simps(2))
    using \<Gamma>_val_imm_not_storage by blast
qed

lemma \<Gamma>_exp_type_implies_type_t:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>type (eval_exp \<Delta> e) = t\<close>
  using assms apply (drule_tac \<Delta>=\<Delta> in typing_expression_exp_implies_eval_exp, auto)
  by (simp add: \<Gamma>_val_type)







(*lemma wf\<Delta>_birstep:
    fixes stmt :: stmt 
  assumes \<open>wf\<Delta> \<Delta>\<close>
      and \<open>\<Gamma> \<turnstile> stmt is ok\<close>
      and \<open>(\<Delta>',w') = eval_stmt \<Delta> w stmt\<close>
    shows \<open>wf\<Delta> \<Delta>'\<close>
  using assms apply (cases stmt, auto)
  apply (auto simp add: wf\<Delta>_def) 
     defer
  apply (case_tac \<open>eval_exp \<Delta> x2\<close>)
  apply auto
  defer
    apply (auto simp add: wf\<Delta>_def)[1]
*)
thm eval_stmt_eval_bil.induct
lemma wf\<Delta>_birstep:
  assumes \<open>(\<Delta>',w') = eval_stmt \<Delta> w stmt\<close>
      and \<open>\<Gamma> \<turnstile> stmt is ok\<close>
      and \<open>stmt_finite stmt\<close>
      and \<open>\<forall>e stmt1 stmt2 . stmt \<noteq> stmt.If e stmt1 stmt2\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>wfnew \<Gamma> \<Delta>'\<close>
  using assms apply (induct rule: eval_stmt_eval_bil.induct(1))
  apply auto
  using wfnew_def typing_expression_exp_implies_eval_exp apply auto[1]

  apply (case_tac \<open>eval_exp \<Delta> e\<close>)
  apply simp
  defer (* jmp = unknown[x21]: x22 non-deterministic *)
  using \<Gamma>_val_imm_not_storage typing_expression_exp_implies_eval_exp apply blast
  apply auto[1]

  oops


(*  assumes \<open>\<close>
      and \<open>\<Gamma> \<turnstile> stmt is ok\<close>
      and \<open>stmt_finite stmt\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>wfnew \<Gamma> \<Delta>'\<close>
*)


  


end