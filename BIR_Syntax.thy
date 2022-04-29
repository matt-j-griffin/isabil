theory BIR_Syntax
  imports BIL
begin

consts addr_size :: nat

subsection \<open>Program Memory\<close>

typedecl hex (*TODO*)
consts convert_hex :: \<open>hex \<Rightarrow> nat\<close>
abbreviation
  const_prog_addr :: \<open>hex \<Rightarrow> word\<close> (\<open>%_\<close>)
where
  \<open>%n \<equiv> Word (convert_hex n)  addr_size\<close>


subsection \<open>Data Memory\<close>

consts main_mem :: Id
abbreviation
  mem :: var
where
  \<open>mem \<equiv> (main_mem, Mem addr_size 8)\<close>

subsection \<open>Registers\<close>

text \<open>General-Purpose Registers (GPR)\<close>

consts rax :: Id
definition
  RAX :: var
where
  \<open>RAX \<equiv> (rax, Imm 64)\<close>

consts rbx :: Id
definition
  RBX :: var
where
  \<open>RBX \<equiv> (rbx, Imm 64)\<close>

consts rcx :: Id
definition
  RCX :: var
where
  \<open>RCX \<equiv> (rcx, Imm 64)\<close>

consts rdx :: Id
definition
  RDX :: var
where
  \<open>RDX \<equiv> (rdx, Imm 64)\<close>

consts rsp :: Id
definition
  RSP :: var
where
  \<open>RSP \<equiv> (rsp, Imm 64)\<close>

consts rbp :: Id
definition
  RBP :: var
where
  \<open>RBP \<equiv> (rbp, Imm 64)\<close>

consts rdi :: Id
definition
  RDI :: var
where
  \<open>RDI \<equiv> (rdi, Imm 64)\<close>

consts rsi :: Id
definition
  RSI :: var
where
  \<open>RSI \<equiv> (rsi, Imm 64)\<close>

text \<open>Additional 64bit general purpose registers R8-15\<close>

consts reg_id :: \<open>nat \<Rightarrow> Id\<close>
definition
  R8 :: var
where
  \<open>R8 \<equiv> (reg_id 8, Imm 64)\<close>

definition
  R9 :: var
where
  \<open>R9 \<equiv> (reg_id 9, Imm 64)\<close>

definition
  R10 :: var
where
  \<open>R10 \<equiv> (reg_id 10, Imm 64)\<close>

definition
  R11 :: var
where
  \<open>R11 \<equiv> (reg_id 11, Imm 64)\<close>

definition
  R12 :: var
where
  \<open>R12 \<equiv> (reg_id 12, Imm 64)\<close>

definition
  R13 :: var
where
  \<open>R13 \<equiv> (reg_id 13, Imm 64)\<close>

definition
  R14 :: var
where
  \<open>R14 \<equiv> (reg_id 14, Imm 64)\<close>

definition
  R15 :: var
where
  \<open>R15 \<equiv> (reg_id 15, Imm 64)\<close>


text \<open>We define the eight 128 bit registers as constants\<close>

consts xmm :: \<open>nat \<Rightarrow> Id\<close>
definition
  XMM0 :: var
where
  \<open>XMM0 \<equiv> (xmm 0, Imm 128)\<close>

definition
  XMM1 :: var
where
  \<open>XMM1 \<equiv> (xmm 1, Imm 128)\<close>

definition
  XMM2 :: var
where
  \<open>XMM2 \<equiv> (xmm 2, Imm 128)\<close>

definition
  XMM3 :: var
where
  \<open>XMM3 \<equiv> (xmm 3, Imm 128)\<close>

definition
  XMM4 :: var
where
  \<open>XMM4 \<equiv> (xmm 4, Imm 128)\<close>

definition
  XMM5 :: var
where
  \<open>XMM5 \<equiv> (xmm 5, Imm 128)\<close>

definition
  XMM6 :: var
where
  \<open>XMM6 \<equiv> (xmm 6, Imm 128)\<close>

definition
  XMM7 :: var
where
  \<open>XMM7 \<equiv> (xmm 7, Imm 128)\<close>

text \<open>Same for the 256 bit registers\<close>

consts ymm :: \<open>nat \<Rightarrow> Id\<close>
definition
  YMM0 :: var
where
  \<open>YMM0 \<equiv> (ymm 0, Imm 256)\<close>

definition
  YMM1 :: var
where
  \<open>YMM1 \<equiv> (ymm 1, Imm 256)\<close>

definition
  YMM2 :: var
where
  \<open>YMM2 \<equiv> (ymm 2, Imm 256)\<close>

definition
  YMM3 :: var
where
  \<open>YMM3 \<equiv> (ymm 3, Imm 256)\<close>

definition
  YMM4 :: var
where
  \<open>YMM4 \<equiv> (ymm 4, Imm 256)\<close>

definition
  YMM5 :: var
where
  \<open>YMM5 \<equiv> (ymm 5, Imm 256)\<close>

definition
  YMM6 :: var
where
  \<open>YMM6 \<equiv> (ymm 6, Imm 256)\<close>

definition
  YMM7 :: var
where
  \<open>YMM7 \<equiv> (ymm 7, Imm 256)\<close>

text \<open>Same for the 512 bit registers\<close>

consts zmm :: \<open>nat \<Rightarrow> Id\<close>
definition
  ZMM0 :: var
where
  \<open>ZMM0 \<equiv> (zmm 0, Imm 512)\<close>

definition
  ZMM1 :: var
where
  \<open>ZMM1 \<equiv> (zmm 1, Imm 512)\<close>

definition
  ZMM2 :: var
where
  \<open>ZMM2 \<equiv> (zmm 2, Imm 512)\<close>

definition
  ZMM3 :: var
where
  \<open>ZMM3 \<equiv> (zmm 3, Imm 512)\<close>

definition
  ZMM4 :: var
where
  \<open>ZMM4 \<equiv> (zmm 4, Imm 512)\<close>

definition
  ZMM5 :: var
where
  \<open>ZMM5 \<equiv> (zmm 5, Imm 512)\<close>

definition
  ZMM6 :: var
where
  \<open>ZMM6 \<equiv> (zmm 6, Imm 512)\<close>

definition
  ZMM7 :: var
where
  \<open>ZMM7 \<equiv> (zmm 7, Imm 512)\<close>

text \<open>The eflags in BIR are represented as individual registers\<close>

consts cf :: Id
definition
  CF :: var
where
  \<open>CF \<equiv> (cf, Imm 1)\<close>

consts of_reg :: Id
definition
  OF :: var
where
  \<open>OF \<equiv> (of_reg, Imm 1)\<close>

consts af :: Id
definition
  AF :: var
where
  \<open>AF \<equiv> (of_reg, Imm 1)\<close>

consts pf :: Id
definition
  PF :: var
where
  \<open>PF \<equiv> (pf, Imm 1)\<close>

consts sf :: Id
definition
  SF :: var
where
  \<open>SF \<equiv> (sf, Imm 1)\<close>

consts zf :: Id
definition
  ZF :: var
where
  \<open>ZF \<equiv> (zf, Imm 1)\<close>


text \<open>We define virtual registers (or variables) as a function over a natural number, which uniquely 
      identifies the variable\<close>

consts virtual :: \<open>nat \<Rightarrow> Id\<close>

definition 
  virtual_reg :: \<open>nat \<Rightarrow> var\<close> (\<open>#_\<close>)
where
  \<open>#x \<equiv> (virtual x, Imm 64)\<close>

abbreviation 
  virual_old :: \<open>nat \<Rightarrow> var\<close> (\<open>V_\<close>)
where
  \<open>V(x::nat) \<equiv> #x\<close>

text \<open>BIR will only commit stores and loads to the main memory (mem)\<close>

fun 
  wfe :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>wfe (Load e\<^sub>1 e\<^sub>2 en sz) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Load e\<^sub>1 e\<^sub>2 en sz))\<close> |
  \<open>wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3))\<close> |
  \<open>wfe e = BIL_Syntax.wfe e\<close>

section \<open>\<close>

datatype calltype =
      Direct Id
    | Indirect exp

datatype callreturn =
      NoReturn (\<open>noreturn\<close>)
    | Return word

datatype birinsn =
      NoOp
    | Move var exp
    | Call calltype callreturn
    | ConditionalGoto exp word
    | Goto word
    | Sub Id
    | Special string

type_synonym program_memory = \<open>word \<rightharpoonup> birinsn\<close>

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

fun
  wf_program_memory :: \<open>program_memory \<Rightarrow> bool\<close>
where
  \<open>wf_program_memory \<Pi> = (\<forall>x \<in> dom \<Pi>. wf_program_addr x)\<close>

lemma dom_program_memory_finite:
    fixes \<Pi> :: program_memory
  assumes \<open>wf_program_memory \<Pi>\<close>
    shows \<open>finite (dom \<Pi>)\<close>
  apply (subgoal_tac \<open>inj_on raw_val (dom \<Pi>)\<close>)
  apply (subgoal_tac \<open>finite (raw_val ` dom \<Pi>)\<close>)
  apply (simp add: finite_image_iff)
  defer
  using wf_program_addr_inj_on apply (meson assms inj_onI wf_program_memory.elims(2))
  apply (subgoal_tac \<open>(\<forall>x \<in> dom \<Pi>. raw_val x < (2 ^ addr_size))\<close>)
  apply (subgoal_tac \<open>(\<forall>x \<in> (raw_val ` dom \<Pi>). x < (2 ^ addr_size))\<close>)
  using finite_nat_set_iff_bounded apply auto[1]
  apply simp
  using assms apply auto[1]
  by (simp add: domI wf_program_addr_simps)

(* Make this a constant and instantiate this later using a context*)

definition
  find_label_set :: \<open>program_memory \<Rightarrow> Id \<Rightarrow> word set\<close> 
where 
  \<open>find_label_set \<Pi> name = {Addr\<^sub>\<Pi>. \<Pi> Addr\<^sub>\<Pi> = Some (Sub name)}\<close>

definition
  find_label :: \<open>program_memory \<Rightarrow> Id \<Rightarrow> word\<close> 
where 
  \<open>find_label \<Pi> name = Word (Min (raw_val ` find_label_set \<Pi> name)) addr_size\<close>

fun
  calltype_to_bil :: \<open>program_memory \<Rightarrow> calltype \<Rightarrow> stmt\<close>
where
  \<open>calltype_to_bil \<Pi> (Direct name) = Jmp (Val (Immediate (find_label \<Pi> name)))\<close> | 
  \<open>calltype_to_bil \<Pi> (Indirect exp) = Jmp exp\<close>

fun
  callreturn_to_bil :: \<open>callreturn \<Rightarrow> bil\<close>
where
  \<open>callreturn_to_bil (Return ret) = Stmt (stmt.Move RSP (Val (Immediate ret))) Empty\<close> | 
  \<open>callreturn_to_bil _ = Empty\<close>

fun
  bir_to_bil :: \<open>program_memory \<Rightarrow> birinsn \<Rightarrow> bil\<close>
where
  \<open>bir_to_bil _ NoOp = Empty\<close> |
  \<open>bir_to_bil _ (Move var exp) = Stmt (stmt.Move var exp) Empty\<close> |
  \<open>bir_to_bil \<Pi> (Call calltype callreturn) = Stmt (calltype_to_bil \<Pi> calltype) (callreturn_to_bil callreturn)\<close> |
  \<open>bir_to_bil _ (ConditionalGoto exp word) = Stmt (IfThen exp (Stmt (Jmp (Val (Immediate word))) Empty)) Empty\<close> |
  \<open>bir_to_bil _ (Goto word) = Stmt (Jmp (Val (Immediate word))) Empty\<close> |
  \<open>bir_to_bil _ (Sub _) = Empty\<close> |
  \<open>bir_to_bil _ (Special string) = Stmt (stmt.Special string) Empty\<close>

text \<open>A BIR step is always finite\<close>

lemma bir_step_finite: \<open>bil_finite (bir_to_bil \<Pi> birinsn)\<close>
  apply (cases birinsn, auto)
  apply (metis calltype_to_bil.elims stmt_finite.simps(4))
  by (metis bil_finite.simps(1) bil_finite.simps(2) callreturn_to_bil.elims stmt_finite.simps(3))


fun
  decode_bir :: \<open>program_memory \<Rightarrow> program \<Rightarrow> insn\<close>
where
  \<open>decode_bir \<Pi> (_, w, _) = (
    case \<Pi> w of
      Some i \<Rightarrow> \<lparr> addr = w, size = (1 \<Colon> addr_size), code = bir_to_bil \<Pi> i \<rparr>      
      | _ \<Rightarrow> no_insn
  )\<close>

text \<open>BIR only allows for one memory in the variable set, ensure the variable type is a memory and 
      all other variables are registers (immediates)\<close>

definition 
  wf\<Delta> :: \<open>variables \<Rightarrow> bool\<close>
where
  \<open>wf\<Delta> \<Delta> \<equiv> (\<forall>var \<in> dom \<Delta>. snd var = type (the (\<Delta> var))) \<and>
            (\<forall>var \<in> dom \<Delta>. var \<noteq> mem \<longrightarrow> (\<exists>sz. snd var = Imm sz))\<close>

(*
thm load.induct

lemma XXX[consumes 2]:
  assumes \<open>\<Gamma> \<turnstile> v :: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
      and \<open>v' = load v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>
    shows \<open>P v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms apply (induct v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en rule: load.induct)
  defer
  defer
  apply simp
  defer
  sledgehammer



lemma \<Gamma>_val_implies_load_val:
  assumes \<open>\<Gamma> \<turnstile> v :: t\<close>
      and \<open>t = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>sz\<^sub>v\<^sub>a\<^sub>l \<ge> sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>v' = load v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en\<close>
    shows \<open>\<Gamma> \<turnstile> v' :: (Imm sz\<^sub>v\<^sub>a\<^sub>l)\<close>
  apply (induct v')
    defer defer
  sledgehammer
  

  using assms apply (induct rule: typing_expression_val_induct)
  apply simp
  defer
  apply simp

  sledgehammer


  using assms apply (induct v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en rule: load.induct)
  defer 
  apply auto[1]
  apply simp


  apply (frule_tac typing_val_storage)
  apply (auto simp del: load.simps)
  apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m\<close>)
  apply simp

  apply (subgoal_tac \<open>\<Gamma> \<turnstile> load mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r)
                 (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)
                 en :: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)\<close>)
  


*)

lemma \<Gamma>_is_ok_implies_t_is_ok:
  fixes \<Gamma> :: TypingContext 
  assumes \<open>(name, t) \<in> set \<Gamma>\<close>
      and \<open>\<Gamma> is ok\<close>
    shows \<open>t is ok\<close>
  using assms by (induct \<Gamma>, auto)

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
    using \<Gamma>_val_type_implies_type_t apply blast
    apply (metis \<Gamma>_val_type_implies_type_t typing_val_implies_valid_t)
    using typing_val_implies_valid_context apply blast
    using \<Gamma>_val_imm_not_storage by blast
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
    apply (metis T_UNKNOWN Type.simps(5) \<Gamma>_val_type_implies_type_t add_gr_0 is_ok_Type.simps(1) type.simps(3) typing_val_implies_valid_context typing_val_implies_valid_t)
    using \<Gamma>_val_imm_not_storage by blast
qed

lemma \<Gamma>_exp_type_implies_type_t:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>type (eval_exp \<Delta> e) = t\<close>
  using assms apply (drule_tac \<Delta>=\<Delta> in typing_expression_exp_implies_eval_exp, auto)
  by (simp add: \<Gamma>_val_type_implies_type_t)

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

lemma wf\<Delta>_birstep:
    fixes stmt :: stmt 
  assumes \<open>wfnew \<Gamma> \<Delta>\<close>
      and \<open>\<Gamma> \<turnstile> stmt is ok\<close>
      and \<open>(\<Delta>',w') = eval_stmt \<Delta> w stmt\<close>
      and \<open>stmt_finite stmt\<close>
    shows \<open>wfnew \<Gamma> \<Delta>'\<close>
  using assms apply (induct stmt, auto)
  using typing_expression_exp_implies_eval_exp wfnew_def apply auto[1]
  apply (case_tac \<open>eval_exp \<Delta> x\<close>)
  apply auto 
  defer
  using \<Gamma>_val_imm_not_storage typing_expression_exp_implies_eval_exp apply blast
  apply (case_tac \<open>eval_exp \<Delta> x61\<close>)
  apply auto

    apply (auto simp add: wf\<Delta>_def)
     defer
  apply (case_tac \<open>eval_exp \<Delta> x2\<close>)
  apply auto
  defer
    apply (auto simp add: wf\<Delta>_def)[1]

  oops 



  


end