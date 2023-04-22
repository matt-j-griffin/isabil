theory BIR_Instrs
  imports BIR_Variables Statement_Semantics
begin


text \<open>Call statements either return to a specific address or revert to the call stack\<close> 

datatype ret =
      NoReturn (\<open>noreturn\<close>)
    | Return word (\<open>return _\<close>)

fun
  ret_to_bil :: \<open>ret \<Rightarrow> bil\<close>
where
  \<open>ret_to_bil (return ret) = Stmt (SP := (Val (Immediate ret))) Empty\<close> | 
  \<open>ret_to_bil _ = Empty\<close>


lemma ret_to_bil_finite: \<open>bil_finite (ret_to_bil ret)\<close>
  by (cases ret, auto)

text \<open>Instructions in BIR\<close> 


instantiation bil :: move_syntax
begin

definition 
  move_syntax_bil :: \<open>BIL_Syntax.var \<Rightarrow> exp \<Rightarrow> bil\<close>
where
  \<open>move_syntax_bil var exp = Stmt (var := exp) Empty\<close>

instance by (standard, simp add: move_syntax_bil_def)

end

lemma step_bil_move: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> var := e \<leadsto> \<Delta>(var \<mapsto> v),w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2,Empty\<close>
  unfolding move_syntax_bil_def apply (rule SEQ_ONE)
  using assms(1) by (rule MOVE)

definition 
  sub_syntax :: \<open>string \<Rightarrow> bil\<close> (\<open>sub _\<close>)
where
  \<open>sub _ \<equiv> Empty\<close>

lemma step_bil_sub: \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> sub l \<leadsto> \<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2,Empty\<close>
  unfolding sub_syntax_def by (rule SEQ_NIL)



definition 
  call_syntax :: \<open>exp \<Rightarrow> ret \<Rightarrow> bil\<close> (\<open>call _ with _\<close>)
where
  \<open>call exp with ret \<equiv> Stmt (Jmp exp) (ret_to_bil ret)\<close>

lemma call_syntax_inject:
  assumes \<open>(call exp with ret) = call exp' with ret'\<close>
    shows \<open>exp' = exp \<and> ret' = ret\<close>
  using assms unfolding call_syntax_def apply auto
  apply (cases ret)
  apply (cases ret')
  apply auto
  apply (cases ret')
  by auto

lemma step_bil_call:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close> (* TODO tidy all val immediates *)
      and \<open>\<Delta>,w\<^sub>3 \<turnstile> ret_to_bil ret \<leadsto> \<Delta>',w,Empty\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> call e with ret \<leadsto> \<Delta>',w,Empty\<close>
  unfolding call_syntax_def apply (rule SEQ_NEXT)
  apply (rule JMP)
  apply (rule assms(1))
  by (rule assms(2))

lemma step_bil_call_noreturn:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> call e with noreturn \<leadsto> \<Delta>,w\<^sub>3,Empty\<close>
  apply (rule step_bil_call)
  apply (rule assms(1))
  unfolding ret_to_bil.simps by (rule SEQ_NIL)

lemma step_bil_call_return:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile>  call e with return w\<^sub>r\<^sub>e\<^sub>t \<leadsto> \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t),w\<^sub>3,Empty\<close>
  apply (rule step_bil_call)
  apply (rule assms(1))
  unfolding ret_to_bil.simps apply (rule SEQ_ONE)
  apply (rule MOVE)
  by simp

definition 
  Special :: \<open>string \<Rightarrow> bil\<close>
where
  \<open>Special string \<equiv> Stmt (stmt.Special string) Empty\<close>

lemma special_inject: (* TODO update all of this to use inject *)
  assumes \<open>BIR_Instrs.Special special = BIR_Instrs.Special special'\<close>
    shows \<open>special = special'\<close>
  using assms unfolding Special_def by simp

lemma special_not_inject[simp]:
  assumes \<open>special \<noteq> special'\<close>
    shows \<open>BIR_Instrs.Special special \<noteq> BIR_Instrs.Special special'\<close>
  using assms unfolding Special_def by simp

lemma step_bil_special: \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> BIR_Instrs.Special string \<leadsto> \<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2,Empty\<close>
  unfolding Special_def apply (rule SEQ_ONE)
  by (rule SPECIAL)

definition
  goto_syntax :: \<open>word \<Rightarrow> bil\<close> (\<open>goto _\<close>)
where
  \<open>goto word \<equiv> Stmt (Jmp (Val (Immediate word))) Empty\<close>

lemma goto_inject: (* TODO update all of this to use inject *)
  assumes \<open>(goto w) = goto w'\<close>
    shows \<open>w = w'\<close>
  using assms unfolding goto_syntax_def by simp

lemma goto_is_call: \<open>(goto w) = call Val (Immediate w) with noreturn\<close>
  unfolding goto_syntax_def call_syntax_def by auto

lemma call_noreturn_is_goto: \<open>( call Val (Immediate w) with noreturn) = goto w\<close>
  unfolding goto_syntax_def call_syntax_def by auto



lemma step_bil_goto: \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> goto w' \<leadsto> \<Delta>,w',Empty\<close>
  unfolding goto_syntax_def apply (rule SEQ_ONE)
  apply (rule JMP)
  by simp

definition
  when_syntax :: \<open>exp \<Rightarrow> bil \<Rightarrow> bil\<close> (\<open>when _ _\<close>)
where
  \<open>when exp\<^sub>1 bil \<equiv> Stmt (IfThen exp\<^sub>1 bil) Empty\<close>

lemma when_inject: (* TODO update all of this to use inject *)
  assumes \<open>(when exp\<^sub>1 bil\<^sub>1) = when exp\<^sub>2 bil\<^sub>2\<close>
    shows \<open>exp\<^sub>1 = exp\<^sub>2 \<and> bil\<^sub>1 = bil\<^sub>2\<close>
  using assms unfolding when_syntax_def by simp

lemma when_disinject[simp]:
  assumes \<open>exp\<^sub>1 \<noteq> exp\<^sub>2 \<or> bil\<^sub>1 \<noteq> bil\<^sub>2\<close>
    shows \<open>(when exp\<^sub>1 bil\<^sub>1) \<noteq> when exp\<^sub>2 bil\<^sub>2\<close>
  using assms unfolding when_syntax_def by simp

lemma step_bil_when_true:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> when e\<^sub>1 bil \<leadsto> \<Delta>',w',Empty\<close>
  unfolding when_syntax_def apply (rule SEQ_ONE)
  using assms by (rule IFTHEN_TRUE)

lemma step_bil_when_true_call_return:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w')\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> when e\<^sub>1 call e\<^sub>2 with return w\<^sub>r\<^sub>e\<^sub>t \<leadsto> \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t),w',Empty\<close>
  apply (rule step_bil_when_true)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_call_return)

lemma step_bil_when_true_call_noreturn:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w')\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> when e\<^sub>1 call e\<^sub>2 with noreturn \<leadsto> \<Delta>,w',Empty\<close>
  apply (rule step_bil_when_true)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_call_noreturn)

lemma step_bil_when_true_goto:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> when e goto w' \<leadsto> \<Delta>,w',Empty\<close>
  apply (rule step_bil_when_true)
  apply (rule assms(1))
  by (rule step_bil_goto)

lemma step_bil_when_false:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* false\<close>
    shows \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> when e\<^sub>1 bil \<leadsto> \<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2,Empty\<close>
  unfolding when_syntax_def apply (rule SEQ_ONE)
  using assms(1) by (rule IFTHEN_FALSE)

definition
  noop_syntax :: \<open>bil\<close> (\<open>noop\<close>)
where
  \<open>noop \<equiv> Empty\<close>

lemma step_bil_noop: \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> noop \<leadsto> \<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2,Empty\<close>
  unfolding noop_syntax_def by (rule SEQ_NIL)

lemma noop_unique_bil[simp]:
  \<open>noop \<noteq> var := e\<close> \<open>noop \<noteq> goto w\<close> \<open>noop \<noteq> Special string\<close>
  \<open>noop \<noteq> call exp with ret\<close> \<open>noop \<noteq> when e bil\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma sub_unique_bil[simp]:
  \<open>(sub l) \<noteq> var := e\<close> \<open>(sub l) \<noteq> goto w\<close> \<open>(sub l) \<noteq> Special string\<close>
  \<open>(sub l) \<noteq> call exp with ret\<close> \<open>(sub l) \<noteq> when e bil\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma special_unique_bil[simp]:
  \<open>(Special string) \<noteq> var := e\<close> \<open>(Special string) \<noteq> goto w\<close> \<open>(Special string) \<noteq> noop\<close>
  \<open>(Special string) \<noteq> call exp with ret\<close> \<open>(Special string) \<noteq> when e bil\<close> 
  \<open>(Special string) \<noteq> sub id'\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma move_unique_bil[simp]:
  \<open>var := e \<noteq> noop\<close> \<open>var := e \<noteq> sub id'\<close> \<open>var := e \<noteq> goto w\<close> \<open>var := e \<noteq> Special string\<close>
  \<open>var := e \<noteq> call exp with ret\<close> \<open>var := e\<^sub>1 \<noteq> when e\<^sub>2 bil\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma goto_eq_call_imm_no_returnI:
  assumes \<open>exp = Val (Immediate w)\<close>
    shows \<open>(goto w) = call exp with noreturn\<close>
  using assms unfolding goto_syntax_def call_syntax_def by auto

lemma goto_eq_call_immE:
  assumes \<open>(goto w) = call exp with ret\<close>
    shows \<open>exp = Val (Immediate w)\<close>
  using assms by (simp add: call_syntax_def goto_syntax_def)

lemmas goto_eq_call_imm_no_returnE = goto_eq_call_immE (* TODO*)

lemma goto_unique_bil[simp]:
  \<open>(goto w) \<noteq> noop\<close> \<open>(goto w) \<noteq> var := e\<close> \<open>(goto w) \<noteq> Special string\<close> 
  \<open>(goto w) \<noteq> call exp with return w'\<close> \<open>(goto w) \<noteq> when e\<^sub>2 bil\<close> \<open>(goto w) \<noteq> sub id'\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma call_unique_bil[simp]:
  \<open>(call exp with ret) \<noteq> noop\<close> \<open>(call exp with ret) \<noteq> var := e\<close> \<open>(call exp with ret) \<noteq> sub id'\<close>
  \<open>(call exp with ret) \<noteq> Special string\<close> \<open>(call exp with ret) \<noteq> when e\<^sub>2 bil\<close> 
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def
            BIR_Instrs.Special_def move_syntax_bil_def by auto

lemma call_no_return_unique_bil[simp]: \<open>(call exp with noreturn) \<noteq> call exp' with return w'\<close>
  unfolding call_syntax_def by auto

lemma call_return_unique_bil[simp]: \<open>(call exp with return w') \<noteq> call exp' with noreturn\<close>
  unfolding call_syntax_def by auto

lemma call_imm_eq_gotoE:
  assumes \<open>(call exp with ret) = goto w\<close>
    shows \<open>exp = Val (Immediate w)\<close>
  using assms by (simp add: call_syntax_def goto_syntax_def)

lemma when_call_imm_eq_gotoE:
  assumes \<open>(when e\<^sub>1 call e\<^sub>2 with ret) = when e\<^sub>1 goto w\<close>
    shows \<open>e\<^sub>2 = Val (Immediate w)\<close>
  using assms by (meson call_imm_eq_gotoE when_disinject)

lemma when_goto_call_imm_eqE:
  assumes \<open>(when e goto w) = when e\<^sub>1 call e\<^sub>2 with ret\<close>
    shows \<open>e\<^sub>2 = Val (Immediate w)\<close>
  using assms goto_eq_call_imm_no_returnE when_disinject by blast

lemma when_call_imm_eq_gotoI:
  assumes \<open>e\<^sub>2 = Val (Immediate w)\<close>
    shows \<open>(when e\<^sub>1 call e\<^sub>2 with noreturn) = when e\<^sub>1 goto w\<close>
  using assms unfolding when_syntax_def goto_syntax_def call_syntax_def by auto

lemmas call_imm_no_return_eq_gotoE = call_imm_eq_gotoE

lemma when_unique_bil[simp]:
  \<open>(when e\<^sub>1 bil) \<noteq> noop\<close> \<open>(when e\<^sub>1 bil) \<noteq> var := e\<close> \<open>(when e\<^sub>1 bil) \<noteq> Special string\<close> 
  \<open>(when e\<^sub>1 bil) \<noteq> call exp with ret\<close> \<open>(when e\<^sub>1 bil) \<noteq> goto w\<close> \<open>(when e\<^sub>1 bil) \<noteq> sub id'\<close>
  unfolding noop_syntax_def goto_syntax_def when_syntax_def sub_syntax_def call_syntax_def 
            BIR_Instrs.Special_def move_syntax_bil_def by auto

definition 
  is_birinsn :: \<open>bil \<Rightarrow> bool\<close> (* TODO should Special string exist? *)
where
  \<open>is_birinsn bil \<equiv> (bil = noop) \<or> (\<exists>w. bil = goto w) \<or> (\<exists>string. bil = Special string) 
      \<or> (\<exists>exp ret. bil = call exp with ret) \<or> (\<exists>id. bil = sub id) \<or> (\<exists>var exp. bil = var := exp)
      \<or> (\<exists>exp\<^sub>1 bil\<^sub>1. bil = (when exp\<^sub>1 bil\<^sub>1) \<and> ((\<exists>w. bil\<^sub>1 = goto w) \<or> (\<exists>exp ret. bil\<^sub>1 = call exp with ret)))
  \<close>

lemma is_bir_ok_exhaust:
  assumes \<open>is_birinsn bil\<close>
  obtains
    (NoOp)
      \<open>bil = noop\<close>
  | (Special) str where
      \<open>bil = Special str\<close>
  | (Sub) id where
      \<open>bil = sub id\<close>
  | (Move) var e where
      \<open>bil = (var := e)\<close>
  | (Goto) w where
      \<open>bil = goto w\<close>
  | (CallReturn) w' w\<^sub>r\<^sub>e\<^sub>t e where
      \<open>bil = call e with return w\<^sub>r\<^sub>e\<^sub>t\<close>
  | (CallNoReturn) w' e where  
      \<open>bil = call e with noreturn\<close>
  | (WhenGoto) e w where
      \<open>bil = when e goto w\<close>
  | (WhenCallReturn) w' w\<^sub>r\<^sub>e\<^sub>t e\<^sub>1 e\<^sub>2 where
      \<open>bil = when e\<^sub>1 call e\<^sub>2 with return w\<^sub>r\<^sub>e\<^sub>t\<close>
  | (WhenCallNoReturn) w' e\<^sub>1 e\<^sub>2 where
      \<open>bil = when e\<^sub>1 call e\<^sub>2 with noreturn\<close>
  using assms unfolding is_birinsn_def apply safe
  apply simp_all
  subgoal for e ret
    apply (cases ret)
    by auto
  subgoal for e 
    by (metis ret.exhaust)
  .

lemma birinsn_is_finite: \<open>is_birinsn bil \<Longrightarrow> bil_finite bil\<close>
  unfolding is_birinsn_def apply (elim disjE)
  unfolding noop_syntax_def apply auto[1]
  unfolding goto_syntax_def apply auto[1]
  unfolding Special_def apply auto[1]
  unfolding call_syntax_def apply auto[1]
  apply (rule ret_to_bil_finite)
  unfolding move_syntax_bil_def apply auto[1]
  unfolding sub_syntax_def apply auto[1]
  unfolding when_syntax_def apply auto
  apply (rule ret_to_bil_finite)
  done

(* Non interface *)
(* TODO these proofs suck *)

lemma step_bil_noopE:
  assumes \<open>\<Delta>,w \<turnstile> noop \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding noop_syntax_def 
  using eval_inf_bil_simps step_pred_bil_empty_equiv by blast

lemma step_bil_moveE:
  assumes \<open>\<Delta>,w \<turnstile> var := e \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>\<Delta>' = \<Delta>(var \<mapsto> v) \<and> w' = w\<close>
  using assms unfolding move_syntax_bil_def apply (drule_tac SEQ_NEXT_REV)
  apply auto
  using SEQ_NIL_NEQ eval_inf_stmt_simps eval_pred_stmt_def stmt.distinct(5) stmt.distinct(9) stmt.inject(1) apply blast
  by (smt (verit, del_insts) eval_inf_stmt_simps eval_pred_stmt_def noop_syntax_def step_bil_noopE stmt.distinct(1) stmt.distinct(7) stmt.distinct(9))

lemma step_bil_gotoE:
  assumes \<open>\<Delta>,w \<turnstile> goto w'' \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w''\<close>
  using assms unfolding goto_syntax_def 
  using eval_inf_bil_simps step_pred_bil_empty_equiv
  by (smt (verit) SEQ_NEXT_REV eval_exp.simps(1) eval_inf_stmt.cases eval_pred_stmt_def noop_syntax_def step_bil_noopE stmt.distinct(1) stmt.distinct(11) stmt.distinct(13) stmt.distinct(15) stmt.distinct(17) stmt.inject(2) val.inject(1))

lemma step_bil_subE:
  assumes \<open>\<Delta>,w \<turnstile> sub id' \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding sub_syntax_def 
  by (simp add: noop_syntax_def step_bil_noopE)

lemma step_bil_specialE:
  assumes \<open>\<Delta>,w \<turnstile> Special special \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding Special_def apply (drule_tac SEQ_NEXT_REV)
  by (smt (verit, best) eval_inf_stmt_simps eval_pred_stmt_def noop_syntax_def step_bil_noopE stmt.distinct(13) stmt.distinct(25) stmt.distinct(27) stmt.distinct(5))

lemma step_bil_call_returnE:
  assumes \<open>\<Delta>,w \<turnstile> call e with return w\<^sub>r\<^sub>e\<^sub>t \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w'')\<close>
    shows \<open>\<Delta>' = \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t) \<and> w' = w''\<close>
  using assms unfolding call_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  apply (thin_tac \<open>\<Delta>,w \<turnstile> Stmt jmp e (Stmt (SP := Val (Immediate w\<^sub>r\<^sub>e\<^sub>t)) Empty) \<leadsto> \<Delta>',w',Empty\<close>)
  apply (drule_tac SEQ_NEXT_REV, clarify)
  by (smt (verit) eval_exp.simps(1) eval_exps_pred_exp.elims(2) eval_inf_stmt_simps eval_pred_stmt_def move_syntax_stmt.elims noop_syntax_def step_bil_noopE stmt.distinct(1) stmt.distinct(11) stmt.distinct(13) stmt.distinct(15) stmt.distinct(17) stmt.distinct(3) stmt.distinct(5) stmt.distinct(7) stmt.distinct(9) stmt.inject(1) stmt.inject(2) val.inject(1))

lemma step_bil_call_noreturnE:
  assumes \<open>\<Delta>,w \<turnstile> call e with noreturn \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w'')\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w''\<close>
  using assms unfolding call_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  apply (thin_tac \<open>\<Delta>,w \<turnstile> Stmt jmp e Empty \<leadsto> \<Delta>',w',Empty\<close>)
  by (smt (verit) eval_exp.simps(1) eval_exps_pred_exp.elims(2) eval_inf_stmt_simps eval_pred_stmt_def move_syntax_stmt.elims noop_syntax_def step_bil_noopE stmt.distinct(1) stmt.distinct(11) stmt.distinct(13) stmt.distinct(15) stmt.distinct(17) stmt.distinct(3) stmt.distinct(5) stmt.distinct(7) stmt.distinct(9) stmt.inject(1) stmt.inject(2) val.inject(1))

lemma step_bil_when_falseE:
  assumes \<open>\<Delta>,w \<turnstile> when e bil \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* false\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<close>
  using assms unfolding when_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  unfolding eval_pred_stmt_def  
  apply (drule_tac eval_inf_stmt_simps, auto)
  apply (metis noop_syntax_def step_bil_noopE step_pred_bil_empty_equiv)
  apply (metis noop_syntax_def step_bil_noopE step_pred_bil_empty_equiv)
  done

lemma step_bil_when_gotoE:
  assumes \<open>\<Delta>,w \<turnstile> when e goto w'' \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w''\<close>
  using assms unfolding when_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  unfolding eval_pred_stmt_def  
  apply (drule_tac eval_inf_stmt_simps, auto)
  apply (metis noop_syntax_def step_bil_gotoE step_bil_noopE step_pred_bil_empty_equiv)
  apply (metis noop_syntax_def step_bil_gotoE step_bil_noopE step_pred_bil_empty_equiv)
  done

lemma step_bil_when_call_returnE:
  assumes \<open>\<Delta>,w \<turnstile> when e\<^sub>1 call e\<^sub>2 with return w\<^sub>r\<^sub>e\<^sub>t \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w\<^sub>c\<^sub>a\<^sub>l\<^sub>l)\<close>
    shows \<open>\<Delta>' = \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t) \<and> w' = w\<^sub>c\<^sub>a\<^sub>l\<^sub>l\<close>
  using assms unfolding when_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  unfolding eval_pred_stmt_def  
  apply (drule_tac eval_inf_stmt_simps, auto)
  using noop_syntax_def step_bil_call_returnE step_bil_noopE step_pred_bil_empty_equiv apply auto[1]
  using noop_syntax_def step_bil_call_returnE step_bil_noopE step_pred_bil_empty_equiv apply auto[1]
  apply metis
  done

lemma step_bil_when_call_noreturnE:
  assumes \<open>\<Delta>,w \<turnstile> when e\<^sub>1 call e\<^sub>2 with noreturn \<leadsto> \<Delta>',w',Empty\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w\<^sub>c\<^sub>a\<^sub>l\<^sub>l)\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>c\<^sub>a\<^sub>l\<^sub>l\<close>
  using assms unfolding when_syntax_def ret_to_bil.simps 
  apply (drule_tac SEQ_NEXT_REV, clarify)
  unfolding eval_pred_stmt_def  
  apply (drule_tac eval_inf_stmt_simps, auto)
  apply (metis assms(3) noop_syntax_def step_bil_call_noreturnE step_bil_noopE step_pred_bil_empty_equiv)
  apply (metis assms(3) noop_syntax_def step_bil_call_noreturnE step_bil_noopE step_pred_bil_empty_equiv)
  done


(*
lemma birinsn_is_finite: 
  assumes \<open>is_birinsn bil\<close>
      and \<open>\<Delta>,w \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>wfnew \<Gamma> \<Delta>\<close> 

  unfolding is_birinsn_def apply (elim disjE)
  unfolding noop_syntax_def apply auto[1]
  unfolding goto_syntax_def apply auto[1]
  unfolding Special_def apply auto[1]
  unfolding call_syntax_def apply auto[1]
  apply (rule ret_to_bil_finite)
  unfolding sub_syntax_def apply auto[1]
  unfolding when_syntax_def apply auto
  apply (rule ret_to_bil_finite)
  done
*)
end