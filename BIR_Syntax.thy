theory BIR_Syntax
  imports BIL BIR_Instrs BIR_Variables
begin

context word_constructor
begin

abbreviation
  address_word :: \<open>nat \<Rightarrow> 'a\<close> (\<open>%_\<close>)
where
  \<open>address_word num \<equiv> (num \<Colon> addr_size)\<close>

end


locale bir_syntax = bil_syntax decode_pred
  for decode_pred :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91) 
+
    fixes label_exp :: \<open>string \<Rightarrow> exp\<close> (\<open>@_\<close>)
  assumes insn_always_bil: \<open>prog \<mapsto>\<^sub>b\<^sub>i\<^sub>l insn \<Longrightarrow> is_birinsn (code insn)\<close>
      and addr_size_gt_0: \<open>addr_size > 0\<close>

begin

lemma decode_code_finite: \<open>prog \<mapsto>\<^sub>b\<^sub>i\<^sub>l insn \<Longrightarrow> bil_finite (code insn)\<close>
  apply (rule birinsn_is_finite)
  by (rule insn_always_bil)
  
(*
fun 
  wfe :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>wfe (Load e\<^sub>1 e\<^sub>2 en sz) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Load e\<^sub>1 e\<^sub>2 en sz))\<close> |
  \<open>wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) = (e\<^sub>1 = Var mem \<and> BIL_Syntax.wfe (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3))\<close> |
  \<open>wfe e = BIL_Syntax.wfe e\<close>
*)
(*
definition 
  wfvars :: \<open>variables \<Rightarrow> bool\<close>
where
  \<open>wfvars \<Delta> \<equiv> (mem \<in> dom \<Delta>)\<close>
*)
(*
  \<open>wf\<Delta> \<Delta> \<equiv> (\<forall>var \<in> dom \<Delta>. snd var = type (the (\<Delta> var))) \<and>
            (\<forall>var \<in> dom \<Delta>. var \<noteq> mem \<longrightarrow> (\<exists>sz. snd var = imm\<langle>sz\<rangle>))\<close>
*)

text \<open>And futhermore on BIL steps\<close>

lemma step_progI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>\<Delta>,w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
  unfolding step_pred.simps
  apply (rule exI[of _ w\<^sub>2])
  apply (rule exI[of _ bil])
  apply (intro conjI)
  apply (rule assms(1))  
  by (rule assms(2))

lemma step_progE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
    shows \<open>\<Delta>,(w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) \<turnstile> bil \<leadsto> \<Delta>',w',Empty\<close>
  using assms unfolding step_pred.simps apply clarify
  apply (drule decode_deterministic, blast)
  subgoal for w\<^sub>2 bil
    by simp
  .

lemma step_prog_noopI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = noop \<rparr>\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  by (rule step_bil_noop)

lemma step_prog_noopE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = noop \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close> 
    shows \<open>\<Delta>' = \<Delta> \<and> w' = (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2)\<close>
  apply (rule step_bil_noopE)
  using assms by (rule step_progE)

lemma step_prog_moveI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = var := e \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(var \<mapsto> v), (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_move)

lemma step_prog_moveE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = var := e \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>\<Delta>' = \<Delta>(var \<mapsto> v) \<and> w' = (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2)\<close>
  apply (rule step_bil_moveE[of _ _ _ e])
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_call_noreturnI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = call e with noreturn \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>                                      
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w\<^sub>3, mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_call_noreturn)

lemma step_prog_call_noreturnE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = call e with noreturn \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>3\<close>
  apply (rule step_bil_call_noreturnE)
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_call_returnI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = call e with return w\<^sub>r\<^sub>e\<^sub>t \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t), w\<^sub>3, mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_call_return)

lemma step_prog_call_returnE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = call e with return w\<^sub>r\<^sub>e\<^sub>t \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>\<Delta>' = \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t) \<and> w' = w\<^sub>3\<close>  
  apply (rule step_bil_call_returnE)
  apply (rule_tac step_progE)
  using assms by blast+

lemma step_prog_when_call_returnI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 call e\<^sub>2 with return w\<^sub>r\<^sub>e\<^sub>t \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w')\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t), w', mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2,3) by (rule step_bil_when_true_call_return)

lemma step_prog_when_call_returnE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 call e\<^sub>2 with return w\<^sub>r\<^sub>e\<^sub>t \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w\<^sub>3)\<close>
    shows \<open>\<Delta>' = \<Delta>(SP \<mapsto> Immediate w\<^sub>r\<^sub>e\<^sub>t) \<and> w' = w\<^sub>3\<close>
  apply (rule step_bil_when_call_returnE)
  apply (rule_tac step_progE)
  using assms by blast+

lemma step_prog_when_falseI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 bil \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* false\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_when_false)

lemma step_prog_when_falseE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 bil \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* false\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2)\<close>
  apply (rule step_bil_when_falseE)
  apply (rule_tac step_progE)
  using assms by blast+

lemma step_prog_when_call_noreturnI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 call e\<^sub>2 with noreturn \<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w')\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w', mem)\<close>  
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2,3) by (rule step_bil_when_true_call_noreturn)

lemma step_prog_when_call_noreturnE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e\<^sub>1 call e\<^sub>2 with noreturn \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* true\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* (Immediate w\<^sub>3)\<close>    
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>3\<close>
  apply (rule step_bil_when_call_noreturnE)
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_gotoI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = goto w'\<rparr>\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w', mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  by (rule step_bil_goto)

lemma step_prog_gotoE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = goto w\<^sub>3\<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>3\<close>
  apply (rule step_bil_gotoE)
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_when_gotoI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e goto w'\<rparr>\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w', mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  using assms(2) by (rule step_bil_when_true_goto) 

lemma step_prog_when_gotoE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = when e goto w\<^sub>3\<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* true\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>3\<close>
  apply (rule step_bil_when_gotoE)
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_subI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = sub l\<rparr>\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  by (rule step_bil_sub)

lemma step_prog_subE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = sub l\<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2\<close>
  apply (rule step_bil_subE)
  apply (rule step_progE)
  using assms by blast+

lemma step_prog_specialI:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = Special string \<rparr>\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
  apply (rule step_progI)
  apply (rule assms(1))
  by (rule step_bil_special)

lemma step_prog_specialE:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = Special string \<rparr>\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', w', mem)\<close>
    shows \<open>\<Delta>' = \<Delta> \<and> w' = w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2\<close>
  apply (rule step_bil_specialE)
  apply (rule step_progE)
  using assms by blast+


(*
lemma step_wfnew:
  assumes \<open>(\<Delta>, w\<^sub>1, mem) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2), mem)\<close>
      and \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr>addr = w\<^sub>1, size = w\<^sub>2', code = bil\<rparr>\<close>
      and \<open>\<Gamma> \<turnstile> bil is ok\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>wfnew \<Gamma> \<Delta>'\<close>
  using assms unfolding step_pred.simps apply auto

  using assms apply (frule_tac insn_always_bil, auto)
  
  

  apply (auto simp only: step_pred_def Let_def step.simps)
  apply (auto simp only: decode_def bir_to_bil_def)
  apply (auto simp del: plus_word.simps)
  apply (cases \<open>eval_bil \<Delta> (w +\<^sub>b\<^sub>v decode_size (\<Delta>, w, mem)) (stack_bir_to_bil SP (decode_bir (\<Delta>, w, mem)))\<close>)
  apply (auto simp del: plus_word.simps)
  using wf\<Delta>_birstep by metis
*)
end

end
