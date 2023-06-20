
section \<open>Introduction rules\<close>

theory Expression_Intros
  imports Expression_Syntax          
begin

lemmas(in word_constructor) SUCC = succI

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)
no_notation (ASCII) HOL.Not (\<open>~ _\<close> [40] 40)

lemma STEP_NOT_EQ: \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e)\<close>
  by (induct e, auto)

lemma STEP_NOT_REDUCTION: 
  assumes \<open>eval_exp \<Delta> e \<noteq> eval_exp \<Delta> e'\<close>
    shows \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e')\<close>
  using assms by (induct e, auto)

lemma STEP_NOT_VAL: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<leadsto> e')\<close>
  by simp

lemma STEP_IMPLIES_NOT_VAL: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>e \<noteq> Val v\<close>
  using assms by auto

lemma STEP_NEXT: 
  assumes \<open>eval_exp \<Delta> e = eval_exp \<Delta> e'\<close>
      and \<open>e \<noteq> e'\<close> and \<open>\<forall>v. e \<noteq> Val v\<close>
    shows \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
  using assms by (induct e, auto)

lemma VAR_IN:
  assumes \<open>((id' :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (Val v)\<close>
  using assms by (auto simp add: val_var_in_vars.simps eval_exp.simps)

lemma VAR_IN_WORD:
  assumes \<open>((id' :\<^sub>t t), (num \<Colon> sz)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_TRUE:
  assumes \<open>(id' :\<^sub>t t, true) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>\<Delta> \<turnstile> id' :\<^sub>t t \<leadsto> true\<close>
  unfolding true_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_FALSE:
  assumes \<open>(id' :\<^sub>t t, false) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>\<Delta> \<turnstile> id' :\<^sub>t t \<leadsto> false\<close>
  unfolding false_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_STORAGE:
  assumes \<open>((id' :\<^sub>t t), v[w \<leftarrow> v', sz]) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (v[w \<leftarrow> v', sz])\<close>
  unfolding storage_constructor_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_UNKNOWN:
  assumes \<open>((id' :\<^sub>t t), (unknown[str]: t)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> unknown[str]: t\<close>
  unfolding unknown_constructor_exp_def using assms by (rule VAR_IN)

lemma VAR_UNKNOWN:
  assumes \<open>(id' :\<^sub>t t) \<notin> dom \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> unknown['''']: t\<close>
  using assms by (auto simp add: eval_exp.simps)

lemma LOAD_STEP_ADDR:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1[e\<^sub>2', ed]:usz)\<close>  
  using assms by (cases e\<^sub>2, auto simp add: eval_exp.simps)

lemma LOAD_STEP_MEM:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close>
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps)

lemma LOAD_STEP_MEM_WORD:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (e\<^sub>1'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  unfolding word_constructor_exp_def using assms by (rule LOAD_STEP_MEM)

lemma LOAD_BYTE:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (Val v')\<close>
  by (auto simp add: eval_exp.simps) 

lemma LOAD_BYTE_WORD:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v \<Colon> sz), sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (num\<^sub>v \<Colon> sz)\<close>
  unfolding word_constructor_exp_def[of num\<^sub>v] by (rule LOAD_BYTE)

lemma LOAD_BYTE_FROM_NEXT:
  assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
  shows \<open>\<Delta> \<turnstile> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms apply auto
  subgoal 
    unfolding storage_constructor_exp_def storage_constructor_val_def by auto
  subgoal
    apply (rule val_exhaust[of v])
    apply (simp_all add: eval_exp.simps)
    by (metis Type.inject(2) load.simps(1) type.simps(1) word_exhaust )
  .

lemma LOAD_UN_ADDR: \<open>\<Delta> \<turnstile> e\<^sub>1[unknown[str]: imm\<langle>sz'\<rangle>, ed]:usz \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma LOAD_UN_MEM: \<open>\<Delta> \<turnstile> ((unknown[str]: t)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz) \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma LOAD_WORD_BE:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> 
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> 
  using assms apply (rule_tac val_exhaust[of v])
  subgoal by auto
  subgoal unfolding SUCC bv_plus.simps by (auto simp add: eval_exp.simps)
  subgoal for mem w v'
    apply (auto simp add: eval_exp.simps)
    apply (cases w rule: word_exhaust, auto)
    unfolding SUCC concat_en_be bv_plus.simps by auto
  .

lemma LOAD_WORD_EL:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> 
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms apply (rule_tac val_exhaust[of v])
  subgoal by auto
  subgoal unfolding SUCC bv_plus.simps by (auto simp add: eval_exp.simps)
  subgoal for mem w v'
    apply (auto simp add: eval_exp.simps)
    apply (cases w rule: word_exhaust, auto)
    unfolding SUCC concat_en_el bv_plus.simps by simp
  .

lemma LOAD_WORD_EL_MEM_INTER:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>\<exists>num. w = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
    shows \<open>\<Delta> \<turnstile> (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  unfolding storage_constructor_exp_def using assms(1,2) apply (rule LOAD_WORD_EL)
  using assms(3) by auto


lemma LOAD_WORD_EL_MEM:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  unfolding storage_constructor_exp_def using assms apply (rule LOAD_WORD_EL)
  by (rule type_storageI)

lemma LOAD_WORD_EL_MEM_SUCC:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM)

lemma LOAD_WORD_EL_MEM_SUCC2:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC)

lemma LOAD_WORD_EL_MEM_SUCC3:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC2)

lemma LOAD_WORD_EL_MEM_WORD_ADDR:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms apply (frule_tac LOAD_WORD_EL[of _ _ \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  by (simp_all add: eval_exp.simps)

lemma LOAD_BYTE_FROM_NEXT_MEM_INTER:
  assumes \<open>\<exists>num. w = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> and \<open>\<exists>num. w' = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<and> num \<noteq> num\<^sub>3\<close>
    shows \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v\<^sub>1, sz][w' \<leftarrow> v\<^sub>2, sz])[(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (v[w \<leftarrow> v\<^sub>1, sz][(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms 
  apply (elim exE conjE)
  by (metis LOAD_BYTE_FROM_NEXT storage_constructor_exp_def type.simps(1))

lemma LOAD_BYTE_FROM_NEXT_MEM:
  assumes \<open>num\<^sub>2 \<noteq> num\<^sub>3\<close>
    shows \<open>\<Delta> \<turnstile> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz][(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, sz])[(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz][(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms apply (drule_tac LOAD_BYTE_FROM_NEXT[of _ _ \<open>v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz]\<close>])
  apply simp
  by (simp add: storage_constructor_exp_def)

lemma STORE_STEP_VAL:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> 
  using assms by (cases e\<^sub>3, auto simp add: eval_exp.simps)

lemma STORE_STEP_ADDR:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>2, auto simp add: eval_exp.simps) 

lemma STORE_STEP_ADDR_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz')) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz'))\<close> 
  using assms STORE_STEP_ADDR word_constructor_exp_def by presburger

lemma STORE_STEP_MEM:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps) 

lemma STORE_WORD_BE:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms unfolding xtract.simps apply (auto simp add: eval_exp.simps)
  apply (cases val rule: val_exhaust, auto)
  unfolding SUCC xtract.simps bv_plus.simps by auto

lemma STORE_WORD_EL:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms unfolding xtract.simps apply (auto simp add: eval_exp.simps)
  apply (cases val rule: val_exhaust, auto)
  unfolding SUCC xtract.simps bv_plus.simps by auto

lemma STORE_VAL:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type v' = imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms by (cases ed, auto simp add: eval_exp.simps)
  
lemma STORE_UN_ADDR:
  assumes \<open>type v = t\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>, ed]:usz' \<leftarrow> (Val v')) \<leadsto> (unknown[str]: t)\<close>
  using assms by (cases t, auto simp add: eval_exp.simps)

lemma STORE_STEP_MEM_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<leadsto> e\<^sub>1' with [(num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
  using assms unfolding word_constructor_exp_def by (rule STORE_STEP_MEM)

lemma STORE_WORD_EL_WORD:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (num' \<Colon> sz)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (num' \<Colon> sz)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (num' \<Colon> sz)))\<close>
  using assms STORE_WORD_EL by (metis Val_simp_word type.simps(2))

lemma STORE_WORD_EL_WORD_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
      and \<open>e\<^sub>1 = (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (num' \<Colon> sz)))\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (num' \<Colon> sz)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (num' \<Colon> sz)))\<close>
  using assms apply (drule_tac STORE_WORD_EL_WORD[of _ _ \<open>v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  apply simp
  apply simp
  apply simp
  using STORE_WORD_EL_WORD assms(1) storage_constructor_exp_def type.simps(1) by presburger

lemma STORE_WORD:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms apply (drule_tac STORE_VAL[of _ _ _ \<open>(num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close> _ num ed])
  by (auto simp add: eval_exp.simps)

lemma STORE_WORD_IN_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) \<leadsto> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms apply (drule_tac STORE_WORD[of \<open>v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>, rotated])
  unfolding Val_simp_storage by simp_all

lemma STORE_STEP_MEM_BV_ADD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4) \<leadsto> e\<^sub>1' with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4)\<close>
  using assms unfolding bv_plus.simps by (rule STORE_STEP_MEM_WORD)

lemma STORE_STEP_MEM_SUCC:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<leadsto> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
  using assms unfolding succ.simps by (rule STORE_STEP_MEM_BV_ADD)

lemma STORE_STEP_MEM_SUCC_XTRACT:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz'' \<leadsto> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz''\<close>
  using assms unfolding xtract.simps by (rule STORE_STEP_MEM_SUCC)

lemma STORE_XTRACT:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  unfolding xtract.simps assms(2)[symmetric]
  apply (rule STORE_WORD)
  using assms(1,3) by blast+

lemma STORE_XTRACT_IN_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<leadsto> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms(1) unfolding xtract.simps assms(2)[symmetric]
  by (rule STORE_WORD_IN_MEM)


lemma LET_STEP:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> (Let var e\<^sub>1' e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps)
(*
fun 
  capture_avoiding :: \<open>(Id \<times> Type) set \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>capture_avoiding \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (var \<notin> \<Delta> \<and> capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding (\<Delta> \<union> {var}) e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (UnOp _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (BinOp e\<^sub>1 _ e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Cast _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding \<Delta> (Extract _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Load e\<^sub>1 e\<^sub>2 _ _) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Store e\<^sub>1 e\<^sub>2 _ _ e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding _ _ = True\<close>

lemma let_substitute_v_Let_size_less: 
    \<open>size_class.size (Let var (Val v\<^sub>1) e\<^sub>2) > size_class.size ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  by (induct e\<^sub>2, auto)

lemma capture_avoiding_substitution_eval_eq:
  assumes \<open>capture_avoiding (dom (\<Delta>(var \<mapsto> v))) e\<close> 
    shows \<open>eval_exp (\<Delta>(var \<mapsto> v)) e = eval_exp \<Delta> ([v\<sslash>var]e)\<close> 
  using assms apply (induct e arbitrary: \<Delta>)
  apply auto
  apply (simp_all only: let_substitute_val.simps capture_avoiding.simps)
  by (metis dom_fun_upd fun_upd_twist option.distinct(1))

lemma LET: 
  assumes \<open>capture_avoiding (dom \<Delta>) (Let var (Val v\<^sub>1) e\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (Let var (Val v\<^sub>1) e\<^sub>2) \<leadsto> ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  using assms apply auto
  apply (metis less_not_refl let_substitute_v_Let_size_less)
  using let_substitute_val_size_eq apply auto[1]
  using capture_avoiding_substitution_eval_eq by simp
*)
lemma ITE_STEP_COND:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps)

lemma ITE_STEP_THEN:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>2, auto simp add: eval_exp.simps)

lemma ITE_STEP_ELSE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3')\<close>
  using assms by (cases e\<^sub>3, auto simp add: eval_exp.simps)

lemma ITE_TRUE: \<open>\<Delta> \<turnstile> (Ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>2)\<close>
  by (auto simp add: eval_exp.simps)

lemma ITE_FALSE: \<open>\<Delta> \<turnstile> (Ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>3)\<close>
  by (auto simp add: eval_exp.simps)

lemma ITE_UNK:
  assumes \<open>type v\<^sub>2 = t'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite (unknown[str]: t) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (unknown[str]: t')\<close>
  using assms by (auto simp add: eval_exp.simps unknown_constructor_exp_def)

text \<open>BOP Lemmas\<close>

lemma bop_lhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp e\<^sub>1 bop e\<^sub>2) \<leadsto> (BinOp e\<^sub>1' bop e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps)

lemma bop_rhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val v\<^sub>1) bop e\<^sub>2) \<leadsto> (BinOp (Val v\<^sub>1) bop e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto simp add: eval_exp.simps)

lemma bop_rhs_wordI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) bop e\<^sub>2) \<leadsto> (BinOp (num \<Colon> sz) bop e\<^sub>2')\<close>
  unfolding word_constructor_exp_def using assms by (rule bop_rhsI)

locale bop_lemmas =
    fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and bop :: BinOp
  assumes bop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 bop e\<^sub>2\<close>
begin

lemma lhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> bop_fun e\<^sub>1' e\<^sub>2\<close>
  using assms unfolding bop_simps by (rule bop_lhsI)

lemma rhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun (Val v\<^sub>1) e\<^sub>2 \<leadsto> bop_fun (Val v\<^sub>1) e\<^sub>2'\<close>
  using assms unfolding bop_simps by (rule bop_rhsI)

lemma rhs_wordI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun (num \<Colon> sz) e\<^sub>2 \<leadsto>  bop_fun (num \<Colon> sz) e\<^sub>2'\<close>
  using assms unfolding bop_simps by (rule bop_rhs_wordI)

end

lemma aop_unk_lhsI: \<open>\<Delta> \<turnstile> (BinOp (unknown[str]: t) (AOp aop) e) \<leadsto> (unknown[str]: t)\<close>
  by (auto simp add: eval_exp.simps)

(* revisit this*)
lemma aop_unk_rhs_wordI: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (AOp aop) (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  by (auto simp add: eval_exp.simps)

locale aop_lemmas =
    fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and aop :: AOp
  assumes aop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (AOp aop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>AOp aop\<close>
  by (standard, rule aop_simps)


lemma unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule aop_unk_lhsI)

lemma unk_rhs_wordI: \<open>\<Delta> \<turnstile> bop_fun (num \<Colon> sz) (unknown[str]: t) \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule aop_unk_rhs_wordI)

end



lemma LOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (unknown[str]: t) (LOp lop) e) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma LOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp lop) (unknown[str]: t)) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

(* TODO can the unreserved syntax just be abbreviations (probable functions?) and attach to exp instead of separate class *)
interpretation plus: aop_lemmas \<open>(+)\<close> \<open>Plus\<close> by (standard, unfold plus_exp.simps, rule)
interpretation minus: aop_lemmas \<open>(-)\<close> \<open>Minus\<close> by (standard, unfold minus_exp.simps, rule)
interpretation times: aop_lemmas \<open>(*)\<close> \<open>Times\<close> by (standard, unfold times_exp.simps, rule)
interpretation divide: aop_lemmas \<open>(div)\<close> \<open>Divide\<close> by (standard, unfold divide_exp.simps, rule)
interpretation mod: aop_lemmas \<open>(mod)\<close> \<open>Mod\<close> by (standard, unfold modulo_exp.simps, rule)
interpretation sdivide: aop_lemmas \<open>(sdiv)\<close> \<open>SDivide\<close> by (standard, unfold sdivide_exp.simps, rule)
interpretation smod: aop_lemmas \<open>(smod)\<close> \<open>SMod\<close> by (standard, unfold smod_exp.simps, rule)
interpretation land: aop_lemmas \<open>(&&)\<close> \<open>And\<close> by (standard, unfold land_exp.simps, rule)
interpretation lor: aop_lemmas \<open>(||)\<close> \<open>Or\<close> by (standard, unfold lor_exp.simps, rule)
interpretation xor: aop_lemmas \<open>(xor)\<close> \<open>Xor\<close> by (standard, unfold xor_exp.simps, rule)
interpretation lsl: aop_lemmas \<open>(<<)\<close> \<open>LShift\<close> by (standard, unfold lsl_exp.simps, rule)
interpretation lsr: aop_lemmas \<open>(>>)\<close> \<open>RShift\<close> by (standard, unfold lsr_exp.simps, rule)
interpretation asr: aop_lemmas \<open>(>>>)\<close> \<open>ARShift\<close> by (standard, unfold asr_exp.simps, rule)

lemmas BOP_LHS = bop_lhsI
lemmas BOP_RHS = bop_rhsI
lemmas BOP_RHS_WORD = bop_rhs_wordI

(* TODO remove *)
lemmas PLUS_RHS = plus.rhsI
lemmas PLUS_RHS_WORD = plus.rhs_wordI
lemmas PLUS_LHS = plus.lhsI

lemma PLUS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  unfolding plus_exp.simps by (auto simp add: bv_plus.simps eval_exp.simps)

lemma MINUS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (cases \<open>num\<^sub>2 \<le> num\<^sub>1\<close>, auto simp add: eval_exp.simps)
  
lemma TIMES: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma DIV: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma SDIV: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma MOD: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma SMOD: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma LSL: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma LSR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma ASR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma LAND: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma LOR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma XOR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma EQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> true\<close>
  by (simp add: bv_eq_def eval_exp.simps)

lemma EQ_DIFF: 
  assumes \<open>(num\<^sub>1 \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz)) \<leadsto> false\<close>
  using assms apply (auto simp add: eval_exp.simps)
  unfolding bv_eq_def  by auto

lemma NEQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> false\<close>
  by (simp add: bv_eq_def eval_exp.simps)

lemma NEQ_DIFF: 
  assumes \<open>(num\<^sub>1 \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz)) (LOp Neq) (num\<^sub>2 \<Colon> sz) \<leadsto> true\<close>
  using assms apply auto
  apply (simp add: bv_eq_def eval_exp.simps)
  by (cases \<open>num\<^sub>1 = num\<^sub>2\<close>, auto)

lemma LESS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma LESS_EQ: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) lteq (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: bv_eq_def eval_exp.simps)

lemma SIGNED_LESS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma SIGNED_LESS_EQ: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) slteq (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (auto simp add: bv_eq_def eval_exp.simps)

lemma UOP: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (UnOp uop e) \<leadsto> (UnOp uop e')\<close>
  using assms by (cases e, auto simp add: eval_exp.simps)

lemma UOP_UNK: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  by (auto simp add: eval_exp.simps)

lemma NOT: \<open>\<Delta> \<turnstile> ~(num \<Colon> sz) \<leadsto> (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
  unfolding BIL_Syntax.not_exp.simps by (auto simp add: eval_exp.simps)

lemma NOT_FALSE: \<open>\<Delta> \<turnstile> ~false \<leadsto> true\<close>
  using bv_negation_false_true NOT by (metis false_word)

lemma NOT_TRUE: \<open>\<Delta> \<turnstile> ~true \<leadsto> false\<close>
  using bv_negation_true_false NOT by (metis true_word)

lemma NEG: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<leadsto> (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
  by (auto simp add: eval_exp.simps)

lemma CONCAT_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<leadsto> (e\<^sub>1 @ e\<^sub>2')\<close>
  using assms unfolding step_pred_exp.simps
  apply (auto simp add: eval_exp.simps)
  apply (simp add: STEP_NOT_EQ)
  by (metis STEP_NOT_REDUCTION)

lemma CONCAT_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<leadsto> (e\<^sub>1' @ (Val v\<^sub>2))\<close>
  using assms unfolding step_pred_exp.simps
  apply (auto simp add: eval_exp.simps)
  apply (simp add: STEP_NOT_EQ)
  by (metis STEP_NOT_REDUCTION)

lemma CONCAT_LHS_WORD: 
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (num \<Colon> sz)) \<leadsto> (e\<^sub>1' @ (num \<Colon> sz))\<close>
  using assms apply (drule_tac CONCAT_LHS)
  unfolding Val_simp_word by (auto simp add: eval_exp.simps)


lemma CONCAT_LHS_UN:
  assumes \<open>type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v\<^sub>2)) \<leadsto> unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms by (cases v\<^sub>2 rule: val_exhaust, auto simp add: eval_exp.simps) 

lemma CONCAT_RHS_UN:
    \<open>\<Delta> \<turnstile> (num \<Colon> sz\<^sub>1) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close>
  by (auto simp add: eval_exp.simps unknown_constructor_exp_def)

lemma CONCAT: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2) \<leadsto> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close>
  by (auto simp add: eval_exp.simps)

lemma EXTRACT: 
  assumes \<open>sz\<^sub>2 \<le> sz\<^sub>1\<close>
    shows \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<leadsto> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)\<close>
  using assms by (auto simp add: eval_exp.simps xtract.simps)

lemma CAST_REDUCE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto> (Cast cast sz e')\<close>
  using assms by (cases e, auto simp add: eval_exp.simps)

lemma CAST_UNK: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma CAST_LOW: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by (auto simp add: xtract.simps eval_exp.simps)

lemma CAST_HIGH: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))\<close>
  by (auto simp add: xtract.simps eval_exp.simps)

lemma CAST_SIGNED: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<leadsto> (exts (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by (auto simp add: sxtract.simps eval_exp.simps)

lemma CAST_UNSIGNED: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by (auto simp add: xtract.simps eval_exp.simps)
  
lemma REDUCE: \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2) \<Longrightarrow> (\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* v) \<Longrightarrow> (\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* v)\<close>
  apply auto
  by (metis STEP_NOT_REDUCTION)

lemma REFL:  \<open>\<Delta> \<turnstile> (Val v) \<leadsto>* v\<close>
  by (auto simp add: eval_exp.simps)

lemma REFL_UNKNOWN[simp]:  \<open>\<Delta> \<turnstile> unknown[str]: t \<leadsto>* unknown[str]: t\<close>
  by auto

lemma REFL_WORD[simp]:  \<open>\<Delta> \<turnstile> (num \<Colon> sz) \<leadsto>* (num \<Colon> sz)\<close>
  by auto

lemma REFL_STORAGE[simp]:  \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v',sz]) \<leadsto>* (v[w \<leftarrow> v',sz])\<close>
  by auto


lemma REFL_TRUE[simp]: \<open>\<Delta>a \<turnstile> true \<leadsto>* true\<close>
  by auto

lemma REFL_FALSE[simp]: \<open>\<Delta>a \<turnstile> false \<leadsto>* false\<close>
  by auto


lemma reflI:
  assumes \<open>e = (Val v)\<close> shows \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
  using assms by (auto simp add: eval_exp.simps)


lemma step_exp_eqI: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz)) \<leadsto> (num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  by (auto simp add: bv_eq_def eval_exp.simps)

method solve_exp = (
  rule NOT_TRUE | rule NOT_FALSE | 
  rule UOP_UNK |

  (rule VAR_IN_TRUE, solve_in_var?) | (rule VAR_IN_FALSE, solve_in_var?) |
  (rule VAR_IN_WORD, solve_in_var?) | (rule VAR_IN_STORAGE, solve_in_var?) |
  (rule VAR_IN_UNKNOWN, solve_in_var?) | (rule VAR_IN, (unfold var_simps)?, solve_in_var?) |

  match conclusion in
    \<open>_ \<turnstile> ~ _ \<leadsto> ~ _\<close> \<Rightarrow> \<open>unfold BIL_Syntax.not_exp.simps, rule UOP, solve_exp\<close>
  
  \<bar> \<open>_ \<turnstile> pad:_[_ \<Colon> _] \<leadsto> ext _ \<Colon> _ \<sim> hi : _ - 1 \<sim> lo : 0\<close> \<Rightarrow> \<open>rule CAST_UNSIGNED\<close>
  \<bar> \<open>_ \<turnstile> extend:_[_ \<Colon> _] \<leadsto> exts _ \<Colon> _ \<sim> hi : _ - 1 \<sim> lo : 0\<close> \<Rightarrow> \<open>rule CAST_SIGNED\<close>
  \<bar> \<open>_ \<turnstile> low:_[_ \<Colon> _] \<leadsto> ext _ \<Colon> _ \<sim> hi : _ - 1 \<sim> lo : 0\<close> \<Rightarrow> \<open>rule CAST_LOW\<close>
  \<bar> \<open>_ \<turnstile> high:_[_ \<Colon> _] \<leadsto> ext _ \<Colon> _ \<sim> hi : _ - 1 \<sim> lo : (_ - _)\<close> \<Rightarrow> \<open>rule CAST_HIGH\<close>
  \<bar> \<open>_ \<turnstile> _:_[_] \<leadsto> _\<close> \<Rightarrow> \<open>rule CAST_REDUCE, solve_exp\<close>

  \<comment>\<open>Load operations\<close>
  \<bar> \<open>_ \<turnstile> _[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v \<Colon> sz), sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), _]:usz \<leadsto> (num\<^sub>v \<Colon> sz)\<close> for num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>v sz \<Rightarrow> \<open>rule LOAD_BYTE_WORD\<close>
  \<bar> \<open>_ \<turnstile> _[(_ \<Colon> _) \<leftarrow> _, _][_ \<leftarrow> _, _][(_ \<Colon> _), _]:u_ \<leadsto> (_[(_ \<Colon> _) \<leftarrow> _, _][(_ \<Colon> _), _]:u_)\<close> \<Rightarrow> \<open>rule LOAD_BYTE_FROM_NEXT_MEM, linarith?\<close>
  \<bar> \<open>_ \<turnstile> _[_ \<Colon> _, _]:u_ \<leadsto> (_[_ \<Colon> _, _]:u_)\<close> \<Rightarrow> \<open>rule LOAD_STEP_MEM_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [succ (_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _) \<leadsto> _ with [succ (_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _)\<close> \<Rightarrow> \<open>rule STORE_STEP_MEM_SUCC, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [succ (_ \<Colon> _), _]:u_ \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _ \<leadsto> _ with [succ (_ \<Colon> _), _]:u_ \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _\<close> \<Rightarrow> \<open>rule STORE_STEP_MEM_SUCC_XTRACT, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _[_, _]:u_ \<leadsto> (_[_, _]:u_)\<close> \<Rightarrow> \<open>rule LOAD_STEP_ADDR, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _[_, _]:u_ \<leadsto> (_[_, el]:u_) @ (_[_, _]:u_)\<close> \<Rightarrow> \<open>rule LOAD_WORD_EL_MEM, linarith, linarith\<close>

  \<comment>\<open>Concat operations\<close>
  \<bar> \<open>_ \<turnstile> (_ \<Colon> _) @ (_ \<Colon> _) \<leadsto> (_ \<Colon> _) \<cdot> (_ \<Colon> _)\<close> \<Rightarrow> \<open>rule CONCAT\<close>
  \<bar> \<open>_ \<turnstile> (_ @ (_ \<Colon> _)) \<leadsto> (_ @ (_ \<Colon> _))\<close> \<Rightarrow> \<open>rule CONCAT_LHS_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> (_ @ _) \<leadsto> (_ @ _)\<close> \<Rightarrow> \<open>rule CONCAT_RHS, solve_exp\<close>


  \<comment>\<open>Store operations\<close>
  \<bar> \<open>_ \<turnstile> (Val _) with [_ \<Colon> _, el]:u_ \<leftarrow> _ \<Colon> _ \<leadsto> _ with [succ (_ \<Colon> _), el]:u_ - _ \<leftarrow> high:_ - _[_ \<Colon> _]\<close> \<Rightarrow> \<open>rule STORE_WORD_EL_WORD, linarith, linarith, blast, clarify\<close>
  \<bar> \<open>_ \<turnstile> _[_ \<Colon> _ \<leftarrow> _ \<Colon> _, _] with [_ \<Colon> _, el]:u_ \<leftarrow> _ \<Colon> _ \<leadsto> _ with [succ (_ \<Colon> _), el]:u_ - _ \<leftarrow> high:_ - _[_ \<Colon> _]\<close> \<Rightarrow> \<open>rule STORE_WORD_EL_WORD_MEM, linarith, linarith, clarify\<close>

  \<bar> \<open>_ \<turnstile> (Val _) with [(_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _) \<leadsto> _[(_ \<Colon> _) \<leftarrow> (_ \<Colon> _), _]\<close> \<Rightarrow> \<open>rule STORE_WORD, linarith, linarith\<close>
  \<bar> \<open>_ \<turnstile> _[(_ \<Colon> _) \<leftarrow> (_ \<Colon> _), _] with [(_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _) \<leadsto> _[(_ \<Colon> _) \<leftarrow> (_ \<Colon> _), _]\<close> \<Rightarrow> \<open>rule STORE_WORD_IN_MEM, linarith\<close>

  \<bar> \<open>_ \<turnstile> (Val _ with [(_ \<Colon> _), _]:u_ \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _) \<leadsto> (_[(_ \<Colon> _) \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _, _])\<close> \<Rightarrow> \<open>rule STORE_XTRACT, linarith, linarith, blast\<close>
  \<bar> \<open>_ \<turnstile> (_[(_ \<Colon> _) \<leftarrow> (_ \<Colon> _), _] with [(_ \<Colon> _), _]:u_ \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _) \<leadsto> (_[(_ \<Colon> _) \<leftarrow> ext (_ \<Colon> _) \<sim> hi : _ \<sim> lo : _, _])\<close> \<Rightarrow> \<open>rule STORE_XTRACT_IN_MEM, linarith, linarith\<close>

  \<bar> \<open>_ \<turnstile> _ with [(Val _), _]:u_ \<leftarrow> (Val _) \<leadsto> _ with [(Val _), _]:u_ \<leftarrow> (Val _)\<close> \<Rightarrow> \<open>rule STORE_STEP_MEM, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [(_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _) \<leadsto> _ with [(_ \<Colon> _), _]:u_ \<leftarrow> (_ \<Colon> _)\<close> \<Rightarrow> \<open>rule STORE_STEP_MEM_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [_, _]:u_ \<leftarrow> (Val _) \<leadsto> _ with [_, _]:u_ \<leftarrow> (Val _)\<close> \<Rightarrow> \<open>rule STORE_STEP_ADDR, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [_, _]:u_ \<leftarrow> (_ \<Colon> _) \<leadsto> _ with [_, _]:u_ \<leftarrow> (_ \<Colon> _)\<close> \<Rightarrow> \<open>rule STORE_STEP_ADDR_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ with [_, _]:u_ \<leftarrow> _ \<leadsto> _ with [_, _]:u_ \<leftarrow> _\<close> \<Rightarrow> \<open>rule STORE_STEP_VAL, solve_exp\<close>

  \<comment>\<open>Binary Operations\<close>
  \<bar> \<open>_ \<turnstile> (_ \<Colon> _) + (_ \<Colon> _) \<leadsto> ((_ \<Colon> _) +\<^sub>b\<^sub>v (_ \<Colon> _))\<close> \<Rightarrow> \<open>rule PLUS\<close>
  \<bar> \<open>_ \<turnstile> (_ \<Colon> _) + _ \<leadsto> ((_ \<Colon> _) + _)\<close> \<Rightarrow> \<open>rule PLUS_RHS_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> _ + _ \<leadsto> (_ + _)\<close> \<Rightarrow> \<open>rule PLUS_LHS, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> BinOp (_ \<Colon> _) (LOp Eq) (_ \<Colon> _) \<leadsto> (_ \<Colon> _) =\<^sub>b\<^sub>v (_ \<Colon> _)\<close> \<Rightarrow> \<open>rule step_exp_eqI\<close>
  \<bar> \<open>_ \<turnstile> BinOp (_ \<Colon> _) _ _ \<leadsto> BinOp (_ \<Colon> _) _ _\<close> \<Rightarrow> \<open>rule BOP_RHS_WORD, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> BinOp (Val _) _ _ \<leadsto> BinOp (Val _) _ _\<close> \<Rightarrow> \<open>rule BOP_RHS, solve_exp\<close>
  \<bar> \<open>_ \<turnstile> BinOp _ _ _ \<leadsto> BinOp _ _ _\<close> \<Rightarrow> \<open>rule BOP_LHS, solve_exp\<close>
  \<bar> _ \<Rightarrow> \<open>succeed\<close>
)

end
