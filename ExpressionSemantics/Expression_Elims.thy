
section \<open>Introduction rules\<close>

theory Expression_Elims
  imports Expression_Rules
          
begin


                                           
lemma "\<Delta> \<turnstile> (unknown[str]: t)[Val v, en]:usz \<Rrightarrow>* unknown[str]: imm\<langle>sz\<rangle>"
  apply (rule step_exps_reduce_singleI)
  by (rule LoadUnMem)



lemma step_exp_var_inE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> e\<close>
      and \<open>((id' :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>e = (Val v)\<close>
using assms(1) proof (rule VarE)
  fix val 
  assume val_e: \<open>e = Val val\<close>
  assume \<open>((id' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  then have \<open>val = v\<close>
  using assms(2) by (rule var_in_deterministic)
  thus \<open>e = Val v\<close>
    using val_e by blast
qed (use assms(2) in \<open>simp_all add: var_in_dom_\<Delta>\<close>)

lemma step_exp_var_in_wordE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> e\<close>
      and \<open>((id' :\<^sub>t t), (num \<Colon> sz)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>e = (num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def using assms by (rule step_exp_var_inE)

lemma step_exp_var_in_trueE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> e\<close>
      and \<open>((id' :\<^sub>t t), true) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>e = true\<close>
  unfolding true_exp_def using assms by (rule step_exp_var_inE)
(*
lemma step_exp_var_in_falseE:
  assumes \<open>(id' :\<^sub>t t, false) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>\<Delta> \<turnstile> id' :\<^sub>t t \<Rrightarrow> false\<close>
  unfolding false_exp_def using assms by (rule step_exp_var_inE)

lemma step_exp_var_in_storageE:
  assumes \<open>((id' :\<^sub>t t), v[w \<leftarrow> v', sz]) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> (v[w \<leftarrow> v', sz])\<close>
  using assms by (auto simp add: val_var_in_vars.simps)

lemma step_exp_var_in_unknownE:
  assumes \<open>((id' :\<^sub>t t), (unknown[str]: t)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> unknown[str]: t\<close>
  using assms by (auto simp add: val_var_in_vars.simps)
*)
lemma step_exp_var_unknownE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<Rrightarrow> e\<close>
      and \<open>(id' :\<^sub>t t) \<notin> dom \<Delta>\<close>
    shows \<open>\<exists>str. e = unknown[str]: t\<close>
using assms(1) proof (rule VarE)
  fix val assume \<open>(id' :\<^sub>t t, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  thus ?thesis
    using var_in_dom_\<Delta> assms(2) by simp
next
  fix str 
  assume unknown_e: \<open>e = unknown[str]: t\<close>
  thus \<open>\<exists>str. e = unknown[str]: t\<close>
    by (rule exI[of _ str])
qed


lemma step_exp_load_byteE: 
  assumes \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> e\<close> 
    shows \<open>e = Val v'\<close>
  using assms apply (rule LoadByteE)
  apply simp_all
  using storage_constructor_exp_def by fastforce+

lemma step_exp_load_byte_from_nextE: 
  assumes \<open>\<Delta> \<turnstile> v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<Rrightarrow> e\<close> 
      and \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>e = (Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz\<close>
  using assms(1) apply (rule LoadByteFromNextE)
  using assms(2) apply simp_all
  using storage_constructor_exp_def by fastforce+

lemma step_exp_load_un_addrE: 
  assumes \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<Rrightarrow> e\<close> 
    shows \<open>e = unknown[str]: imm\<langle>sz'\<rangle>\<close>
  using assms(1) apply (rule LoadUnAddrE)
  by simp_all

lemma step_exp_load_un_memE: 
  assumes \<open>\<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[Val v, ed]:usz\<^sub>m\<^sub>e\<^sub>m \<Rrightarrow> e\<close> 
    shows \<open>e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms(1) apply (rule LoadUnMemE)
  apply simp_all
  using unknown_constructor_exp_def by force+

lemma step_exp_load_word_beE: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> e\<close>
      and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close>
    shows \<open>e = ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) 
           \<or> (\<exists>str. v = unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<and> e = unknown[str]: imm\<langle>sz\<rangle>)\<close>
  using assms(1) apply (rule LoadWordBeE)
  using assms(2-) unfolding storage_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_load_word_elE: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> e\<close>
      and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close>
    shows \<open>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m) 
           \<or> (\<exists>str. v = unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<and> e = unknown[str]: imm\<langle>sz\<rangle>)\<close>
  using assms(1) apply (rule LoadWordElE)
  using assms(2-) unfolding storage_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_load_storage_word_elE: 
  assumes \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> e\<close>
      and \<open>type (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close>
    shows \<open>e = (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) @ (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (insert assms)
  unfolding storage_constructor_exp_def apply (drule step_exp_load_word_elE, blast, linarith)
  by auto


lemma step_exp_load_step_addrE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e\<^sub>1 \<noteq> e\<^sub>1' \<and> e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close>
  using assms(1) apply (rule LoadStepMemE)
  using assms(2) unfolding storage_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_load_step_memE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e\<^sub>2 \<noteq> e\<^sub>2' \<and> e = (e\<^sub>1[e\<^sub>2', ed]:usz)\<close>
  using assms(1) apply (rule LoadStepAddrE)
  using assms(2-) unfolding storage_constructor_exp_def unknown_constructor_exp_def by simp_all

(*

lemma LOAD_STEP_MEM_WORD:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> (e\<^sub>1'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  unfolding word_constructor_exp_def using assms by (rule LOAD_STEP_MEM)

lemma LOAD_BYTE:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> (Val v')\<close>
  by (auto simp add: eval_exp.simps) 

lemma LOAD_BYTE_WORD:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v \<Colon> sz), sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> (num\<^sub>v \<Colon> sz)\<close>
  unfolding word_constructor_exp_def[of num\<^sub>v] by (rule LOAD_BYTE)

lemma LOAD_BYTE_FROM_NEXT:
  assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
  shows \<open>\<Delta> \<turnstile> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms apply auto
  subgoal
    apply (rule val_exhaust[of v])
    apply (simp_all add: eval_exp.simps)
    by (metis Type.inject(2) load.simps(1) type.simps(1) word_exhaust )
  .

lemma LOAD_UN_ADDR: \<open>\<Delta> \<turnstile> e\<^sub>1[unknown[str]: imm\<langle>sz'\<rangle>, ed]:usz \<Rrightarrow> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma LOAD_UN_MEM: \<open>\<Delta> \<turnstile> ((unknown[str]: t)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (auto simp add: eval_exp.simps)

lemma LOAD_WORD_BE:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> 
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> 
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
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
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
    shows \<open>\<Delta> \<turnstile> (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  unfolding storage_constructor_exp_def using assms(1,2) apply (rule LOAD_WORD_EL)
  using assms(3) by auto


lemma LOAD_WORD_EL_MEM:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  unfolding storage_constructor_exp_def using assms apply (rule LOAD_WORD_EL)
  by (rule type_storageI)

lemma LOAD_WORD_EL_MEM_SUCC:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM)

lemma LOAD_WORD_EL_MEM_SUCC2:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC)

lemma LOAD_WORD_EL_MEM_SUCC3:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC2)

lemma LOAD_WORD_EL_MEM_WORD_ADDR:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> (((v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms apply (frule_tac LOAD_WORD_EL[of _ _ \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  by (simp_all add: eval_exp.simps)

lemma LOAD_BYTE_FROM_NEXT_MEM_INTER:
  assumes \<open>\<exists>num. w = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> and \<open>\<exists>num. w' = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<and> num \<noteq> num\<^sub>3\<close>
    shows \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v\<^sub>1, sz][w' \<leftarrow> v\<^sub>2, sz])[(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> (v[w \<leftarrow> v\<^sub>1, sz][(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms 
  apply (elim exE conjE)
  by (metis LOAD_BYTE_FROM_NEXT storage_constructor_exp_def type.simps(1))

lemma LOAD_BYTE_FROM_NEXT_MEM:
  assumes \<open>num\<^sub>2 \<noteq> num\<^sub>3\<close>
    shows \<open>\<Delta> \<turnstile> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz][(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, sz])[(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz][(num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms apply (drule_tac LOAD_BYTE_FROM_NEXT[of _ _ \<open>v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, sz]\<close>])
  apply simp
  by (simp add: storage_constructor_exp_def)
*)

lemma step_exp_store_valE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leftarrow> (Val v')) \<Rrightarrow> e\<close>
      and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
    shows \<open>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])\<close>
  using assms(1) apply (rule StoreValE)
  using assms(2) by simp_all

lemma step_exp_store_un_addrE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: t', ed]:usz' \<leftarrow> (Val v')) \<Rrightarrow> e\<close>
      and \<open>type v = t\<close>
    shows \<open>e = unknown[str]: t\<close>
  using assms(1) apply (rule StoreUnAddrE) using StoreUnAddrE
  using assms(2) by simp_all

lemma store_neq_plus[simp]: \<open>(e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) + (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding plus_exp.simps by simp

lemma step_exp_store_step_valE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>3 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>3'. \<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3' \<and> e\<^sub>3 \<noteq> e\<^sub>3' \<and> e = (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close>
  using assms(1) apply (rule StoreStepValE)
  using assms(2-) unfolding storage_constructor_exp_def unknown_constructor_exp_def apply simp_all
  using step_exp_neq by blast

lemma step_exp_store_step_addrE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close> 
    shows \<open>\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e\<^sub>2 \<noteq> e\<^sub>2' \<and> e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close>
  using assms(1) apply (rule StoreStepAddrE)
  using assms(2-) unfolding storage_constructor_exp_def unknown_constructor_exp_def apply simp_all
  using step_exp_neq by blast

lemma step_exp_store_step_memE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e\<^sub>1 \<noteq> e\<^sub>1' \<and> e = (e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3))\<close>
  using assms(1) apply (rule StoreStepMemE)
  using assms(2) unfolding storage_constructor_exp_def unknown_constructor_exp_def apply simp_all
  using step_exp_neq by blast

(*

lemma STORE_STEP_VAL:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> 
  using assms by (cases e\<^sub>3, auto simp add: eval_exp.simps)

lemma STORE_STEP_ADDR:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>2, auto simp add: eval_exp.simps) 

lemma STORE_STEP_ADDR_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz')) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz'))\<close> 
  using assms STORE_STEP_ADDR word_constructor_exp_def by presburger

lemma STORE_STEP_MEM:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>1, auto simp add: eval_exp.simps) 

lemma STORE_WORD_BE:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms unfolding xtract.simps apply (auto simp add: eval_exp.simps)
  apply (cases val rule: val_exhaust, auto)
  unfolding SUCC xtract.simps bv_plus.simps by auto

lemma STORE_WORD_EL:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms unfolding xtract.simps apply (auto simp add: eval_exp.simps)
  apply (cases val rule: val_exhaust, auto)
  unfolding SUCC xtract.simps bv_plus.simps by auto

lemma STORE_VAL:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type v' = imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<Rrightarrow> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms by (cases ed, auto simp add: eval_exp.simps)
  
lemma STORE_UN_ADDR:
  assumes \<open>type v = t\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>, ed]:usz' \<leftarrow> (Val v')) \<Rrightarrow> (unknown[str]: t)\<close>
  using assms by (cases t, auto simp add: eval_exp.simps)

lemma STORE_STEP_MEM_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<Rrightarrow> e\<^sub>1' with [(num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
  using assms unfolding word_constructor_exp_def by (rule STORE_STEP_MEM)

lemma STORE_WORD_EL_WORD:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (num' \<Colon> sz)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (num' \<Colon> sz)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (num' \<Colon> sz)))\<close>
  using assms STORE_WORD_EL by (metis Val_simp_word type.simps(2))

lemma STORE_WORD_EL_WORD_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
      and \<open>e\<^sub>1 = (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (num' \<Colon> sz)))\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (num' \<Colon> sz)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (num' \<Colon> sz)))\<close>
  using assms apply (drule_tac STORE_WORD_EL_WORD[of _ _ \<open>v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  apply simp
  apply simp
  apply simp
  using STORE_WORD_EL_WORD assms(1) storage_constructor_exp_def type.simps(1) by presburger

lemma STORE_WORD:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) \<Rrightarrow> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms apply (drule_tac STORE_VAL[of _ _ _ \<open>(num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close> _ num ed])
  by (auto simp add: eval_exp.simps)

lemma STORE_WORD_IN_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) \<Rrightarrow> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms apply (drule_tac STORE_WORD[of \<open>v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>, rotated])
  unfolding Val_simp_storage by simp_all

lemma STORE_STEP_MEM_BV_ADD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4) \<Rrightarrow> e\<^sub>1' with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4)\<close>
  using assms unfolding bv_plus.simps by (rule STORE_STEP_MEM_WORD)

lemma STORE_STEP_MEM_SUCC:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<Rrightarrow> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
  using assms unfolding succ.simps by (rule STORE_STEP_MEM_BV_ADD)

lemma STORE_STEP_MEM_SUCC_XTRACT:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz'' \<Rrightarrow> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz''\<close>
  using assms unfolding xtract.simps by (rule STORE_STEP_MEM_SUCC)

lemma STORE_XTRACT:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<Rrightarrow> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  unfolding xtract.simps assms(2)[symmetric]
  apply (rule STORE_WORD)
  using assms(1,3) by blast+

lemma STORE_XTRACT_IN_MEM:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<Rrightarrow> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms(1) unfolding xtract.simps assms(2)[symmetric]
  by (rule STORE_WORD_IN_MEM)
*)

text \<open>Let steps\<close>

lemma let_neq_plus[simp]: \<open>exp.Let var e\<^sub>1 e\<^sub>2 \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) + (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding plus_exp.simps by simp

lemma step_exp_step_letE:
  assumes \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = (Let var e\<^sub>1' e\<^sub>2)\<close>
  using assms(1) apply (rule LetStepE)
  using assms(2) by simp_all

lemma step_exp_letE:
  assumes \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<Rrightarrow> e'\<close>
    shows \<open>e' = [v\<sslash>var]e\<close>
  using assms apply (rule LetE)
  by simp_all

text \<open>Ite steps\<close>

lemma step_exp_if_trueE:
  assumes \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
    shows \<open>e = Val v\<^sub>2\<close>
  using assms apply (rule IfTrueE)
  by simp_all

lemma step_exp_if_falseE:
  assumes \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
    shows \<open>e = Val v\<^sub>3\<close>
  using assms apply (rule IfFalseE)
  by simp_all

lemma step_exp_if_unknownE:
  assumes \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
    shows \<open>e = unknown[str]: (type v\<^sub>2)\<close>
  using assms apply (rule IfUnknownE)
  by simp_all

lemma step_exp_if_step_elseE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>3 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>3'. \<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3' \<and> e = (ite e\<^sub>1 e\<^sub>2 e\<^sub>3')\<close>
  using assms(1) apply (rule IfStepElseE)
  using assms(2-) by simp_all

lemma step_exp_if_step_thenE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e = (ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3))\<close>
  using assms(1) apply (rule IfStepElseE)
  using assms(2-) by simp_all

lemma step_exp_if_step_condE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = (ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3))\<close>
  using assms(1) apply (rule IfStepCondE)
  using assms(2-) apply simp_all
  unfolding true_exp_def false_exp_def apply simp_all
  by (metis Val_simp_unknown)

text \<open>Uop steps\<close>

lemma step_exp_uopE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp uop e\<^sub>1) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = (UnOp uop e\<^sub>1')\<close>
  using assms(1) apply (rule UopE)
  using assms(2-) apply simp_all
  apply (metis Val_simp_unknown)
  apply (metis Val_simp_word)
  using word_constructor_exp_def by auto

lemma step_exp_uop_unkE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp uop unknown[str]: t) \<Rrightarrow> e\<close>
    shows \<open>e = unknown[str]: t\<close>
  using assms(1) apply (rule UopUnkE)
  by simp_all

lemma step_exp_notE: 
  assumes \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = ~\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  using assms(1) apply (rule NotE)
  by simp_all

lemma step_exp_negE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = -\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  using assms(1) apply (rule NegE)
  by simp_all

text \<open>Concat steps\<close>

lemma step_exp_concat_rhsE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e = (e\<^sub>1 @ e\<^sub>2')\<close>
  using assms(1) apply (rule ConcatRhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_concat_lhsE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = (e\<^sub>1' @ (Val v\<^sub>2))\<close>
  using assms(1) apply (rule ConcatLhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_concat_rhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) @ unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<Rrightarrow> e\<close> and \<open>type v = imm\<langle>sz\<^sub>1\<rangle>\<close>
    shows \<open>(\<exists>str. v = unknown[str]: imm\<langle>sz\<^sub>1\<rangle> \<and> e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>) \<or> (e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close>
  using assms(1) apply (rule ConcatRhsUnE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def apply simp_all
  by force

lemma step_exp_concat_lhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<Rrightarrow> e\<close> and \<open>type v = imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>(\<exists>str. v = (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<and> e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>) \<or> (e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close>
  using assms(1) apply (rule ConcatLhsUnE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def apply simp_all
  by force

lemma step_exp_concatE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using assms(1) apply (rule ConcatE)
  by simp_all

text \<open>Extract steps\<close>

lemma step_exp_extractE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)] \<Rrightarrow> e\<close>
    shows \<open>e = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<close>
  using assms(1) apply (rule ExtractE)
  by simp_all

lemma step_exp_extract_unE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t] \<Rrightarrow> e\<close>
    shows \<open>e = unknown[str]: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle>\<close>
  using assms(1) apply (rule ExtractUnE)
  by simp_all

lemma step_exp_extract_reduceE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e\<^sub>1] \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = extract:sz\<^sub>1:sz\<^sub>2[e\<^sub>1']\<close>
  using assms(1) apply (rule ExtractReduceE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all

text \<open>Cast steps\<close>

lemma step_exp_cast_lowE:
  assumes \<open>\<Delta> \<turnstile> low:sz[(num \<Colon> sz')] \<Rrightarrow> e\<close>
    shows \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (rule CastLowE)
  by simp_all

lemma step_exp_cast_highE:
  assumes \<open>\<Delta> \<turnstile> high:sz[(num \<Colon> sz')] \<Rrightarrow> e\<close>
    shows \<open>e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz)\<close>
  using assms(1) apply (rule CastHighE)
  by simp_all

lemma step_exp_cast_signedE:
  assumes \<open>\<Delta> \<turnstile> extend:sz[(num \<Colon> sz')] \<Rrightarrow> e\<close>
    shows \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (rule CastSignedE)
  by simp_all

lemma step_exp_cast_unsignedE:
  assumes \<open>\<Delta> \<turnstile> pad:sz[(num \<Colon> sz')] \<Rrightarrow> e\<close>
    shows \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (rule CastUnsignedE)
  by simp_all

lemma step_exp_cast_unknownE:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<Rrightarrow> e\<close>
    shows \<open>e = unknown[str]: imm\<langle>sz\<rangle>\<close>
  using assms(1) apply (rule CastUnkE)
  by simp_all

lemma step_exp_cast_reduceE:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = (Cast cast sz e\<^sub>1')\<close>
  using assms(1) apply (rule CastReduceE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all

text \<open>BOP steps\<close>

lemma step_exp_bop_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close> and \<open>\<forall>str t. v \<noteq> unknown[str]: t\<close>
    shows \<open>\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e = BinOp (Val v) bop e\<^sub>2'\<close>
  using assms(1) apply (rule BopRhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def plus_exp.simps by simp_all

lemma step_exp_bop_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<Rrightarrow> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = BinOp e\<^sub>1' bop e\<^sub>2\<close>
  using assms(1) apply (rule BopLhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def plus_exp.simps by simp_all

lemma step_exp_aop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e\<^sub>2 \<Rrightarrow> e\<close>
  shows \<open>(\<exists>str' t'. e\<^sub>2 = (unknown[str']: t') \<and> e = unknown[str']: t') 
           \<or> (e = unknown[str]: t)
           \<or> (\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e = BinOp (unknown[str]: t) (AOp aop) e\<^sub>2')\<close>
  using assms apply (elim AopUnkRhsE)
  subgoal for e\<^sub>2'
    apply (intro disjI2)
    apply (intro conjI exI[of _ e\<^sub>2'])
    apply assumption
    by simp
  apply simp
  subgoal by (rule disjI2, rule disjI1)
  subgoal for str' t'
    apply (intro disjI1)
    by (rule exI[of _ str'], rule exI[of _ t'], intro conjI)
  subgoal
    unfolding plus_exp.simps by simp
  .

lemma step_exp_aop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (AOp aop) unknown[str]: t \<Rrightarrow> e\<close>
    shows \<open>(\<exists>str' t'. e\<^sub>1 = (unknown[str']: t') \<and> e = unknown[str']: t') 
           \<or> (e = unknown[str]: t)
           \<or> (\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = BinOp e\<^sub>1' (AOp aop) (unknown[str]: t))\<close>
  using assms apply (rule AopUnkLhsE)
  apply simp
  subgoal for e\<^sub>1'
    apply (intro disjI2)
    apply (intro conjI exI[of _ e\<^sub>1'])
    apply assumption
    by simp
  apply simp
  subgoal by (rule disjI2, rule disjI1)
  subgoal
    unfolding plus_exp.simps by simp
  .

lemma step_exp_lop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e\<^sub>2 \<Rrightarrow> e\<close>
    shows \<open>(\<exists>str' t'. e\<^sub>2 = (unknown[str']: t') \<and> e = unknown[str']: imm\<langle>1\<rangle>) 
           \<or> (e = unknown[str]: imm\<langle>1\<rangle>)
           \<or> (\<exists>e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<and> e = BinOp (unknown[str]: t) (LOp lop) e\<^sub>2')\<close>
  using assms apply (elim LopUnkRhsE)
  subgoal for e\<^sub>2'
    apply (intro disjI2)
    apply (intro conjI exI[of _ e\<^sub>2'])
    apply assumption
    by simp
  apply simp
  subgoal unfolding One_nat_def by (rule disjI2, rule disjI1)
  subgoal for str' t'
    unfolding One_nat_def
    apply (intro disjI1)
    by (rule exI[of _ str'], rule exI[of _ t'], intro conjI)
  subgoal
    unfolding plus_exp.simps by simp
  .

lemma step_exp_lop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (LOp lop) unknown[str]: t \<Rrightarrow> e\<close>
    shows \<open>(\<exists>str' t'. e\<^sub>1 = (unknown[str']: t') \<and> e = unknown[str']: imm\<langle>1\<rangle>) 
           \<or> (e = unknown[str]: imm\<langle>1\<rangle>)
           \<or> (\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<and> e = BinOp e\<^sub>1' (LOp lop) (unknown[str]: t))\<close>
  using assms apply (rule LopUnkLhsE)
  apply simp
  subgoal for e\<^sub>1'
    apply (intro disjI2)
    apply (intro conjI exI[of _ e\<^sub>1'])
    apply assumption
    by simp
  subgoal for str' t'
    unfolding One_nat_def
    apply (intro disjI1)
    by (rule exI[of _ str'], rule exI[of _ t'], intro conjI)    
  subgoal unfolding One_nat_def by (rule disjI2, rule disjI1)
  subgoal unfolding plus_exp.simps by simp
  .

lemma step_exp_plusE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule PlusE)
  unfolding bv_plus.simps plus_exp.simps by auto

lemma step_exp_minusE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule MinusE)
  unfolding plus_exp.simps by auto

lemma step_exp_timesE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule TimesE)
  unfolding plus_exp.simps by auto

lemma step_exp_divE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule DivE)
  unfolding plus_exp.simps by auto

lemma step_exp_sdivE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule SDivE)
  unfolding plus_exp.simps by auto

lemma step_exp_modE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule ModE)
  unfolding plus_exp.simps by auto

lemma step_exp_smodE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule SModE)
  unfolding plus_exp.simps by auto

lemma step_exp_lslE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule LslE)
  unfolding plus_exp.simps by auto

lemma step_exp_lsrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule LsrE)
  unfolding plus_exp.simps by auto

lemma step_exp_asrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule AsrE)
  unfolding plus_exp.simps by auto

lemma step_exp_landE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule LAndE)
  unfolding plus_exp.simps by auto

lemma step_exp_lorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule LOrE)
  unfolding plus_exp.simps by auto

lemma step_exp_xorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule XOrE)
  unfolding plus_exp.simps by auto

lemma step_exp_eq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = true\<close>
  using assms apply (rule EqSameE)
  unfolding plus_exp.simps by auto

lemma step_exp_eq_diffE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close> and \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true\<close>
    shows \<open>e = false\<close>
  using assms(1) apply (rule EqDiffE)
  using assms(2-)   unfolding plus_exp.simps by auto


lemma step_exp_neq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = false\<close>
  using assms apply (rule NeqSameE)
  unfolding plus_exp.simps by auto

lemma step_exp_neq_diffE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close> and \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true\<close>
    shows \<open>e = true\<close>
  using assms(1) apply (rule NeqDiffE)
  using assms(2-)   unfolding plus_exp.simps by auto


lemma step_exp_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule LessE)
  unfolding plus_exp.simps by auto

lemma step_exp_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) apply (rule LessEqE)
  unfolding plus_exp.simps by auto

lemma step_exp_signed_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms apply (rule SignedLessE)
  unfolding plus_exp.simps by auto

lemma step_exp_signed_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
    shows \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) apply (rule SignedLessEqE)
  unfolding plus_exp.simps by auto






lemma step_exps_valE:
  assumes \<open>\<Delta> \<turnstile> (Val v) \<Rrightarrow>* e\<close>
    shows \<open>e = (Val v)\<close>
  using assms step_exp_not_val step_exps_reduceE by blast


lemma step_exps_unknownE:
  assumes \<open>\<Delta> \<turnstile> unknown[str]: t \<Rrightarrow>* e'\<close>
    shows \<open>e' = unknown[str]: t\<close>
  apply (insert assms)
  unfolding unknown_constructor_exp_def
  by (rule step_exps_valE, assumption)



(*
lemma refl8_load_unknown_skip64I:
  assumes \<open>\<Delta> \<turnstile> (Val v\<^sub>1)[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<Rrightarrow>* (Val v\<^sub>4)\<close> 
      and \<open>type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and \<open>type (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, 8]) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and \<open>w\<^sub>2 \<noteq> (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
      and \<open>w\<^sub>2 \<noteq> succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))))\<close>
    shows \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<Rrightarrow>* (Val v\<^sub>4)\<close>
  apply (insert assms)
  apply (cases w\<^sub>2 rule: word_exhaust, clarify)
  apply (drule step_exps_reduceE, simp, elim exE conjE)
  apply (drule step_exp_load_word_elE, assumption, linarith)
  apply auto
  subgoal sorry
  subgoal for num str
    apply (drule step_exps_unknownE, auto)
    apply (rule Reduce[of _ _ \<open>(unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(64 - 8)) @ (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8)\<close>])
    unfolding storage_constructor_exp_def
    apply (rule LoadWordEl, linarith)
    apply solve_type_storage
    apply auto

    using step_exp_load_un_memE

    sorry
  sorry


lemma refl8_load_storage_skip16I:
  assumes \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<Rrightarrow>* (Val v\<^sub>4)\<close> 
      and \<open>w\<^sub>2 \<noteq> (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
      and \<open>w\<^sub>2 \<noteq> succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
    shows \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][w\<^sub>2 \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<Rrightarrow>* (Val v\<^sub>4)\<close>





lemma refl8_load_storage_skip64I:
  assumes \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<Rrightarrow>* (Val v\<^sub>4)\<close> 
      and \<open>type (v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][w\<^sub>2 \<leftarrow> v\<^sub>3, 8]) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and \<open>type (v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8]) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and \<open>w\<^sub>2 \<noteq> (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
      and \<open>w\<^sub>2 \<noteq> succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))))\<close>
    shows \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][w\<^sub>2 \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<Rrightarrow>* (Val v\<^sub>4)\<close>
  apply (insert assms(1-3))
  apply (cases w\<^sub>1 rule: word_exhaust, auto)
  apply (cases w\<^sub>2 rule: word_exhaust, auto)
  subgoal for num\<^sub>1 num\<^sub>2
    apply (drule step_exps_reduceE, simp, elim exE conjE)
    apply (drule step_exp_load_storage_word_elE)
    using assms(3) apply blast
    apply linarith
    apply auto
    apply (drule step_exps_reduceE, metis concat.not_val, elim exE conjE)
    apply (drule step_exp_concat_rhsE, blast, clarify)
    apply (rule Reduce[of _ _ \<open>((v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8])[succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(64 - 8)) @ ((v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8])[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8)\<close>])
    unfolding storage_constructor_exp_def
    apply (rule LoadWordEl, linarith, simp)
    unfolding storage_constructor_exp_def[symmetric]
    apply auto
    apply (rule Reduce[of _ _ \<open>((v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8])[succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56) @ ((v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8])[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8)\<close>])
    apply (rule ConcatRhs)
    unfolding storage_constructor_exp_def[of \<open>v\<^sub>1\<close>]
    apply (rule LoadByteFromNext)
    unfolding storage_constructor_exp_def[symmetric]
    using assms(4) apply simp
    subgoal for e\<^sub>2'
      apply (rule Reduce[of _ _ \<open>(((v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8])[succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56) @ e\<^sub>2')\<close>])
      apply (rule ConcatRhs)
      apply assumption
      apply (thin_tac "_ \<turnstile> _ \<Rrightarrow> _")
      apply (thin_tac "_ = _")+

                apply (rule ZZZ, assumption)
      unfolding succ.simps bv_plus.simps
      apply (rule Reduce[of _ _ \<open>(Val v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8])[succ ((num\<^sub>3 + 1) mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(56 - 8) @ (Val v\<^sub>1[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, 8][num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, 8][(num\<^sub>3 + 1) mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8)\<close>])
      unfolding storage_constructor_exp_def
      apply (rule LoadWordEl, linarith, simp)
      apply simp
      using LoadWordEl

      using eval_exp'.induct

*)

end
