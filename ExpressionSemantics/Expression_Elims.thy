
section \<open>Elimination rules for expressions\<close>

theory Expression_Elims
  imports Expression_Rules
begin

subsection \<open>Val\<close>

lemma step_exp_valE:
  assumes \<open>\<Delta> \<turnstile> (Val v) \<leadsto> e\<close>
    shows P
  using assms by auto

interpretation step_exp_valE: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' P. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_valE, blast+)

subsection \<open>Var\<close>

lemmas step_exp_varE = VarE

lemma step_exp_var_inE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> e\<close>
      and \<open>((id' :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and elim: \<open>e = (Val v) \<Longrightarrow> P\<close>
    shows P
using assms(1) proof (elim step_exp_varE)
  fix val 
  assume val_e: \<open>e = Val val\<close>
  assume \<open>((id' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  then have \<open>e = (Val v)\<close>
    using assms(2) apply -
    apply (drule var_in_deterministic, blast)
    using val_e by blast
  thus ?thesis
    by (rule elim)
qed (use assms(2) in \<open>simp_all add: var_in_dom_\<Delta>\<close>)

interpretation step_exp_var_inE: exp_val_syntax \<open>\<lambda>e' v. (\<And>\<Delta> id t P e. \<Delta> \<turnstile> (id :\<^sub>t t) \<leadsto> e \<Longrightarrow> ((id :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> (e = e' \<Longrightarrow> P) \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_var_inE, blast+)

lemma step_exp_var_unknownE:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> e\<close>
      and \<open>(id' :\<^sub>t t) \<notin> dom \<Delta>\<close>
      and elim: \<open>\<And>str. e = unknown[str]: t \<Longrightarrow> P\<close>
    shows P
using assms(1) proof (elim VarE)
  fix val assume \<open>(id' :\<^sub>t t, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  thus ?thesis
    using var_in_dom_\<Delta> assms(2) by simp
next
  fix str 
  assume unknown_e: \<open>e = unknown[str]: t\<close>
  thus ?thesis by (rule elim[of str])
qed

subsection \<open>Load\<close>

lemma step_exp_load_byte_eqE: 
  assumes \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> e\<close> 
      and E: \<open>e = Val v' \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadByteE step_exp_valE.syntaxs E)
  using storage_constructor_exp_def by fastforce+

interpretation step_exp_load_byte_eqE: exp_val_syntax \<open>\<lambda>e' v'. (\<And>\<Delta> e v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r ed sz P. \<lbrakk>
    \<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> e; e = e' \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_load_byte_eqE)

lemma step_exp_load_byteE: 
  assumes \<open>\<Delta> \<turnstile> v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e\<close> 
      and Eeq: \<open>\<lbrakk>num\<^sub>2 = num\<^sub>1; sz\<^sub>2 = sz\<^sub>1; e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Eneq: \<open>\<lbrakk>num\<^sub>1 \<noteq> num\<^sub>2 \<or> sz\<^sub>1 \<noteq> sz\<^sub>2; e = ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadByteFromNextE step_exp_valE.syntaxs Eeq)
  apply assumption+
  subgoal by (rule Eneq, auto)
  unfolding storage_constructor_exp_def by force+

interpretation step_exp_load_byteE: exp2_val_syntax \<open>\<lambda>e' e v' v. (\<And>\<Delta> num\<^sub>1 num\<^sub>2 sz\<^sub>1 sz\<^sub>2 ed sz e'' P. \<lbrakk>
    \<Delta> \<turnstile> v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e'';
    (\<lbrakk>num\<^sub>2 = num\<^sub>1; sz\<^sub>2 = sz\<^sub>1; e'' = e'\<rbrakk> \<Longrightarrow> P); 
    (\<lbrakk>num\<^sub>1 \<noteq> num\<^sub>2 \<or> sz\<^sub>1 \<noteq> sz\<^sub>2; e'' = (e[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<rbrakk> \<Longrightarrow> P)
  \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_load_byteE)


lemma step_exp_load_un_addrE: 
  assumes \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<leadsto> e\<close> 
      and E: \<open>e = unknown[str]: imm\<langle>sz'\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LoadUnAddrE step_exp_valE.syntaxs E)

lemma step_exp_load_un_memE: 
  assumes \<open>\<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[Val v, ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e\<close> 
      and E: \<open>e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadUnMemE step_exp_valE.syntaxs E)
  using unknown_constructor_exp_def by force+

interpretation step_exp_load_un_memE: exp_syntax \<open>\<lambda>e'. (\<And>\<Delta> str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m ed  P e. \<lbrakk>
  \<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[e', ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e; e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_load_un_memE)

lemma step_exp_load_word_beE: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> e\<close>
      and Esingle: \<open>\<And>va v'. \<lbrakk>v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w va v'. \<lbrakk>v = (va[w \<leftarrow> v', sz]); e = ((Val va)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz);
                    w \<noteq> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk: \<open>\<And>str t va. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: t; va = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> P\<close>
      and Emany: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) @ ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)); 
                    sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadWordBeE step_exp_valE.syntaxs Eunk Emany)
  subgoal for va v' 
    apply (rule Esingle[of va v'])
    unfolding storage_constructor_exp_def by simp_all
  subgoal for va v' 
    apply (rule Enext)
    unfolding storage_constructor_exp_def by simp_all
  unfolding unknown_constructor_exp_def by simp_all

lemma step_exp_load_word_elE: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>
      and Esingle: \<open>\<And>va v'. \<lbrakk>v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w va v'. \<lbrakk>v = (va[w \<leftarrow> v', sz]); e = ((Val va)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz);
                    w \<noteq> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk: \<open>\<And>str t va. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: t; va = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> P\<close>
      and Emany: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) @ ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m); 
                    sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadWordElE step_exp_valE.syntaxs Eunk Emany)
  subgoal for va v' 
    apply (rule Esingle[of va v'])
    unfolding storage_constructor_exp_def by simp_all
  subgoal for va v' 
    apply (rule Enext)
    unfolding storage_constructor_exp_def by simp_all
  unfolding unknown_constructor_exp_def by simp_all

lemma step_exp_load_step_memE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> e\<close>
      and Emem: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Esingle: \<open>\<And>v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'. \<lbrakk>e\<^sub>1 = (v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w\<^sub>1 num\<^sub>2 sz\<^sub>2 v v'. \<lbrakk>w\<^sub>1 \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2);
                   e\<^sub>1 = (v[w\<^sub>1 \<leftarrow> v', sz]); v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e = ((Val v)[num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_mem: \<open>\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e = unknown[str]: imm\<langle>sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_addr: \<open>\<And>v w v' sza str t. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; e\<^sub>1 = (v[w \<leftarrow> v', sza]);
                        v\<^sub>2 = unknown[str]: t\<rbrakk> \<Longrightarrow> P\<close>
      and Ebe: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) @ ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m));
                   sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; ed = be\<rbrakk> \<Longrightarrow> P\<close>
      and Eel: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num. \<lbrakk>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) @ ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m);
                   type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m < sz; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; ed = el\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadStepMemE step_exp_valE.syntaxs Emem Eunk_mem Eunk_addr Ebe Eel)
  prefer 2 subgoal apply (rule Esingle)
    unfolding storage_constructor_exp_def word_constructor_exp_def by simp_all
  prefer 2
  subgoal apply (rule Enext)
    unfolding word_constructor_exp_def by simp_all
  apply assumption+
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_load_step_addrE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e\<close>
      and Eaddr: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1[e\<^sub>2', ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Emem: \<open>\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = Val v\<^sub>2; e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Esingle: \<open>\<And>v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'. \<lbrakk>e\<^sub>1 = (v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w\<^sub>1 num\<^sub>2 sz\<^sub>2 v v'. \<lbrakk>e\<^sub>1 = (v[w\<^sub>1 \<leftarrow> v', sz]); e\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; 
                    w\<^sub>1 \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2); e = ((Val v)[num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_mem: \<open>\<And>str t v. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v; e = unknown[str]: imm\<langle>sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_addr: \<open>\<And>v w v' sza str t. \<lbrakk>e\<^sub>1 = (v[w \<leftarrow> v', sza]); e\<^sub>2 = unknown[str]: t; e = unknown[str]: imm\<langle>sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Ebe: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>ed = be; sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) @ ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))\<rbrakk> \<Longrightarrow> P\<close>
      and Eel: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num. \<lbrakk>ed = el; sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) @ ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadStepAddrE step_exp_valE.syntaxs Eaddr Emem Eunk_mem Ebe Eel)
  prefer 4 subgoal by (rule Esingle)
  prefer 4 subgoal by (rule Enext, simp_all)
  prefer 6 subgoal by (rule Eunk_addr, simp_all)
  .

(*

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
*)

subsection \<open>Store\<close>

lemma step_exp_store_un_addrE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: t, ed]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and E: \<open>\<lbrakk>e = unknown[str]: (type v)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreUnAddrE step_exp_valE.syntaxs E)

interpretation step_exp_store_un_addrE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 _. (\<And>\<Delta> str t ed sz e P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [unknown[str]: t, ed]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; (e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_store_un_addrE)

lemma step_exp_store_elE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and Emore: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
         e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<rbrakk>
        \<Longrightarrow> P\<close>
      and Esingle: \<open>\<lbrakk>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreWordElE step_exp_valE.syntaxs Esingle Emore)

interpretation step_exp_store_elE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_store_elE)

lemma step_exp_store_beE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and Emore: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
         e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (low:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<rbrakk>
        \<Longrightarrow> P\<close>
      and Esingle: \<open>\<lbrakk>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreWordBeE step_exp_valE.syntaxs Esingle Emore)

interpretation step_exp_store_beE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (low:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_store_beE)

text \<open>Fallback steps\<close>

lemma step_exp_store_step_memE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
      and Estep_mem: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3))\<rbrakk> \<Longrightarrow> P\<close>
      and Eword: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> P\<close>
      and Ebe: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3]));
                 sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; en = be\<rbrakk> \<Longrightarrow> P\<close>
      and Eel: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3]));
                 sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; en = el\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk: \<open>\<And>v str t'. \<lbrakk>e = unknown[str]: (type v); e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: t'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim StoreStepMemE step_exp_valE.syntaxs Estep_mem Eunk Eword Ebe Eel)
  apply assumption+
  unfolding storage_constructor_exp_def unknown_constructor_exp_def word_constructor_exp_def by simp_all

lemma step_exp_store_step_addrE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
      and Estep_addr: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<rbrakk> \<Longrightarrow> P\<close>
      and Estep_mem: \<open>\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = Val v\<^sub>2; e = (e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3))\<rbrakk> \<Longrightarrow> P\<close>
      and Eword: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>3, sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>; e\<^sub>1 = Val v; e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> P\<close>
      and Ebe: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3]));
                 sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; en = be\<rbrakk> \<Longrightarrow> P\<close>
      and Eel: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val v\<^sub>3]));
                 sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; e\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; en = el\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk: \<open>\<And>v str t'. \<lbrakk>e = unknown[str]: (type v); e\<^sub>1 = Val v; e\<^sub>2 = unknown[str]: t'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreStepAddrE step_exp_valE.syntaxs Estep_addr Estep_mem Eunk Eword Ebe Eel)

lemmas step_exp_store_step_valE = StoreStepValE



(*

lemma STORE_STEP_ADDR_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz')) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz'))\<close> 
  using assms STORE_STEP_ADDR word_constructor_exp_def by presburger
t, auto simp add: eval_exp.simps)

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
*)

subsection \<open>Let steps\<close>

lemma step_exp_letE:
  assumes \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<leadsto> e'\<close>
      and E: \<open>e' = [v\<sslash>var]e \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LetE step_exp_valE E)

interpretation step_exp_letE: exp_val_syntax \<open>\<lambda>e'' v. (\<And>\<Delta> var e e' P. \<lbrakk>\<Delta> \<turnstile> (Let var e'' e) \<leadsto> e'; e' = [v\<sslash>var]e \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_letE, blast+)

text \<open>Fallback steps\<close>

lemmas step_exp_step_letE = LetStepE

text \<open>Ite steps\<close>

lemma step_exp_if_trueE:
  assumes \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
      and E: \<open>e = Val v\<^sub>2 \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim IfTrueE step_exp_valE.syntaxs E)

interpretation step_exp_ite_trueE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>1 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_if_trueE)

lemma step_exp_if_falseE:
  assumes \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
      and E: \<open>e = Val v\<^sub>3 \<Longrightarrow> P\<close>
    shows P
  using assms by (elim IfFalseE step_exp_valE.syntaxs E)

interpretation step_exp_ite_falseE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>2 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_if_falseE)

lemma step_exp_if_unknownE:
  assumes \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: (type v\<^sub>2) \<Longrightarrow> P\<close>
    shows P
  using assms by (elim IfUnknownE step_exp_valE.syntaxs E)

interpretation step_exp_if_unknownE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> e str t P. \<lbrakk>
      \<Delta> \<turnstile> ite (unknown[str]: t) e\<^sub>1 e\<^sub>2 \<leadsto> e; e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_if_unknownE)
(* TODO further optimisations with type *)
(* TODO rename unknown_constructor_exp_def to unknown_exp_def*)

text \<open>Fallback steps\<close>

lemma step_exp_if_step_condE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e'\<close>
      and Estep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<rbrakk> \<Longrightarrow> P\<close>
      and Etrue: \<open>\<lbrakk>e\<^sub>1 = true; e' = Val v\<^sub>2\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>e\<^sub>1 = false; e' = Val v\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and Eunknown: \<open>\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim IfStepCondE step_exp_valE.syntaxs Estep Etrue Efalse Eunknown)

interpretation step_exp_if_step_condE: exp2_val_syntax \<open>\<lambda>e\<^sub>2 e\<^sub>3 v\<^sub>2 _. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = ite e\<^sub>1' e\<^sub>2 e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<lbrakk>e\<^sub>1 = true; e' = e\<^sub>2\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_if_step_condE)

lemma step_exp_if_step_thenE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> e'\<close>
      and Ethen: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<rbrakk> \<Longrightarrow> P\<close>
      and Econd: \<open>\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = (Val v\<^sub>2); e' = ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<rbrakk> \<Longrightarrow> P\<close>
      and Etrue: \<open>\<And>v\<^sub>2. \<lbrakk>e\<^sub>1 = true; e\<^sub>2 = (Val v\<^sub>2); e' = Val v\<^sub>2\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>e\<^sub>1 = false; e' = Val v\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and Eunknown: \<open>\<And>str t v\<^sub>2. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v\<^sub>2; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim IfStepThenE step_exp_valE.syntaxs Eunknown Efalse Etrue Econd Ethen)

interpretation step_exp_if_step_thenE: exp_syntax \<open>\<lambda>e\<^sub>3. (\<And>\<Delta> e\<^sub>1 e\<^sub>2 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = (ite e\<^sub>1 e\<^sub>2' e\<^sub>3)\<rbrakk> \<Longrightarrow> P);
      (\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = (Val v\<^sub>2); e' = ite e\<^sub>1' (Val v\<^sub>2) e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>v\<^sub>2. \<lbrakk>e\<^sub>1 = true; e\<^sub>2 = (Val v\<^sub>2); e' = (Val v\<^sub>2)\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t v\<^sub>2. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v\<^sub>2; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_if_step_thenE)

lemmas step_exp_if_step_elseE = IfStepElseE

text \<open>Uop steps\<close>

lemma step_exp_uop_unkE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp uop unknown[str]: t) \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: t \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim UopUnkE step_exp_valE.syntaxs E)

lemma step_exp_notE: 
  assumes \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = ~\<^sub>b\<^sub>v (num \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim NotE step_exp_valE.syntaxs E)

lemma step_exp_negE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = -\<^sub>b\<^sub>v (num \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim NegE step_exp_valE.syntaxs E)

text \<open>Fallback steps\<close>

lemmas step_exp_uopE = UopE

text \<open>Concat steps\<close>

lemma step_exp_concatE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim ConcatE step_exp_valE.syntaxs E)

lemma step_exp_concat_rhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) @ unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
      and E1: \<open>\<And>sz\<^sub>1 str'. \<lbrakk>v = unknown[str']: imm\<langle>sz\<^sub>1\<rangle>; e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<And>sz\<^sub>1. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P 
  using assms(1) apply (elim ConcatRhsUnE step_exp_valE.syntaxs E2)
  defer
  using E1 unknown_constructor_exp_def by force

(* TODO lots of optimisation *)

lemma step_exp_concat_lhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<leadsto> e\<close>
      and E1: \<open>\<And>sz\<^sub>2 str'. \<lbrakk>v = unknown[str']: imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<And>sz\<^sub>2. \<lbrakk>type v = imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P 
  using assms(1) apply (elim ConcatLhsUnE step_exp_valE.syntaxs E2)
  using E1 unknown_constructor_exp_def by force

(* TODO lots of optimisation *)

lemma step_exp_concat_unE:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1\<rangle>) @ unknown[str\<^sub>2]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
      and E1: \<open>\<lbrakk>e = unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<lbrakk>e = unknown[str\<^sub>2]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ConcatRhsE step_exp_valE.syntaxs)
  apply simp_all
  unfolding unknown_constructor_exp_def apply auto
  unfolding unknown_constructor_exp_def[symmetric] 
  subgoal by (rule E2)
  subgoal by (rule E1)
  .

text \<open>Fallback rules\<close>

lemma step_exp_concat_lhsE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<leadsto> e\<close>
      and Pstep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' @ (Val v\<^sub>2))\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>sz\<^sub>1 sz\<^sub>2 str v. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>sz\<^sub>1 sz\<^sub>2 str. \<lbrakk>e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Econcat: \<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1; v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ConcatLhsE step_exp_valE.syntaxs Pstep Econcat)
  apply assumption+
  unfolding unknown_constructor_exp_def word_constructor_exp_def apply simp_all
  subgoal apply (rule EunknownR, assumption+)
    unfolding unknown_constructor_exp_def by simp
  subgoal apply (rule EunknownL)
    unfolding unknown_constructor_exp_def by simp
  .

(* Lots of optimisations? *)
interpretation step_exp_concat_lhsE: exp_val_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = (e\<^sub>1' @ e\<^sub>2)\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str v. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str. \<lbrakk>e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1; v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e' = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_concat_lhsE)

lemmas step_exp_concat_rhsE = ConcatRhsE

text \<open>Extract steps\<close>

lemma step_exp_extractE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)] \<leadsto> e\<close>
      and E: \<open>e = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2 \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim ExtractE step_exp_valE.syntaxs E)

lemma step_exp_extract_unE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t] \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ExtractUnE step_exp_valE.syntaxs)
  apply (rule E)
  by simp

text \<open>Fallback rules\<close>

lemma step_exp_extract_reduceE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e\<^sub>1] \<leadsto> e\<close>
      and Estep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = extract:sz\<^sub>1:sz\<^sub>2[e\<^sub>1']\<rbrakk> \<Longrightarrow> P\<close>
      and Eextract: \<open>\<And>num sz. \<lbrakk>e\<^sub>1 = num \<Colon> sz; e = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<rbrakk> \<Longrightarrow> P\<close>
      and Eunknown: \<open>\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e = unknown[str]: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ExtractReduceE Estep Eextract Eunknown)
  prefer 3 by simp

text \<open>Cast steps\<close>

lemma step_exp_cast_lowE:
  assumes \<open>\<Delta> \<turnstile> low:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastLowE step_exp_valE.syntaxs)
  by (rule E, simp)

lemma step_exp_cast_highE:
  assumes \<open>\<Delta> \<turnstile> high:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastHighE step_exp_valE.syntaxs)
  by (rule E, simp)

lemma step_exp_cast_signedE:
  assumes \<open>\<Delta> \<turnstile> extend:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastSignedE step_exp_valE.syntaxs)
  by (rule E, simp)

lemma step_exp_cast_unsignedE:
  assumes \<open>\<Delta> \<turnstile> pad:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastUnsignedE step_exp_valE.syntaxs)
  by (rule E, simp)

lemma step_exp_cast_unknownE:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: imm\<langle>sz\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim CastUnkE step_exp_valE.syntaxs E)

text \<open>Fallback rules\<close>

lemma step_exp_cast_reduceE:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<leadsto> e\<close>
      and Estep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = Cast cast sz e\<^sub>1'\<rbrakk> \<Longrightarrow> P\<close>
      and Elow: \<open>\<And>num sz'. \<lbrakk>cast = low; e\<^sub>1 = num \<Colon> sz'; e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<rbrakk> \<Longrightarrow> P\<close>
      and Ehigh: \<open>\<And>num sz'. \<lbrakk>cast = high; e\<^sub>1 = num \<Colon> sz'; e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz)\<rbrakk> \<Longrightarrow> P\<close>
      and Esigned: \<open>\<And>num sz'. \<lbrakk>cast = extend; e\<^sub>1 = num \<Colon> sz'; e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<rbrakk> \<Longrightarrow> P\<close>
      and Eunsigned: \<open>\<And>num sz'. \<lbrakk>cast = pad; e\<^sub>1 = num \<Colon> sz'; e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<rbrakk> \<Longrightarrow> P\<close>
      and Eunknown: \<open>\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e = unknown[str]: imm\<langle>sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastReduceE Estep Elow Ehigh Esigned Eunsigned Eunknown)
  by simp_all

text \<open>BOP steps\<close>

lemma step_exp_plusE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim PlusE step_exp_valE.syntaxs E)

lemma step_exp_minusE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim MinusE step_exp_valE.syntaxs E)

lemma step_exp_timesE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim TimesE step_exp_valE.syntaxs E)

lemma step_exp_divE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim DivE step_exp_valE.syntaxs E)

lemma step_exp_sdivE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim SDivE step_exp_valE.syntaxs E)

lemma step_exp_modE: 
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim ModE step_exp_valE.syntaxs E)

lemma step_exp_smodE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim SModE step_exp_valE.syntaxs E)

lemma step_exp_lslE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LslE step_exp_valE.syntaxs E)

lemma step_exp_lsrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LsrE step_exp_valE.syntaxs E)

lemma step_exp_asrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim AsrE step_exp_valE.syntaxs E)

lemma step_exp_landE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LAndE step_exp_valE.syntaxs E)

lemma step_exp_lorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LOrE step_exp_valE.syntaxs E)

lemma step_exp_xorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim XOrE step_exp_valE.syntaxs E)

lemma step_exp_eq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = true \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim EqSameE step_exp_valE.syntaxs E)

lemma step_exp_neq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = false \<Longrightarrow> P\<close>
    shows P
  using assms by (elim NeqSameE step_exp_valE.syntaxs E)

lemma step_exp_eqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
      and E: \<open>\<lbrakk>e = (num\<^sub>1 \<Colon> sz\<^sub>1) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) 
  by (metis E EqDiffE bv_eq_def step_exp_eq_sameE step_exp_valE.syntaxs(1))
  
lemma step_exp_neqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
      and E: \<open>\<lbrakk>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1)
  by (metis E NeqDiffE bv_eq_def bv_negation_false_true bv_negation_true_false step_exp_neq_sameE step_exp_valE.syntaxs(1))

lemma step_exp_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LessE step_exp_valE.syntaxs E)

lemma step_exp_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LessEqE step_exp_valE.syntaxs E)

lemma step_exp_signed_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim SignedLessE step_exp_valE.syntaxs E)

lemma step_exp_signed_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
      and E: \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim SignedLessEqE step_exp_valE.syntaxs E)

lemma step_exp_aop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e\<^sub>2 \<leadsto> e\<close>
      and EunknownL: \<open>e = unknown[str]: t \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>str' t'. \<lbrakk>e\<^sub>2 = (unknown[str']: t'); e = unknown[str']: t'\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (unknown[str]: t) (AOp aop) e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim AopUnkRhsE step_exp_valE.syntaxs EunknownL EunknownR EunknownStep)
  by simp

lemma step_exp_aop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (AOp aop) unknown[str]: t \<leadsto> e\<close>
      and EunknownR: \<open>e = unknown[str]: t \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>str' t'. \<lbrakk>e\<^sub>1 = (unknown[str']: t'); e = unknown[str']: t'\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = BinOp e\<^sub>1' (AOp aop) (unknown[str]: t)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim AopUnkLhsE step_exp_valE.syntaxs EunknownL EunknownR EunknownStep)

lemma step_exp_lop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e\<^sub>2 \<leadsto> e\<close>
      and EunknownL: \<open>e = unknown[str]: imm\<langle>1\<rangle> \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>str' t'. \<lbrakk>e\<^sub>2 = (unknown[str']: t'); e = unknown[str']: imm\<langle>1\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (unknown[str]: t) (LOp lop) e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LopUnkRhsE step_exp_valE.syntaxs EunknownL EunknownR EunknownStep)
  apply simp_all
  by (rule EunknownL, simp)

lemma step_exp_lop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (LOp lop) unknown[str]: t \<leadsto> e\<close>
      and EunknownR: \<open>e = unknown[str]: imm\<langle>1\<rangle> \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>str' t'. \<lbrakk>e\<^sub>1 = (unknown[str']: t'); e = unknown[str']: imm\<langle>1\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = BinOp e\<^sub>1' (LOp lop) (unknown[str]: t)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms apply (elim LopUnkLhsE step_exp_valE.syntaxs EunknownR EunknownL EunknownStep)
  by simp_all

text \<open>Fallback rules\<close>

lemma step_exp_bop_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
      and Estep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (Val v) bop e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
      and EaopL: \<open>\<And>str t aop. \<lbrakk>e = unknown[str]: t; v = unknown[str]: t; bop = AOp aop\<rbrakk> \<Longrightarrow> P\<close>
      and ElopL: \<open>\<And>str t lop. \<lbrakk>e = unknown[str]: imm\<langle>1\<rangle>; v = unknown[str]: t; bop = LOp lop\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim BopRhsE Estep)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def plus_exp.simps by simp_all

lemma step_exp_bop_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
    shows \<open>\<exists>e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<and> e = BinOp e\<^sub>1' bop e\<^sub>2\<close>
  using assms(1) apply (rule BopLhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def plus_exp.simps by simp_all


end
