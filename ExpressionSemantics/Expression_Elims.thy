section \<open>Elimination rules for expressions\<close>

theory Expression_Elims
  imports Expression_Rules Solve_BitVector
begin

subsection \<open>Val\<close>

lemma step_exp_valE[elim!]:
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

lemma step_exp_load_byteE:
  assumes major: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e\<close> 
      and Eeq: \<open>\<lbrakk>w = (num\<^sub>2 \<Colon> sz\<^sub>2); e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Eneq: \<open>\<lbrakk>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2); e = ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
using major proof (elim LoadByteFromNextE step_exp_valE.word step_exp_valE.storage Eeq Eneq)
  fix sz\<^sub>m\<^sub>e\<^sub>m :: nat and va :: val
  assume "sz\<^sub>m\<^sub>e\<^sub>m < sz"
    and "type va = mem\<langle>sz\<^sub>2, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
    and "v[w \<leftarrow> v', sz] = Val va"
  thus P 
    unfolding Val_simp_storage[symmetric] apply clarify
    apply (cases w rule : word_exhaust, clarify)
    by (elim type_storageE, clarify)
next
  fix va :: val
    and sz\<^sub>m\<^sub>e\<^sub>m :: nat
  assume "type va = mem\<langle>sz\<^sub>2, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
    and "sz\<^sub>m\<^sub>e\<^sub>m < sz"
    and "v[w \<leftarrow> v', sz] = Val va"
  thus P
    unfolding Val_simp_storage[symmetric] apply clarify
    apply (cases w rule : word_exhaust, clarify)
    by (elim type_storageE, clarify)
qed 

interpretation step_exp_load_byteE: exp2_val_syntax \<open>\<lambda>e' e v' v. (\<And>\<Delta> w num\<^sub>2 sz\<^sub>2 ed sz e'' P. \<lbrakk>
    \<Delta> \<turnstile> v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e'';
    (\<lbrakk>w = (num\<^sub>2 \<Colon> sz\<^sub>2); e'' = e'\<rbrakk> \<Longrightarrow> P); 
    (\<lbrakk>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2); e'' = (e[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<rbrakk> \<Longrightarrow> P)
  \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_byteE in blast)

lemma step_exp_load_byte_eqE: 
  assumes major: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> e\<close> 
      and minor: \<open>e = Val v' \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim step_exp_load_byteE minor)
  by blast

interpretation step_exp_load_byte_eqE: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e' v'. (\<And>\<Delta> e v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r ed sz P. \<lbrakk>
    \<Delta> \<turnstile> v[w\<^sub>w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e; e = e' \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_byte_eqE in blast)

lemma step_exp_load_byte_from_nextE: 
  assumes major: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e\<close> 
      and caveat: \<open>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
      and minor: \<open>\<lbrakk>e = ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major by (elim step_exp_load_byteE minor, use caveat in simp)

(* TODO incorrect precedence - should be val.word not word.val ? *)
interpretation step_exp_load_byte_from_nextE: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v. 
    (\<And>\<Delta> w v' ed sz P e'. \<lbrakk>
    \<Delta> \<turnstile> v[w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e'; w \<noteq> w\<^sub>w; 
    (\<lbrakk>e' = (e[w\<^sub>e, ed]:usz)\<rbrakk> \<Longrightarrow> P)\<rbrakk> 
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_byte_from_nextE in blast)


lemma step_exp_load_un_addrE: 
  assumes \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<leadsto> e\<close> 
      and E: \<open>e = unknown[str]: imm\<langle>sz'\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim LoadUnAddrE step_exp_valE.storage step_exp_valE.unknown E)

lemma step_exp_load_un_memE: 
  assumes \<open>\<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[Val v, ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e\<close> 
      and E: \<open>e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadUnMemE step_exp_valE.storage step_exp_valE.unknown E)
  using unknown_constructor_exp_def by force+

interpretation step_exp_load_un_memE: exp_val_syntax \<open>\<lambda>e' _. (\<And>\<Delta> str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m ed  P e. \<lbrakk>
  \<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[e', ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e; e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_un_memE in blast)

lemma step_exp_load_word_beE: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> e\<close>
      and Esingle: \<open>\<And>va v'. \<lbrakk>v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w va v'. \<lbrakk>v = (va[w \<leftarrow> v', sz]); e = ((Val va)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz);
                    w \<noteq> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk: \<open>\<And>str t va. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: t; va = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> P\<close>
      and Emany: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)); 
                    sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadWordBeE step_exp_valE step_exp_valE.word Eunk Emany)
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
      and Emany: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m); 
                    sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadWordElE step_exp_valE step_exp_valE.word Eunk Emany)
  subgoal for va v' 
    apply (rule Esingle[of va v'])
    unfolding storage_constructor_exp_def by simp_all
  subgoal for va v' 
    apply (rule Enext)
    unfolding storage_constructor_exp_def by simp_all
  unfolding unknown_constructor_exp_def by simp_all

lemma step_exp_load_word_el_memE:
  assumes major: \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>
      and caveat: \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
      and minor: \<open>\<lbrakk>e = (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m);
                    type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat
  unfolding Val_simp_storage[symmetric]
  apply (elim step_exp_load_word_elE)
  apply simp_all
  apply (rule minor)
  apply (metis Type.inject(2) storage_constructor_exp_def type_storageI type_word.elims)
  by (metis Type.inject(2) type_storage_addrI type_word.elims)

interpretation step_exp_load_word_el_memE: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. 
  (\<And>\<Delta> sz v w v' e sz\<^sub>m\<^sub>e\<^sub>m P. \<lbrakk>\<Delta> \<turnstile> v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][e\<^sub>2, el]:usz \<leadsto> e; sz\<^sub>m\<^sub>e\<^sub>m < sz; (
      \<lbrakk>e = (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ e\<^sub>2, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<copyright> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][e\<^sub>2, el]:usz\<^sub>m\<^sub>e\<^sub>m)); type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  apply (standard)
  using step_exp_load_word_el_memE by blast

(*
interpretation step_exp_load_word_el_storageE: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz P. 
    \<Delta> \<turnstile> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e
    \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz
    \<Longrightarrow> (\<lbrakk>e = (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m);
                    type (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<Longrightarrow> P)\<close>
  apply (standard)
  using step_load_word_elI by blast
*)
lemma step_exp_load_step_memE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> e\<close>
      and Emem: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Esingle: \<open>\<And>v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'. \<lbrakk>e\<^sub>1 = (v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz]); v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; e = Val v'\<rbrakk> \<Longrightarrow> P\<close>
      and Enext: \<open>\<And>w\<^sub>1 num\<^sub>2 sz\<^sub>2 v v'. \<lbrakk>w\<^sub>1 \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2);
                   e\<^sub>1 = (v[w\<^sub>1 \<leftarrow> v', sz]); v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e = ((Val v)[num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_mem: \<open>\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e = unknown[str]: imm\<langle>sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Eunk_addr: \<open>\<And>v w v' sza str t. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; e\<^sub>1 = (v[w \<leftarrow> v', sza]);
                        v\<^sub>2 = unknown[str]: t\<rbrakk> \<Longrightarrow> P\<close>
      and Ebe: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m));
                   sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; ed = be\<rbrakk> \<Longrightarrow> P\<close>
      and Eel: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num. \<lbrakk>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m);
                   type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m < sz; e\<^sub>1 = Val v; v\<^sub>2 = num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; ed = el\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LoadStepMemE step_exp_valE step_exp_valE.word Emem Eunk_mem Eunk_addr Ebe Eel)
  prefer 2 subgoal apply (rule Esingle)
    unfolding storage_constructor_exp_def word_constructor_exp_def by simp_all
  prefer 2
  subgoal apply (rule Enext)
    unfolding word_constructor_exp_def by simp_all
  apply assumption+
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_load_step_mem_strictE:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (elim step_exp_load_step_memE minor)
  using storage_constructor_exp_def unknown_constructor_exp_def word_constructor_exp_def by auto

interpretation step_exp_load_step_mem_strictE: exp_val_syntax \<open>\<lambda>e\<^sub>2 _. 
  (\<And>\<Delta> e\<^sub>1 e sz ed P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e; \<forall>v. e\<^sub>1 \<noteq> (Val v); 
      (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1'[e\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  apply (standard)
  using step_exp_load_step_mem_strictE by blast

lemmas step_exp_load_step_addrE = LoadStepAddrE

lemma step_exp_load_step_addr_strictE:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1[e\<^sub>2', ed]:usz)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (elim step_exp_load_step_addrE minor)
  using unknown_constructor_exp_def word_constructor_exp_def by auto

subsection \<open>Store\<close>

lemma step_exp_store_un_addrE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: t, ed]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and E: \<open>\<lbrakk>e = unknown[str]: (type v)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreUnAddrE step_exp_valE step_exp_valE.unknown E)

interpretation step_exp_store_un_addrE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 _. (\<And>\<Delta> str t ed sz e P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [unknown[str]: t, ed]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; (e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_un_addrE in blast)

lemma step_exp_store_singleE:
  assumes major: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz \<leftarrow> (Val v')) \<leadsto> e\<close> 
      and caveat: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
      and minor: \<open>\<lbrakk>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major sketch (elim StoreWordE step_exp_valE step_exp_valE.word minor)
proof (elim StoreWordE step_exp_valE step_exp_valE.word minor)
  fix sz\<^sub>m\<^sub>e\<^sub>m assume gt: "sz\<^sub>m\<^sub>e\<^sub>m < sz" and type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close>
    using type caveat by fastforce
  thus P
    using gt by fastforce
next
  fix sz\<^sub>m\<^sub>e\<^sub>m assume gt: "sz\<^sub>m\<^sub>e\<^sub>m < sz" and type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close>
    using type caveat by fastforce
  thus P
    using gt by fastforce
qed

interpretation step_exp_store_singleE: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. 
  (\<And>\<Delta> e en. \<lbrakk>
    \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>3) \<leadsto> e;
    (e = (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m]) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_singleE in blast)

lemma step_exp_store_elE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and Emore: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
         e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<rbrakk>
        \<Longrightarrow> P\<close>
      and Esingle: \<open>\<lbrakk>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreWordElE step_exp_valE step_exp_valE.word Esingle Emore)

interpretation step_exp_store_elE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> e num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_elE in blast)

lemma step_exp_store_el_manyE:
  assumes major: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and caveat: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
      and minor: \<open>\<lbrakk>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<rbrakk>
        \<Longrightarrow> P\<close>
    shows P
  using major caveat sketch (elim step_exp_store_elE minor )
proof (elim step_exp_store_elE minor)
  fix sz\<^sub>m\<^sub>e\<^sub>m' :: nat
  assume type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>" "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m'\<rangle>"
    and major: "e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m' \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m'[Val v'])) 
                              with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m') \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m')[Val v']))"
  have sz\<^sub>m\<^sub>e\<^sub>m: \<open>sz\<^sub>m\<^sub>e\<^sub>m' = sz\<^sub>m\<^sub>e\<^sub>m\<close>
    using type_determ[OF type] by simp
  show P
    using major[unfolded sz\<^sub>m\<^sub>e\<^sub>m] by (rule minor )
next
  assume type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>" "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>"
    and sz_neq: "sz\<^sub>m\<^sub>e\<^sub>m < sz"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close> 
    using type_determ[OF type] by simp
  thus P
    using sz_neq by blast
qed
(*
interpretation step_exp_store_el_manyE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> e num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;  sz\<^sub>m\<^sub>e\<^sub>m < sz;
      (\<lbrakk>
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_el_manyE in blast)
*)
interpretation step_exp_store_el_manyE: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ _ e\<^sub>3 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m.
    (\<And>\<Delta> e P sz. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:usz \<leftarrow> e\<^sub>3 \<leadsto> e; sz\<^sub>m\<^sub>e\<^sub>m < sz;
      (e = ((e\<^sub>1 with [e\<^sub>2, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3]) with [succ e\<^sub>2, el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3])) \<Longrightarrow> P)
  \<rbrakk> \<Longrightarrow> P)\<close>
  apply (standard)
  using step_exp_store_el_manyE by blast

lemma step_exp_store_beE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and Emore: \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
         e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (low:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<rbrakk>
        \<Longrightarrow> P\<close>
      and Esingle: \<open>\<lbrakk>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz]); type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim StoreWordBeE step_exp_valE step_exp_valE.word Esingle Emore)

interpretation step_exp_store_beE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (low:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_beE in blast)

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
  using assms(1) apply (elim StoreStepMemE step_exp_valE Estep_mem Eunk Eword Ebe Eel)
  apply assumption+
  unfolding storage_constructor_exp_def unknown_constructor_exp_def word_constructor_exp_def by simp_all

lemma step_exp_store_step_mem_strictE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3))\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major apply (elim step_exp_store_step_memE minor)
  using caveat by simp_all

interpretation step_exp_store_step_mem_strictE: exp2_val_syntax \<open>\<lambda>e\<^sub>2 e\<^sub>3 _ _. (\<And>\<Delta> e e\<^sub>1 en sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; \<forall>v. e\<^sub>1 \<noteq> (Val v);
      (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_step_mem_strictE in blast)


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
  using assms(1) by (elim StoreStepAddrE step_exp_valE Estep_addr Estep_mem Eunk Eword Ebe Eel)

lemma step_exp_store_step_addr_strictE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
      and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<rbrakk> \<Longrightarrow> P\<close>
    shows P
using major proof (elim step_exp_store_step_addrE)
  fix e\<^sub>2' assume "\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'" "e = e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> Val v\<^sub>3"
  thus P by (rule minor)
qed(use caveat unknown_constructor_exp_def word_constructor_exp_def in blast)+

interpretation step_exp_store_step_addr_strictE: exp_val_syntax \<open>\<lambda>e\<^sub>3 _. 
  (\<And>\<Delta> e e\<^sub>1 e\<^sub>2 en sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; \<forall>v. e\<^sub>2 \<noteq> (Val v);
      (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e\<^sub>3)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_step_addr_strictE in blast)



lemmas step_exp_store_step_valE = StoreStepValE

lemma step_exp_store_step_val_strictE:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3 \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>3 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>3'. \<lbrakk>e = (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3'); \<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major apply (elim step_exp_store_step_valE minor)
  using caveat by simp_all

subsection \<open>Let steps\<close>

lemma step_exp_letE:
  assumes \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<leadsto> e'\<close>
  obtains \<open>e' = [v\<sslash>var]e\<close>
  using assms(1) by (elim LetE step_exp_valE)

interpretation step_exp_letE: exp_val_syntax \<open>\<lambda>e'' v. (\<And>\<Delta> var e e' P. \<lbrakk>\<Delta> \<turnstile> (Let var e'' e) \<leadsto> e'; e' = [v\<sslash>var]e \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_letE, blast+)

text \<open>Fallback steps\<close>

lemmas step_exp_step_letE = LetStepE

text \<open>Ite steps\<close>

lemma step_exp_if_trueE:
  assumes \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
  obtains \<open>e = Val v\<^sub>2\<close>
  using assms(1) by (elim IfTrueE step_exp_valE step_exp_valE.true)
  

interpretation step_exp_ite_trueE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>1 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_trueE in blast)

lemma step_exp_if_falseE:
  assumes \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
  obtains \<open>e = Val v\<^sub>3\<close>
  using assms by (elim IfFalseE step_exp_valE step_exp_valE.false)

interpretation step_exp_ite_falseE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>2 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_falseE in blast)

lemma step_exp_if_unknownE:
  assumes \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
  obtains \<open>e = unknown[str]: (type v\<^sub>2)\<close>
  using assms by (elim IfUnknownE step_exp_valE step_exp_valE.unknown)

interpretation step_exp_if_unknownE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> e str t P. \<lbrakk>
      \<Delta> \<turnstile> ite (unknown[str]: t) e\<^sub>1 e\<^sub>2 \<leadsto> e; e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_unknownE in blast)
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
  using assms(1) by (elim IfStepCondE step_exp_valE Estep Etrue Efalse Eunknown)

interpretation step_exp_if_step_condE: exp2_val_syntax \<open>\<lambda>e\<^sub>2 e\<^sub>3 v\<^sub>2 _. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = ite e\<^sub>1' e\<^sub>2 e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<lbrakk>e\<^sub>1 = true; e' = e\<^sub>2\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_step_condE in blast)

lemma step_exp_if_step_thenE:
  assumes \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> e'\<close>
      and Ethen: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<rbrakk> \<Longrightarrow> P\<close>
      and Econd: \<open>\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = (Val v\<^sub>2); e' = ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<rbrakk> \<Longrightarrow> P\<close>
      and Etrue: \<open>\<And>v\<^sub>2. \<lbrakk>e\<^sub>1 = true; e\<^sub>2 = (Val v\<^sub>2); e' = Val v\<^sub>2\<rbrakk> \<Longrightarrow> P\<close>
      and Efalse: \<open>\<lbrakk>e\<^sub>1 = false; e' = Val v\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and Eunknown: \<open>\<And>str t v\<^sub>2. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v\<^sub>2; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim IfStepThenE step_exp_valE Eunknown Efalse Etrue Econd Ethen)

interpretation step_exp_if_step_thenE: exp_val_syntax \<open>\<lambda>e\<^sub>3 _. (\<And>\<Delta> e\<^sub>1 e\<^sub>2 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = (ite e\<^sub>1 e\<^sub>2' e\<^sub>3)\<rbrakk> \<Longrightarrow> P);
      (\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = (Val v\<^sub>2); e' = ite e\<^sub>1' (Val v\<^sub>2) e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>v\<^sub>2. \<lbrakk>e\<^sub>1 = true; e\<^sub>2 = (Val v\<^sub>2); e' = (Val v\<^sub>2)\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t v\<^sub>2. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v\<^sub>2; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_step_thenE in blast)

lemmas step_exp_if_step_elseE = IfStepElseE

text \<open>Uop steps\<close>

lemma step_exp_uop_unkE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp uop unknown[str]: t) \<leadsto> e\<close>
  obtains \<open>e = unknown[str]: t\<close>
  using assms(1) by (elim UopUnkE step_exp_valE step_exp_valE.unknown)

lemma step_exp_notE: 
  assumes \<open>\<Delta> \<turnstile> (\<sim>(num \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = ~\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  using assms(1) by (elim NotE step_exp_valE step_exp_valE.word)

lemma step_exp_negE: 
  assumes \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = -\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  using assms(1) by (elim NegE step_exp_valE step_exp_valE.word)

text \<open>Fallback steps\<close>

lemmas step_exp_uopE = UopE

text \<open>Concat steps\<close>

lemma step_exp_concatE:
  assumes major: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using major by (elim ConcatE step_exp_valE.word)

interpretation step_exp_concatE: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e; e = e\<^sub>1 \<cdot> e\<^sub>2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concatE in blast)

lemma step_exp_concat_rhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((Val v) \<copyright> unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
      and E1: \<open>\<And>sz\<^sub>1 str'. \<lbrakk>v = unknown[str']: imm\<langle>sz\<^sub>1\<rangle>; e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<And>sz\<^sub>1. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P 
  using assms(1) apply (elim ConcatRhsUnE step_exp_valE step_exp_valE.unknown E2)
  defer
  using E1 unknown_constructor_exp_def by force

(* TODO lots of optimisation *)

lemma step_exp_concat_lhs_unE:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> (Val v)) \<leadsto> e\<close>
      and E1: \<open>\<And>sz\<^sub>2 str'. \<lbrakk>v = unknown[str']: imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<And>sz\<^sub>2. \<lbrakk>type v = imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P 
  using assms(1) apply (elim ConcatLhsUnE step_exp_valE step_exp_valE.unknown E2)
  using E1 unknown_constructor_exp_def by force

(* TODO lots of optimisation *)

lemma step_exp_concat_unE:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> unknown[str\<^sub>2]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
      and E1: \<open>\<lbrakk>e = unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and E2: \<open>\<lbrakk>e = unknown[str\<^sub>2]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ConcatRhsE step_exp_valE)
  apply simp_all
  unfolding unknown_constructor_exp_def apply auto
  unfolding unknown_constructor_exp_def[symmetric] 
  subgoal by (rule E2)
  subgoal by (rule E1)
  .

text \<open>Fallback rules\<close>

lemma step_exp_concat_lhsE:
  assumes \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> (Val v\<^sub>2)) \<leadsto> e\<close>
      and Pstep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' \<copyright> (Val v\<^sub>2))\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>sz\<^sub>1 sz\<^sub>2 str v. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>sz\<^sub>1 sz\<^sub>2 str. \<lbrakk>e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>; e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and Econcat: \<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1; v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ConcatLhsE step_exp_valE Pstep Econcat)
  apply assumption+
  unfolding unknown_constructor_exp_def word_constructor_exp_def apply simp_all
  subgoal apply (rule EunknownR, assumption+)
    unfolding unknown_constructor_exp_def by simp
  subgoal apply (rule EunknownL)
    unfolding unknown_constructor_exp_def by simp
  .

(* Lots of optimisations? *)
interpretation step_exp_concat_lhsE: exp_val_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = (e\<^sub>1' \<copyright> e\<^sub>2)\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str v. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str. \<lbrakk>e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1; v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e' = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concat_lhsE in blast)

lemma step_exp_concat_lhs_stepE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> (Val v\<^sub>2)) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' \<copyright> (Val v\<^sub>2))\<rbrakk> \<Longrightarrow> P\<close>
    shows P
using major proof (elim step_exp_concat_lhsE minor)
  fix sz\<^sub>1 :: nat
    and sz\<^sub>2 :: nat
    and str :: "char list"
    and v :: val
  assume "e\<^sub>1 = Val v"
  thus P
    using caveat by blast
next
  fix sz\<^sub>1 str assume "e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>" 
  thus P
    using caveat unknown_constructor_exp_def by blast
next
  fix num\<^sub>1 sz\<^sub>1 assume "e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1" 
  thus P
    using caveat word_constructor_exp_def by blast
qed

interpretation step_exp_concat_lhs_stepE: exp_val_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e'; \<forall>v. e\<^sub>1 \<noteq> (Val v); (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = (e\<^sub>1' \<copyright> e\<^sub>2)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concat_lhs_stepE in blast)


lemmas step_exp_concat_rhsE = ConcatRhsE

lemma step_exp_concat_rhs_stepE:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e\<close> 
      and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
      and minor: \<open>\<And>e\<^sub>2'. \<lbrakk>e = e\<^sub>1 \<copyright> e\<^sub>2'; \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat
  apply (elim step_exp_concat_rhsE minor)
  apply simp_all
  using unknown_constructor_exp_def apply blast
  using word_constructor_exp_def by blast

text \<open>Extract steps\<close>

lemma step_exp_extractE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)] \<leadsto> e\<close>
      and E: \<open>e = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2 \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim ExtractE step_exp_valE step_exp_valE.word E)

lemma step_exp_extract_unE:
  assumes \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t] \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim ExtractUnE step_exp_valE step_exp_valE.unknown)
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
  using assms(1) apply (elim CastLowE step_exp_valE step_exp_valE.word)
  by (rule E, simp)

interpretation step_exp_cast_lowE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> low:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_lowE in blast)

lemma step_exp_cast_highE:
  assumes \<open>\<Delta> \<turnstile> high:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz) \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastHighE step_exp_valE step_exp_valE.word)
  by (rule E, simp)

interpretation step_exp_cast_highE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ sz'. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> high:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_highE in blast)

lemma step_exp_cast_signedE:
  assumes \<open>\<Delta> \<turnstile> extend:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastSignedE step_exp_valE step_exp_valE.word)
  by (rule E, simp)

interpretation step_exp_cast_signedE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> extend:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_signedE in blast)

lemma step_exp_cast_unsignedE:
  assumes \<open>\<Delta> \<turnstile> pad:sz[(num \<Colon> sz')] \<leadsto> e\<close>
      and E: \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim CastUnsignedE step_exp_valE step_exp_valE.word)
  by (rule E, simp)

interpretation step_exp_cast_unsignedE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> pad:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_unsignedE in blast)

lemma step_exp_cast_unknownE:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> e\<close>
      and E: \<open>e = unknown[str]: imm\<langle>sz\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim CastUnkE step_exp_valE step_exp_valE.unknown E)

text \<open>Fallback rules\<close>

lemma step_exp_castE:
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

lemma step_exp_cast_reduceE:
  assumes major: \<open>\<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = Cast cast sz e\<^sub>1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat 
proof (elim step_exp_castE)
  fix e\<^sub>1' assume "\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'" "e = cast:sz[e\<^sub>1']"
  thus P by (rule minor)
qed (use word_constructor_exp_def unknown_constructor_exp_def in blast)+

text \<open>BOP steps\<close>

lemmas step_exp_plusE = PlusE[simplified]
lemmas step_exp_minusE = MinusE[simplified]
lemmas step_exp_timesE = TimesE[simplified]

lemma step_exp_divE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim DivE step_exp_valE step_exp_valE.word)

lemma step_exp_sdivE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim SDivE step_exp_valE step_exp_valE.word)

lemma step_exp_modE: 
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim ModE step_exp_valE step_exp_valE.word)

lemma step_exp_smodE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim SModE step_exp_valE step_exp_valE.word)

lemma step_exp_lslE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LslE step_exp_valE step_exp_valE.word)

lemma step_exp_lsrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LsrE step_exp_valE step_exp_valE.word)

lemma step_exp_asrE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim AsrE step_exp_valE step_exp_valE.word)

lemma step_exp_landE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LAndE step_exp_valE step_exp_valE.word)

lemma step_exp_lorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LOrE step_exp_valE step_exp_valE.word)

lemma step_exp_xorE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim XOrE step_exp_valE step_exp_valE.word)

lemma step_exp_eq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = true\<close>
  using assms(1) by (elim EqSameE step_exp_valE step_exp_valE.word)

lemma step_exp_neq_sameE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = false\<close>
  using assms by (elim NeqSameE step_exp_valE step_exp_valE.word)

lemma step_exp_eqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using assms(1) 
  by (metis EqDiffE bv_eq_def step_exp_eq_sameE step_exp_valE.word)
  
lemma step_exp_neqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using assms(1)
  by (metis  NeqDiffE bv_eq_def bv_negation_false_true bv_negation_true_false step_exp_neq_sameE step_exp_valE.word)

lemma step_exp_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LessE step_exp_valE step_exp_valE.word)

lemma step_exp_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim LessEqE step_exp_valE step_exp_valE.word)

lemma step_exp_signed_lessE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim SignedLessE step_exp_valE step_exp_valE.word)

lemma step_exp_signed_less_eqE:
  assumes \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using assms(1) by (elim SignedLessEqE step_exp_valE step_exp_valE.word)

text \<open>BOP - Generic\<close>

lemma step_exp_lop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e\<^sub>2 \<leadsto> e\<close>
      and EunknownL: \<open>e = unknown[str]: imm\<langle>1\<rangle> \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>str' t'. \<lbrakk>e\<^sub>2 = (unknown[str']: t'); e = unknown[str']: imm\<langle>1\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (unknown[str]: t) (LOp lop) e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim LopUnkRhsE step_exp_valE EunknownL EunknownR EunknownStep step_exp_valE.unknown)
  apply simp_all
  by (rule EunknownL, simp)

lemma step_exp_lop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (LOp lop) unknown[str]: t \<leadsto> e\<close>
      and EunknownR: \<open>e = unknown[str]: imm\<langle>1\<rangle> \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>str' t'. \<lbrakk>e\<^sub>1 = (unknown[str']: t'); e = unknown[str']: imm\<langle>1\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = BinOp e\<^sub>1' (LOp lop) (unknown[str]: t)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms apply (elim LopUnkLhsE step_exp_valE EunknownR EunknownL EunknownStep step_exp_valE.unknown)
  by simp_all

text \<open>Fallback rules\<close>

lemma step_exp_bop_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close>
      and Estep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (Val v) bop e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
      and EaopL: \<open>\<And>str t aop. \<lbrakk>e = unknown[str]: t; v = unknown[str]: t; bop = AOp aop\<rbrakk> \<Longrightarrow> P\<close>
      and ElopL: \<open>\<And>str t lop. \<lbrakk>e = unknown[str]: imm\<langle>1\<rangle>; v = unknown[str]: t; bop = LOp lop\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim BopRhsE Estep)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all

lemma step_exp_bop_rhs_strictE:
  assumes major: \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<leadsto> e\<close> 
      and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> Val v\<close> \<open>\<forall>str t. v \<noteq> unknown[str]: t\<close>
      and minor: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (Val v) bop e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (elim step_exp_bop_rhsE)
  using minor by auto

lemma step_exp_bop_lhs_strictE:
  assumes major: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>str t. e\<^sub>2 \<noteq> unknown[str]: t\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>e = BinOp e\<^sub>1' bop e\<^sub>2; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using major apply (rule BopLhsE)
  using assms(2-) unfolding word_constructor_exp_def unknown_constructor_exp_def by simp_all


text \<open>BOP Generic Syntax overloads\<close>

context bop_lemmas
begin

lemma step_exp_lhs_strictE:
  assumes major: \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close> and \<open>\<forall>str t. e\<^sub>2 \<noteq> unknown[str]: t\<close>
      and minor: \<open>\<And>e\<^sub>1'. \<lbrakk>e = bop_fun e\<^sub>1' e\<^sub>2; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding bop_simps by (rule step_exp_bop_lhs_strictE)

sublocale step_exp_rhs_strictE: exp_val_syntax \<open>\<lambda>e v. 
    (\<And>\<Delta> e\<^sub>2 e\<^sub>2' e'. \<lbrakk>\<Delta> \<turnstile> bop_fun e e\<^sub>2 \<leadsto> e'; \<forall>v. e\<^sub>2 \<noteq> Val v; \<forall>str t. v \<noteq> unknown[str]: t;
       (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = bop_fun e e\<^sub>2'\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
  apply standard
  unfolding bop_simps by (simp, rule step_exp_bop_rhs_strictE)

end

lemma step_exp_aop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e\<^sub>2 \<leadsto> e\<close>
      and EunknownL: \<open>e = unknown[str]: t \<Longrightarrow> P\<close>
      and EunknownR: \<open>\<And>str' t'. \<lbrakk>e\<^sub>2 = (unknown[str']: t'); e = unknown[str']: t'\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (unknown[str]: t) (AOp aop) e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (elim AopUnkRhsE step_exp_valE EunknownL EunknownR EunknownStep step_exp_valE.unknown)
  by simp

lemma step_exp_aop_unk_rhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (AOp aop) unknown[str]: t \<leadsto> e\<close>
      and EunknownR: \<open>e = unknown[str]: t \<Longrightarrow> P\<close>
      and EunknownL: \<open>\<And>str' t'. \<lbrakk>e\<^sub>1 = (unknown[str']: t'); e = unknown[str']: t'\<rbrakk> \<Longrightarrow> P\<close>
      and EunknownStep: \<open>\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = BinOp e\<^sub>1' (AOp aop) (unknown[str]: t)\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) by (elim AopUnkLhsE step_exp_valE EunknownL EunknownR EunknownStep step_exp_valE.unknown)
(*
context aop_lemmas
begin

lemma step_exp_unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_lhsI)

lemma step_exp_unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_rhsI)

end

lemmas step_lop_unk_rhsI = LopUnkRhs
lemmas step_lop_unk_lhsI = LopUnkLhs

context lop_lemmas
begin

lemma step_exp_unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_lhsI)

lemma step_exp_unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_rhsI)

end
*)




(**




Auto solver




**)

method erulel uses rules = (erule rules, print_fact rules) (* TODO delete when done*)

method solve_expE_scaffold methods recurs solve_type uses add
  \<open>Scaffold method for deconstructing expression relations as premises (elimination rules).
   This should not be called directly.\<close> = (

\<comment> \<open>Var\<close>
  (erule step_exp_var_inE.word step_exp_var_inE, solve_in_var, clarify) |

\<comment> \<open>BinOps\<close>
  (erule step_exp_plusE step_exp_eq_sameE step_exp_eqE, clarify) |
  (erule plus.step_exp_lhs_strictE step_exp_bop_lhs_strictE, 
      solves fastforce, solves fastforce, clarify, recurs) |
                          
\<comment> \<open>Cast\<close>
  (erule step_exp_cast_highE step_exp_cast_lowE step_exp_cast_signedE step_exp_cast_unsignedE, 
     clarify) |
  (erule step_exp_cast_highE.is_word[rotated]   step_exp_cast_lowE.is_word[rotated] 
         step_exp_cast_signedE.is_word[rotated] step_exp_cast_unsignedE.is_word[rotated],
     prefer_last, solve_is_wordI, clarify) |
  (erule step_exp_cast_reduceE, solves clarify, clarify, recurs) |

\<comment> \<open>Store\<close>
  (erule step_exp_store_el_manyE.word.val.word[rotated], 
     prefer_last, solve_type, linarith, (unfold load_byte_minus_simps)?, clarify) |
  (erule step_exp_store_el_manyE.is_val3[rotated 4],
     prefer_last, solve_is_valI,
     prefer_last, solve_is_wordI,
     prefer_last, solve_is_valI,
     prefer_last, solve_type, 
     linarith, (unfold load_byte_minus_simps)?, clarify) |
  (erule step_exp_store_singleE.is_val3[rotated 4],
     prefer_last, solve_is_valI,
     prefer_last, solve_is_wordI,
     prefer_last, solve_is_valI,
     prefer_last, solve_type, 
     clarify) |
  (erule step_exp_store_step_addr_strictE.word step_exp_store_step_addr_strictE,
     solves fastforce, clarify, recurs) |
  (erule step_exp_store_step_val_strictE, fastforce, clarify, recurs) |
  (erule step_exp_store_step_mem_strictE.is_val2[rotated 2], fastforce,
     prefer_last, solve_is_valI,
     prefer_last, solve_is_valI,
     clarify, recurs) |

\<comment> \<open>Load\<close>
  (erule step_exp_load_byte_from_nextE.word.storage, solve_word_neq add: add, clarify) |
  (erule step_exp_load_byte_from_nextE.is_word2[rotated 2],
     prefer_last, solve_is_valI,
     prefer_last, solve_is_wordI,
     solve_word_neq add: add, clarify) |
  (erulel rules: step_exp_load_word_el_memE, linarith, (unfold load_byte_minus_simps)?, clarify) |
  (erule step_exp_load_word_el_memE.is_word[rotated], linarith, (unfold load_byte_minus_simps)?,
     prefer_last, solve_is_wordI, clarify) |
  (erulel rules: step_exp_load_byte_eqE.is_word2[rotated 2],
     prefer_last, solve_is_valI, 
     prefer_last, solve_is_wordI, 
     clarify) |
  (erule step_exp_load_step_mem_strictE.is_val[rotated],
           prefer_last, solve_is_valI, fastforce, recurs) |
  (erule step_exp_load_step_addr_strictE, fastforce, recurs) |

\<comment> \<open>Concatenate\<close>
  (erule step_exp_concatE.is_word2[rotated 2],
           prefer_last, solve_is_wordI,
           prefer_last, solve_is_wordI, clarify) |
  (erule step_exp_concat_lhs_stepE.is_val[rotated], solves clarify,
     prefer_last, solve_is_valI,
     clarify, recurs) |
  (erulel rules: step_exp_concat_rhs_stepE, solves clarify, clarify, recurs)
)

method solve_expE uses add
  \<open>Scaffold method for deconstructing expression relations as premises (elimination rules)\<close> = (
  solve_expE_scaffold \<open>solve_expE add: add\<close> solve_typeI add: add
)

end
