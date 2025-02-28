section \<open>Elimination rules for expressions\<close>

theory Expression_Elims
  imports Expression_Rules Solve_BitVector
begin

(* TODO *)
lemma Val_word[simp]: \<open>Val v = num \<Colon> sz \<longleftrightarrow> v = num \<Colon> sz\<close> \<open>num \<Colon> sz = Val v \<longleftrightarrow> num \<Colon> sz = v\<close>
  by (simp_all add: word_constructor_exp_def)

lemma Val_unknown[simp]: \<open>Val v = (unknown[str]: t) \<longleftrightarrow> (v = unknown[str]: t)\<close>
    \<open>(unknown[str]: t) = Val v \<longleftrightarrow> ((unknown[str]: t) = v)\<close>
  by (simp_all add: unknown_constructor_exp_def)

lemma word_not_valE[elim]: assumes \<open>\<forall>v. (num \<Colon> sz) \<noteq> Val v\<close> shows P
  using assms word_constructor_exp_def by blast

lemma unknown_not_valE[elim]: assumes \<open>\<forall>v. (unknown[str]: t) \<noteq> Val v\<close> shows P
  using assms unknown_constructor_exp_def by blast

subsection \<open>Val\<close>

lemmas step_exp_valE[elim!] = ValE

interpretation step_exp_valE: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' P. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_valE, blast+)

subsection \<open>Var\<close>

lemmas step_exp_varE = VarE

lemma step_exp_var_inE[elim]:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> e\<close>
      and \<open>((id' :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    obtains (Val) \<open>e = (Val v)\<close>
using assms(1) proof (elim step_exp_varE)
  fix val 
  assume val_e: \<open>e = Val val\<close>
  assume \<open>((id' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  then have \<open>e = (Val v)\<close>
    using assms(2) apply -
    apply (drule var_in_deterministic, blast)
    using val_e by blast
  thus ?thesis
    by (rule Val)
qed (use assms(2) in \<open>simp_all add: var_in_dom_\<Delta>\<close>)

interpretation step_exp_var_inE: exp_val_syntax \<open>\<lambda>e' v. (\<And>\<Delta> id t P e. \<Delta> \<turnstile> (id :\<^sub>t t) \<leadsto> e \<Longrightarrow> ((id :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> (e = e' \<Longrightarrow> P) \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_var_inE, blast+)

lemma step_exp_var_unknownE[elim]:
  assumes \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> e\<close>
      and \<open>(id' :\<^sub>t t) \<notin> dom \<Delta>\<close>
  obtains (elim) str where \<open>e = unknown[str]: t\<close>
using assms(1) proof (elim VarE)
  fix val assume is_in: \<open>(id' :\<^sub>t t, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
  show ?thesis
    using var_in_dom_\<Delta>[OF is_in] assms(2) by simp
next
  fix str 
  assume unknown_e: \<open>e = unknown[str]: t\<close>
  thus ?thesis by (rule elim)
qed

subsection \<open>Load\<close>

lemma step_exp_load_byteE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e\<close> 
  obtains (Eq) \<open>w = (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> \<open>e = Val v'\<close>
        | (Neq) \<open>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> \<open>e = ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<close>
using major proof (elim LoadByteFromNextE step_exp_valE.word step_exp_valE.storage Eq Neq)
  fix sz\<^sub>m\<^sub>e\<^sub>m :: nat and va :: val
  assume "sz\<^sub>m\<^sub>e\<^sub>m < sz"
    and "type va = mem\<langle>sz\<^sub>2, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
    and "v[w \<leftarrow> v', sz] = Val va"
  thus ?thesis
    unfolding Val_simp_storage[symmetric] apply clarify
    apply (cases w rule : word_exhaust, clarify)
    by (elim type_storageE, clarify)
next
  fix va :: val
    and sz\<^sub>m\<^sub>e\<^sub>m :: nat
  assume "type va = mem\<langle>sz\<^sub>2, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
    and "sz\<^sub>m\<^sub>e\<^sub>m < sz"
    and "v[w \<leftarrow> v', sz] = Val va"
  thus ?thesis
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

lemma step_exp_load_byte_eqE[elim]: 
  assumes major: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> e\<close> 
  obtains \<open>e = Val v'\<close>
  using assms(1) apply (elim step_exp_load_byteE)
  by auto

interpretation step_exp_load_byte_eqE: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e' v'. (\<And>\<Delta> e v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r ed sz P. \<lbrakk>
    \<Delta> \<turnstile> v[w\<^sub>w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e; e = e' \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_byte_eqE in blast)

lemma step_exp_load_byte_from_nextE[elim]: 
  assumes major: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz \<leadsto> e\<close> 
      and caveat: \<open>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    obtains \<open>e = ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<close>
  using major by (elim step_exp_load_byteE, use caveat in simp)

(* TODO incorrect precedence - should be val.word not word.val ? *)
interpretation step_exp_load_byte_from_nextE: exp_val2_word_sz1_syntax \<open>\<lambda>w\<^sub>e _ w\<^sub>w _ e v. 
    (\<And>\<Delta> w v' ed sz P e'. \<lbrakk>
    \<Delta> \<turnstile> v[w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e'; w \<noteq> w\<^sub>w; 
    (\<lbrakk>e' = (e[w\<^sub>e, ed]:usz)\<rbrakk> \<Longrightarrow> P)\<rbrakk> 
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_byte_from_nextE in blast)

lemmas step_exp_load_un_addrE[elim] = LoadUnAddrE[simplified]

lemma step_exp_load_un_memE[elim]:
  assumes \<open>\<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[Val v, ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e\<close> 
  obtains (Unk) \<open>e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms(1) apply (elim LoadUnMemE step_exp_valE.storage step_exp_valE.unknown Unk)
  using unknown_constructor_exp_def by force+

interpretation step_exp_load_un_memE: exp_val_syntax \<open>\<lambda>e' _. (\<And>\<Delta> str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m ed  P e. \<lbrakk>
  \<Delta> \<turnstile> (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)[e', ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leadsto> e; e = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_load_un_memE in blast)

lemma step_exp_load_word_beE[elim]: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> e\<close>
  obtains (Single) va v' where \<open>v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz])\<close> \<open>e = Val v'\<close>
        | (Next) w va v' where \<open>v = (va[w \<leftarrow> v', sz])\<close> \<open>e = ((Val va)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz)\<close>
                    \<open>w \<noteq> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
        | (unk) str t where \<open>e = unknown[str]: imm\<langle>sz\<rangle>\<close> \<open>v = unknown[str]: t\<close>
        | (many) sz\<^sub>m\<^sub>e\<^sub>m where \<open>e = ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))\<close>
                    \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms(1) apply (elim LoadWordBeE step_exp_valE step_exp_valE.word unk many)
  subgoal for va v' 
    apply (rule Single[of va v'])
    unfolding storage_constructor_exp_def by simp_all
  subgoal for va v' 
    apply (rule Next)
    unfolding storage_constructor_exp_def by simp_all
  unfolding unknown_constructor_exp_def by simp_all

lemma step_exp_load_word_elE[elim]: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>
  obtains (Single) va v' where \<open>v = (va[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz])\<close> \<open>e = Val v'\<close>
        | (Next) w va v' where \<open>v = (va[w \<leftarrow> v', sz])\<close> \<open>e = ((Val va)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz)\<close>
                    \<open>w \<noteq> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
        | (unk) str t where \<open>e = unknown[str]: imm\<langle>sz\<rangle>\<close> \<open>v = unknown[str]: t\<close>
        | (many) sz\<^sub>m\<^sub>e\<^sub>m where \<open>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)\<close>
                    \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    using assms(1) apply (elim LoadWordElE step_exp_valE step_exp_valE.word unk many)
  subgoal for va v' 
    apply (rule Single[of va v'])
    unfolding storage_constructor_exp_def by simp_all
  subgoal for va v' 
    apply (rule Next)
    unfolding storage_constructor_exp_def by simp_all
  unfolding unknown_constructor_exp_def by simp_all

lemma Val_storage_eq: \<open>(Val v) = (va[w \<leftarrow> v', sz]) \<longleftrightarrow> (v = (va[w \<leftarrow> v', sz]))\<close>
  by (simp add: storage_constructor_exp_def)

lemma step_exp_load_word_el_strictE[elim]: 
  assumes \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>
      and caveat: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
  obtains (unk) str t where \<open>e = unknown[str]: imm\<langle>sz\<rangle>\<close> \<open>v = unknown[str]: t\<close>
        | (many) \<open>e = ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)\<close>
  using assms(1) apply (elim LoadWordElE step_exp_valE step_exp_valE.word unk many)
  subgoal for va v' 
    using caveat apply auto
    unfolding Val_storage_eq by auto
  subgoal for va v' 
    using caveat apply auto
    unfolding Val_storage_eq by (cases va rule: word_exhaust, auto)
  using caveat  unfolding unknown_constructor_exp_def by simp_all

interpretation step_exp_load_word_el_strictE: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. 
  (\<And>\<Delta> sz v e sz\<^sub>m\<^sub>e\<^sub>m P. \<lbrakk>\<Delta> \<turnstile> (Val v)[e\<^sub>2, el]:usz \<leadsto> e; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m < sz; 
      (\<And>str t. \<lbrakk>e = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: t\<rbrakk> \<Longrightarrow> P);
      (\<lbrakk>e = (((Val v)[succ e\<^sub>2, el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> ((Val v)[e\<^sub>2, el]:usz\<^sub>m\<^sub>e\<^sub>m))\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  apply (standard)
  using step_exp_load_word_el_strictE by blast

lemma step_exp_load_word_el_memE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>
      and caveat: \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
  obtains (minor) \<open>e = (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)\<close>
                  \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
  using major caveat
  unfolding Val_simp_storage[symmetric]
  apply (elim step_exp_load_word_elE)
  apply simp_all
  apply (rule minor)
  apply (metis Type.inject(2) storage_constructor_exp_def type_storageI type_word.elims)
  by (metis Type.inject(2) type_storage_addrI type_word.elims)

interpretation step_exp_load_word_el_memE: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. 
  (\<And>\<Delta> sz v w v' e sz\<^sub>m\<^sub>e\<^sub>m P. \<lbrakk>\<Delta> \<turnstile> v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][e\<^sub>2, el]:usz \<leadsto> e; sz\<^sub>m\<^sub>e\<^sub>m < sz; (
      \<lbrakk>e = ((v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][succ e\<^sub>2, el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m)) \<copyright> (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m][e\<^sub>2, el]:usz\<^sub>m\<^sub>e\<^sub>m)); type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<rbrakk> \<Longrightarrow> P)
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
lemmas step_exp_load_step_memE[elim] = LoadStepMemE[simplified]

lemma step_exp_load_step_mem_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>1' where \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> \<open>e = (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close>
  using major caveat apply (elim step_exp_load_step_memE minor)
  using storage_constructor_exp_def unknown_constructor_exp_def word_constructor_exp_def by auto

interpretation step_exp_load_step_mem_strictE: exp_val_syntax \<open>\<lambda>e\<^sub>2 _. 
  (\<And>\<Delta> e\<^sub>1 e sz ed P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e; \<forall>v. e\<^sub>1 \<noteq> (Val v); 
      (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1'[e\<^sub>2, ed]:usz)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  apply (standard)
  using step_exp_load_step_mem_strictE by blast

lemmas step_exp_load_step_addrE[elim] = LoadStepAddrE

lemma step_exp_load_step_addr_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>2' where \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close> \<open>e = (e\<^sub>1[e\<^sub>2', ed]:usz)\<close>
  using major caveat apply (elim step_exp_load_step_addrE minor)
  using unknown_constructor_exp_def word_constructor_exp_def by auto

subsection \<open>Store\<close>

lemmas step_exp_store_un_addrE[elim] = StoreUnAddrE[simplified]

interpretation step_exp_store_un_addrE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 _. (\<And>\<Delta> str t ed sz e P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [unknown[str]: t, ed]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; (e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_un_addrE in blast)

lemma step_exp_store_singleE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz \<leftarrow> (Val v')) \<leadsto> e\<close> 
      and caveat: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
  obtains (minor) \<open>e = (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])\<close>
using major proof (elim StoreWordE step_exp_valE step_exp_valE.word minor)
  fix sz\<^sub>m\<^sub>e\<^sub>m assume gt: "sz\<^sub>m\<^sub>e\<^sub>m < sz" and type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close>
    using type caveat by fastforce
  thus ?thesis
    using gt by fastforce
next
  fix sz\<^sub>m\<^sub>e\<^sub>m assume gt: "sz\<^sub>m\<^sub>e\<^sub>m < sz" and type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close>
    using type caveat by fastforce
  thus ?thesis
    using gt by fastforce
qed

interpretation step_exp_store_singleE: store_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 _ w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. 
  (\<And>\<Delta> e en. \<lbrakk>
    \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>3) \<leadsto> e;
    (e = (v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m]) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_singleE in blast)

lemmas step_exp_store_elE[elim] = StoreWordElE[simplified]

interpretation step_exp_store_elE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> e num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_elE in blast)

lemma step_exp_store_el_manyE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val v')) \<leadsto> e\<close>
      and caveat: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
  obtains (minor) \<open>e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[Val v'])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[Val v']))\<close>
using major caveat proof (elim step_exp_store_elE minor)
  fix sz\<^sub>m\<^sub>e\<^sub>m' :: nat
  assume type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>" "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m'\<rangle>"
    and major: "e = (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m' \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m'[Val v'])) 
                              with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m') \<leftarrow> (high:(sz - sz\<^sub>m\<^sub>e\<^sub>m')[Val v']))"
  have sz\<^sub>m\<^sub>e\<^sub>m: \<open>sz\<^sub>m\<^sub>e\<^sub>m' = sz\<^sub>m\<^sub>e\<^sub>m\<close>
    using type_determ[OF type] by simp
  show ?thesis
    using major[unfolded sz\<^sub>m\<^sub>e\<^sub>m] by (rule minor )
next
  assume type: "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>" "type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>"
    and sz_neq: "sz\<^sub>m\<^sub>e\<^sub>m < sz"
  have \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<close> 
    using type_determ[OF type] by simp
  thus ?thesis
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

lemmas step_exp_store_beE[elim] = StoreWordBeE[simplified]

interpretation step_exp_store_beE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>3 v\<^sub>1 v\<^sub>3. (\<And>\<Delta> num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> e\<^sub>3) \<leadsto> e;
      (\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
         e = ((e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>3])) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (low:(sz - sz\<^sub>m\<^sub>e\<^sub>m)[e\<^sub>3]))\<rbrakk>
        \<Longrightarrow> P);
      (\<lbrakk>e = (v\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>3, sz]); type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_beE in blast)

text \<open>Fallback steps\<close>

lemmas step_exp_store_step_memE[elim] = StoreStepMemE[simplified]

lemma step_exp_store_step_mem_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>1' where \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> \<open>e = (e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3))\<close>
  using major apply (elim step_exp_store_step_memE minor)
  using caveat by simp_all

interpretation step_exp_store_step_mem_strictE: exp2_val_syntax \<open>\<lambda>e\<^sub>2 e\<^sub>3 _ _. (\<And>\<Delta> e e\<^sub>1 en sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; \<forall>v. e\<^sub>1 \<noteq> (Val v);
      (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e = (e\<^sub>1' with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_step_mem_strictE in blast)

lemmas step_exp_store_step_addrE[elim] = StoreStepAddrE[simplified]

lemma step_exp_store_step_addr_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
      and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>2' where \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close> \<open>e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close>
using major proof (elim step_exp_store_step_addrE)
  fix e\<^sub>2' assume "\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'" "e = e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3)"
  thus ?thesis by (rule minor)
qed(use caveat unknown_constructor_exp_def word_constructor_exp_def in blast)+

interpretation step_exp_store_step_addr_strictE: exp_val_syntax \<open>\<lambda>e\<^sub>3 _. 
  (\<And>\<Delta> e e\<^sub>1 e\<^sub>2 en sz P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> e; \<forall>v. e\<^sub>2 \<noteq> (Val v);
      (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e\<^sub>3)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_store_step_addr_strictE in blast)

lemmas step_exp_store_step_valE[elim] = StoreStepValE

lemma step_exp_store_step_val_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3 \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>3 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>3' where \<open>e = (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
  using major apply (elim step_exp_store_step_valE minor)
  using caveat by simp_all

subsection \<open>Let steps\<close>

lemmas step_exp_letE[elim] = LetE[simplified]

interpretation step_exp_letE: exp_val_syntax \<open>\<lambda>e'' v. (\<And>\<Delta> var e e' P. \<lbrakk>\<Delta> \<turnstile> (Let var e'' e) \<leadsto> e'; e' = [v\<sslash>var]e \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, rule step_exp_letE, blast+)

text \<open>Fallback steps\<close>

lemmas step_exp_step_letE[elim] = LetStepE

lemma step_exp_step_let_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> Let var e\<^sub>1 e\<^sub>2 \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>1' where \<open>e = (Let var e\<^sub>1' e\<^sub>2)\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
  using major apply (elim step_exp_step_letE minor)
  using caveat by simp_all

text \<open>Ite steps\<close>

lemmas step_exp_if_trueE[elim] = IfTrueE[simplified]
 
interpretation step_exp_ite_trueE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>1 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_trueE in blast)

lemmas step_exp_if_falseE[elim] = IfFalseE[simplified]

interpretation step_exp_ite_falseE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e P. \<lbrakk>
      \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto> e; e = e\<^sub>2 \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_falseE in blast)

lemmas step_exp_if_unknownE[elim] = IfUnknownE[simplified]

interpretation step_exp_if_unknownE: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> e str t P. \<lbrakk>
      \<Delta> \<turnstile> ite (unknown[str]: t) e\<^sub>1 e\<^sub>2 \<leadsto> e; e = unknown[str]: (type v\<^sub>1) \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_unknownE in blast)
(* TODO further optimisations with type *)
(* TODO rename unknown_constructor_exp_def to unknown_exp_def*)

text \<open>Fallback steps\<close>

lemmas step_exp_if_step_condE[elim] = IfStepCondE[simplified]

lemma step_exp_if_step_cond_strictE[elim]:
  assumes major:  \<open>\<Delta> \<turnstile> ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3) \<leadsto> e\<close> and caveat:  \<open>\<forall>v\<^sub>1. e\<^sub>1 \<noteq> Val v\<^sub>1\<close>
  obtains e\<^sub>1' where \<open>e = ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
  using major caveat apply (elim step_exp_if_step_condE)
  by auto

interpretation step_exp_if_step_condE: exp2_val_syntax \<open>\<lambda>e\<^sub>2 e\<^sub>3 v\<^sub>2 _. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = ite e\<^sub>1' e\<^sub>2 e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<lbrakk>e\<^sub>1 = true; e' = e\<^sub>2\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t. \<lbrakk>e\<^sub>1 = unknown[str]: t; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_step_condE in blast)

lemmas step_exp_if_step_thenE[elim] = IfStepThenE[simplified]

lemma step_exp_if_step_then_strictE[elim]:
  assumes major:  \<open>\<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3) \<leadsto> e\<close> and caveat:  \<open>\<forall>v\<^sub>2. e\<^sub>2 \<noteq> Val v\<^sub>2\<close>
  obtains e\<^sub>2' where \<open>e = ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<close> \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
  using major caveat apply (elim step_exp_if_step_thenE)
  by auto

interpretation step_exp_if_step_thenE: exp_val_syntax \<open>\<lambda>e\<^sub>3 _. (\<And>\<Delta> e\<^sub>1 e\<^sub>2 e' P. \<lbrakk>
      \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e'; (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = (ite e\<^sub>1 e\<^sub>2' e\<^sub>3)\<rbrakk> \<Longrightarrow> P);
      (\<And>e\<^sub>1' v\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e\<^sub>2 = (Val v\<^sub>2); e' = ite e\<^sub>1' (Val v\<^sub>2) e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>v\<^sub>2. \<lbrakk>e\<^sub>1 = true; e\<^sub>2 = (Val v\<^sub>2); e' = (Val v\<^sub>2)\<rbrakk> \<Longrightarrow> P); (\<lbrakk>e\<^sub>1 = false; e' = e\<^sub>3\<rbrakk> \<Longrightarrow> P);
      (\<And>str t v\<^sub>2. \<lbrakk>e\<^sub>1 = unknown[str]: t; e\<^sub>2 = Val v\<^sub>2; e' = unknown[str]: (type v\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_if_step_thenE in blast)

lemmas step_exp_if_step_elseE = IfStepElseE

lemma step_exp_if_step_else_strictE[elim]:
  assumes major:  \<open>\<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 \<leadsto> e\<close> and caveat:  \<open>\<forall>v\<^sub>1. e\<^sub>3 \<noteq> Val v\<^sub>1\<close>
  obtains e\<^sub>3' where \<open>e = ite e\<^sub>1 e\<^sub>2 e\<^sub>3'\<close> \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
  using major caveat apply (elim step_exp_if_step_elseE)
  by auto

text \<open>Uop steps\<close>

lemmas step_exp_uop_unkE[elim] = UopUnkE[simplified]

lemmas step_exp_notE[elim] = NotE[simplified]
interpretation step_exp_notE: exp_val_word_sz_syntax 
    \<open>\<lambda>e\<^sub>1 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (\<sim> e\<^sub>1) \<leadsto> e; e = ~\<^sub>b\<^sub>v e\<^sub>1 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_notE in blast)

lemmas step_exp_negE[elim] = NegE[simplified]
interpretation step_exp_negE: exp_val_word_sz_syntax 
    \<open>\<lambda>e\<^sub>1 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (- e\<^sub>1) \<leadsto> e; e = -\<^sub>b\<^sub>v e\<^sub>1 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_negE in blast)

text \<open>Fallback steps\<close>

lemmas step_exp_uopE[elim] = UopE

lemma step_exp_uop_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> UnOp uop e \<leadsto> e''\<close> and caveat: \<open>\<forall>v. e \<noteq> Val v\<close>
  obtains (Step) e' where  \<open>e'' = UnOp uop e'\<close> \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
using major proof (rule step_exp_uopE)
  fix e' :: exp
  assume asm: "e'' = UnOp uop e'"  "\<Delta> \<turnstile> e \<leadsto> e'"
  thus thesis by (rule Step)
qed (use caveat in auto)

text \<open>UOP Generic Syntax overloads\<close>

context uop_lemmas
begin

lemma step_exp_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> uop_fun e\<^sub>1 \<leadsto> e\<close> and \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
  obtains e\<^sub>1' where \<open>e = uop_fun e\<^sub>1'\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
  using assms unfolding uop_simps by (rule step_exp_uop_strictE)

end

text \<open>Concat steps\<close>

lemmas step_exp_concatE[elim] = ConcatE[simplified]

interpretation step_exp_concatE: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e; e = e\<^sub>1 \<cdot> e\<^sub>2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concatE in blast)

lemma step_exp_concat_rhs_unE[elim]:
  assumes \<open>\<Delta> \<turnstile> ((Val v) \<copyright> unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
  obtains (1) sz\<^sub>1 str' where \<open>v = unknown[str']: imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
        | (2) sz\<^sub>1 where \<open>type v = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
using assms proof (elim ConcatRhsUnE [simplified])
qed auto

lemma step_exp_concat_lhs_unE[elim]:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> (Val v)) \<leadsto> e\<close>
  obtains (1) sz\<^sub>2 str' where \<open>v = unknown[str']: imm\<langle>sz\<^sub>2\<rangle>\<close> \<open>e = unknown[str']: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
        | (2) sz\<^sub>2 where \<open>type v = imm\<langle>sz\<^sub>2\<rangle>\<close> \<open>e = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
using assms proof (elim ConcatLhsUnE[simplified])
qed auto

lemma step_exp_concat_unE[elim]:
  assumes \<open>\<Delta> \<turnstile> ((unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> unknown[str\<^sub>2]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> e\<close>
  obtains (1) \<open>e = unknown[str\<^sub>1]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
        | (2) \<open>e = unknown[str\<^sub>2]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms(1) apply (elim ConcatRhsE)
  by auto

text \<open>Fallback rules\<close>

lemmas step_exp_concat_lhsE[elim] = ConcatLhsE[simplified]

(* Lots of optimisations? *)
interpretation step_exp_concat_lhsE: exp_val_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e'; (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = (e\<^sub>1' \<copyright> e\<^sub>2)\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str v. \<lbrakk>type v = imm\<langle>sz\<^sub>1\<rangle>; e\<^sub>1 = Val v; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>sz\<^sub>1 sz\<^sub>2 str. \<lbrakk>e\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>; e' = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> P);
      (\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>1; v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>2; e' = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P)      
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concat_lhsE in blast)

lemma step_exp_concat_lhs_stepE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> (Val v\<^sub>2)) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>1' where \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> \<open>e = (e\<^sub>1' \<copyright> (Val v\<^sub>2))\<close>
using major caveat by (elim step_exp_concat_lhsE minor, auto)

interpretation step_exp_concat_lhs_stepE: exp_val_syntax \<open>\<lambda>e\<^sub>2 v\<^sub>2. (\<And>\<Delta> e\<^sub>1 e' P. \<lbrakk>
      \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e'; \<forall>v. e\<^sub>1 \<noteq> (Val v); (\<And>e\<^sub>1'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'; e' = (e\<^sub>1' \<copyright> e\<^sub>2)\<rbrakk> \<Longrightarrow> P)
    \<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_concat_lhs_stepE in blast)

lemmas step_exp_concat_rhsE[elim] = ConcatRhsE

lemma step_exp_concat_rhs_stepE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e\<close> 
      and caveat: \<open>\<forall>v. e\<^sub>2 \<noteq> (Val v)\<close>
  obtains (minor) e\<^sub>2' where \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close> \<open>e = e\<^sub>1 \<copyright> e\<^sub>2'\<close>
  using major caveat
  apply (elim step_exp_concat_rhsE minor)
  by simp_all

text \<open>Extract steps\<close>

lemmas step_exp_extractE[elim] = ExtractE[simplified]
lemmas step_exp_extract_unE[elim] = ExtractUnE[simplified]

text \<open>Fallback rules\<close>

lemmas step_exp_extract_reduceE[elim] = ExtractReduceE[simplified]

lemma step_exp_extract_reduce_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e] \<leadsto> e'\<close> 
      and caveat: \<open>\<forall>v. e \<noteq> (Val v)\<close>
    obtains (minor) e\<^sub>1 where \<open>\<Delta> \<turnstile> e \<leadsto> e\<^sub>1\<close> \<open>e' = extract:sz\<^sub>1:sz\<^sub>2[e\<^sub>1]\<close>
  using major caveat apply (elim step_exp_extract_reduceE)
  by simp_all

text \<open>Cast steps\<close>

lemma step_exp_cast_lowE[elim]: (* TODO many erules have been kept to avoid Suc 0 issues *)
  assumes \<open>\<Delta> \<turnstile> low:sz[(num \<Colon> sz')] \<leadsto> e\<close>
  obtains \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (elim CastLowE[simplified] step_exp_valE step_exp_valE.word)
  by simp

interpretation step_exp_cast_lowE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> low:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_lowE in blast)

lemma step_exp_cast_highE[elim]:
  assumes \<open>\<Delta> \<turnstile> high:sz[(num \<Colon> sz')] \<leadsto> e\<close>
  obtains \<open>e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz)\<close>
  using assms(1) apply (elim CastHighE step_exp_valE step_exp_valE.word)
  by simp

interpretation step_exp_cast_highE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ sz'. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> high:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_highE in blast)

lemma step_exp_cast_signedE[elim]:
  assumes \<open>\<Delta> \<turnstile> extend:sz[(num \<Colon> sz')] \<leadsto> e\<close>
  obtains \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (elim CastSignedE step_exp_valE step_exp_valE.word)
  by simp

interpretation step_exp_cast_signedE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> extend:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_signedE in blast)

lemma step_exp_cast_unsignedE[elim]:
  assumes \<open>\<Delta> \<turnstile> pad:sz[(num \<Colon> sz')] \<leadsto> e\<close>
  obtains \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
  using assms(1) apply (elim CastUnsignedE step_exp_valE step_exp_valE.word)
  by simp

interpretation step_exp_cast_unsignedE: exp_val_word_sz_syntax \<open>\<lambda>e _ _ _. 
    (\<And>\<Delta> sz e' P. \<lbrakk>\<Delta> \<turnstile> pad:sz[e] \<leadsto> e'; e' = ext e \<sim> hi : sz - 1 \<sim> lo : 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_cast_unsignedE in blast)

lemmas step_exp_cast_unknownE[elim] = CastUnkE[simplified]

text \<open>Fallback rules\<close>

lemma step_exp_castE[elim]:
  assumes \<open>\<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<leadsto> e\<close>
  obtains (step) e\<^sub>1' where \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> \<open>e = Cast cast sz e\<^sub>1'\<close>
        | (low) num sz' where \<open>cast = low\<close> \<open>e\<^sub>1 = num \<Colon> sz'\<close> \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
        | (high) num sz' where \<open>cast = high\<close> \<open>e\<^sub>1 = num \<Colon> sz'\<close> \<open>e = ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : (sz' - sz)\<close>
        | (signed) num sz' where \<open>cast = extend\<close> \<open>e\<^sub>1 = num \<Colon> sz'\<close> \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
        | (unsigned) num sz' where \<open>cast = pad\<close> \<open>e\<^sub>1 = num \<Colon> sz'\<close> \<open>e = ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
        | (unknown) str t where \<open>e\<^sub>1 = unknown[str]: t\<close> \<open>e = unknown[str]: imm\<langle>sz\<rangle>\<close>
  using assms(1) apply (elim CastReduceE step low high signed unsigned unknown)
  by simp_all

lemma step_exp_cast_reduceE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (Cast cast sz e\<^sub>1) \<leadsto> e\<close> and caveat: \<open>\<forall>v. e\<^sub>1 \<noteq> Val v\<close>
  obtains (minor) e\<^sub>1' where \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close> \<open>e = Cast cast sz e\<^sub>1'\<close>
using major caveat proof (elim step_exp_castE)
  fix e\<^sub>1' assume "\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'" "e = (cast:sz[e\<^sub>1'])" thus ?thesis by (rule minor)
qed (use word_constructor_exp_def unknown_constructor_exp_def in blast)+

text \<open>BOP steps\<close>

lemmas step_exp_plusE[elim] = PlusE[simplified]
interpretation step_exp_plusE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 + e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 +\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_plusE by blast

lemmas step_exp_minusE[elim] = MinusE[simplified]
interpretation step_exp_minusE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 - e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 -\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_minusE by blast

lemmas step_exp_timesE[elim] = TimesE[simplified]
interpretation step_exp_timesE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 * e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 *\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_timesE by blast

lemmas step_exp_divE[elim] = DivE[simplified]
lemmas step_exp_sdivE[elim] = SDivE[simplified]
lemmas step_exp_modE[elim] = ModE[simplified]
lemmas step_exp_smodE[elim] = SModE[simplified]
lemmas step_exp_lslE[elim] = LslE[simplified]
interpretation step_exp_lslE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 << e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 <<\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_lslE by blast

lemmas step_exp_lsrE[elim] = LsrE[simplified]
interpretation step_exp_lsrE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 >> e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 >>\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_lsrE by blast

lemmas step_exp_asrE[elim] = AsrE[simplified]
interpretation step_exp_asrE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 >>> e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 >>>\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_asrE by blast

lemmas step_exp_landE[elim] = LAndE[simplified]
interpretation step_exp_landE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 && e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 &\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_landE by blast

lemmas step_exp_lorE[elim] = LOrE[simplified]
interpretation step_exp_lorE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 || e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 |\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_lorE by blast

lemmas step_exp_xorE[elim] = XOrE[simplified]
interpretation step_exp_xorE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 xor e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 xor\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_xorE by blast

lemmas step_exp_eq_sameE[elim] = EqSameE[simplified]
lemmas step_exp_neq_sameE[elim] = NeqSameE[simplified]
lemmas step_exp_lessE[elim] = LessE[simplified]
interpretation step_exp_lessE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 lt e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 <\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_lessE by blast

lemmas step_exp_less_eqE[elim] = LessEqE[simplified]
interpretation step_exp_less_eqE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (e\<^sub>1 le e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 \<le>\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_less_eqE by blast

lemmas step_exp_signed_lessE[elim] = SignedLessE[simplified]
lemmas step_exp_signed_less_eqE[elim] = SignedLessEqE[simplified]

lemma step_exp_eqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using assms(1) 
  by (metis EqDiffE bv_eq_def step_exp_eq_sameE step_exp_valE.word)

interpretation step_exp_eqE: exp_val_word_fixed_sz_syntax2
    \<open>\<lambda>e\<^sub>1 _ _ _ e\<^sub>2 _ _ _. (\<And>\<Delta> e P. \<lbrakk>\<Delta> \<turnstile> (BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) \<leadsto> e; e = (e\<^sub>1 =\<^sub>b\<^sub>v e\<^sub>2) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> sz sz
  apply (standard) 
  using step_exp_eqE by blast

lemma step_exp_neqE:
  assumes \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>
  obtains \<open>e = (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  using assms(1)
  by (metis  NeqDiffE bv_eq_def bv_negation_false_true bv_negation_true_false step_exp_neq_sameE step_exp_valE.word)

text \<open>BOP - Generic\<close>

lemma step_exp_lop_unk_lhsE:
  assumes \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e\<^sub>2 \<leadsto> e\<close>
        and EunknownL: \<open>e = unknown[str]: imm\<langle>Suc 0\<rangle> \<Longrightarrow> P\<close>
        and EunknownR: \<open>\<And>str' t'. \<lbrakk>e\<^sub>2 = (unknown[str']: t'); e = unknown[str']: imm\<langle>Suc 0\<rangle>\<rbrakk> \<Longrightarrow> P\<close>
        and EunknownStep: \<open>\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e = BinOp (unknown[str]: t) (LOp lop) e\<^sub>2'\<rbrakk> \<Longrightarrow> P\<close>
      shows P
  using assms(1) apply (elim LopUnkRhsE step_exp_valE EunknownL EunknownR EunknownStep step_exp_valE.unknown)
  by simp_all

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
  obtains (minor) e\<^sub>2' where \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close> \<open>e = BinOp (Val v) bop e\<^sub>2'\<close>
  using major caveat apply (elim step_exp_bop_rhsE)
  using minor by auto

interpretation step_exp_bop_rhs_strictE: exp_val_syntax \<open>\<lambda>e v. 
    (\<And>\<Delta> bop e\<^sub>2 e' P. \<lbrakk>\<Delta> \<turnstile> BinOp e bop e\<^sub>2 \<leadsto> e'; \<forall>v. e\<^sub>2 \<noteq> Val v; \<forall>str t. v \<noteq> unknown[str]: t; 
        (\<And>e\<^sub>2'. \<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'; e' = BinOp e bop e\<^sub>2'\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P)\<close>
  by (standard, use step_exp_bop_rhs_strictE in blast)

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
    obtains e\<^sub>1' where \<open>e = bop_fun e\<^sub>1' e\<^sub>2\<close> \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
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

lemmas step_exp_aop_unk_rhsE[elim] = AopUnkLhsE
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
context uop_is_word
begin

lemma exp_not_unkI: 
  fixes v\<^sub>1 :: val and w\<^sub>1 :: word
  assumes e: \<open>\<exists>num. e\<^sub>1 = num \<Colon> sz \<and> v\<^sub>1 = num \<Colon> sz \<and> w\<^sub>1 = num \<Colon> sz\<close>
  shows \<open>bv_fun1 e\<^sub>1 \<noteq> unknown[str]: t\<close>
  using e apply clarify
  using bv_fun_is_word by (metis unknown_simps(1))

lemma val_not_unkI: 
  fixes e\<^sub>1 :: exp and w\<^sub>1 :: word
  assumes e: \<open>\<exists>num. e\<^sub>1 = num \<Colon> sz \<and> v\<^sub>1 = num \<Colon> sz \<and> w\<^sub>1 = num \<Colon> sz\<close>
  shows \<open>bv_fun2 v\<^sub>1 \<noteq> unknown[str]: t\<close>
  using e apply clarify
  using bv_fun_is_word by (metis unknown_simps(1))

end


context bop_is_word
begin 

lemma exp_not_unkI: 
  fixes v\<^sub>1 v\<^sub>2 :: val and w\<^sub>1 w\<^sub>2 :: word
  assumes e1: \<open>\<exists>num. e\<^sub>1 = num \<Colon> sz\<^sub>1 \<and> v\<^sub>1 = num \<Colon> sz\<^sub>1 \<and> w\<^sub>1 = num \<Colon> sz\<^sub>1\<close>
      and e2: \<open>\<exists>num. e\<^sub>2 = num \<Colon> sz\<^sub>2 \<and> v\<^sub>2 = num \<Colon> sz\<^sub>2 \<and> w\<^sub>2 = num \<Colon> sz\<^sub>2\<close>
  shows \<open>bv_fun1 e\<^sub>1 e\<^sub>2 \<noteq> unknown[str]: t\<close>
  using e1 e2 apply clarify
  using bv_fun_is_word by (metis unknown_simps(1))

lemma val_not_unkI: 
  fixes e\<^sub>1 e\<^sub>2 :: exp and w\<^sub>1 w\<^sub>2 :: word
  assumes e1: \<open>\<exists>num. e\<^sub>1 = num \<Colon> sz\<^sub>1 \<and> v\<^sub>1 = num \<Colon> sz\<^sub>1 \<and> w\<^sub>1 = num \<Colon> sz\<^sub>1\<close>
      and e2: \<open>\<exists>num. e\<^sub>2 = num \<Colon> sz\<^sub>2 \<and> v\<^sub>2 = num \<Colon> sz\<^sub>2 \<and> w\<^sub>2 = num \<Colon> sz\<^sub>2\<close>
  shows \<open>bv_fun2 v\<^sub>1 v\<^sub>2 \<noteq> unknown[str]: t\<close>
  using e1 e2 apply clarify
  using bv_fun_is_word by (metis unknown_simps(1))

end


lemma capture_avoiding_sub_not_unknownI[intro]:
  assumes \<open>val \<noteq> unknown[str]: t'\<close>
    shows \<open>[val\<sslash>(nm :\<^sub>t t)](nm :\<^sub>t t) \<noteq> unknown[str]: t'\<close>
  using assms by auto

method rewrite uses add = (simp only: add, ((thin_tac \<open>(_::exp) = _\<close>)+)?)
method solve_not_unknown uses add = (solves \<open>simp (no_asm) add: add\<close> | 
  (intro allI capture_avoiding_sub_not_unknownI plus.val_not_unkI minus.val_not_unkI 
         times.val_not_unkI divide.val_not_unkI sdivide.val_not_unkI xor.val_not_unkI 
         lsl.val_not_unkI lsr.val_not_unkI asr.val_not_unkI not.val_not_unkI neg.val_not_unkI 
         eq.val_not_unkI land.val_not_unkI lor.val_not_unkI
         xtract.val_not_unkI succ.val_not_unkI; solve_is_wordI)
)
method simp_capture_avoidE uses add = (simp (asm_lr) only: capture_avoiding_sub_simps)

method solve_expE_scaffold methods recurs solve_is_val solve_type uses add
  \<open>Scaffold method for deconstructing expression relations as premises (elimination rules).
   This should not be called directly.\<close> = (

\<comment> \<open>Var\<close>
  (erule step_exp_var_inE.is_val[rotated], solve_var_inI add: add, defer_tac, solve_is_val,
     prefer_last, rewrite) |

\<comment> \<open>Let\<close>
  (erule step_exp_letE.is_val[rotated], defer_tac, solve_is_valI, prefer_last, simp_capture_avoidE,
     rewrite) |


\<comment> \<open>UnOps\<close>
  (erule step_exp_notE.is_sz_word[rotated] step_exp_negE.is_sz_word[rotated], defer_tac, 
      solve_is_wordI, rewrite) |
  (erule not.step_exp_strictE neg.step_exp_strictE, 
      solves fastforce, recurs) |

\<comment> \<open>BinOps\<close>
  (erule step_exp_divE step_exp_sdivE step_exp_modE step_exp_smodE 
         step_exp_eq_sameE step_exp_neq_sameE step_exp_lessE step_exp_less_eqE step_exp_signed_lessE 
         step_exp_signed_less_eqE, rewrite) |
  (erule step_exp_plusE.is_word2[rotated 2] step_exp_minusE.is_word2[rotated 2] 
         step_exp_timesE.is_word2[rotated 2] step_exp_lsrE.is_word2[rotated 2] 
         step_exp_lslE.is_word2[rotated 2] step_exp_asrE.is_word2[rotated 2]
         step_exp_lessE.is_word2[rotated 2] step_exp_less_eqE.is_word2[rotated 2]
         step_exp_eqE.is_word2[rotated 2] step_exp_xorE.is_word2[rotated 2]
         step_exp_landE.is_word2[rotated 2] step_exp_lorE.is_word2[rotated 2], 
      defer_tac, solve_is_wordI, solve_is_wordI, prefer_last, rewrite) |
  (erule plus.step_exp_lhs_strictE minus.step_exp_lhs_strictE times.step_exp_lhs_strictE 
         divide.step_exp_lhs_strictE sdivide.step_exp_lhs_strictE mod.step_exp_lhs_strictE
         smod.step_exp_lhs_strictE lsl.step_exp_lhs_strictE lsr.step_exp_lhs_strictE 
         asr.step_exp_lhs_strictE xor.step_exp_lhs_strictE land.step_exp_lhs_strictE
         lor.step_exp_lhs_strictE lt.step_exp_lhs_strictE le.step_exp_lhs_strictE 
         step_exp_bop_lhs_strictE, 
      solves \<open>simp (no_asm) add: add\<close>, solve_not_unknown add: add, recurs) |

  (erule plus.step_exp_rhs_strictE.is_val[rotated] minus.step_exp_rhs_strictE.is_val[rotated] 
         times.step_exp_rhs_strictE.is_val[rotated] divide.step_exp_rhs_strictE.is_val[rotated]
         sdivide.step_exp_rhs_strictE.is_val[rotated] mod.step_exp_rhs_strictE.is_val[rotated]
         smod.step_exp_rhs_strictE.is_val[rotated] lsl.step_exp_rhs_strictE.is_val[rotated]
         lsr.step_exp_rhs_strictE.is_val[rotated] asr.step_exp_rhs_strictE.is_val[rotated]
         xor.step_exp_rhs_strictE.is_val[rotated] land.step_exp_rhs_strictE.is_val[rotated] 
         lor.step_exp_rhs_strictE.is_val[rotated] lt.step_exp_rhs_strictE.is_val[rotated]
         le.step_exp_rhs_strictE.is_val[rotated] step_exp_bop_rhs_strictE.is_val[rotated],
      solves \<open>simp (no_asm)\<close>, prefer_last, solve_is_val, solve_not_unknown add: add, recurs) |
                          
\<comment> \<open>Cast\<close>
  (erule step_exp_cast_highE.is_word[rotated]   step_exp_cast_lowE.is_word[rotated] 
         step_exp_cast_signedE.is_word[rotated] step_exp_cast_unsignedE.is_word[rotated],
     prefer_last, solve_is_wordI, rewrite) |
 
  \<comment> \<open>Single reduction\<close>
  (erule step_exp_cast_reduceE step_exp_step_let_strictE, solves \<open>simp (no_asm)\<close>, recurs) |

\<comment> \<open>Store\<close>
  (erule step_exp_store_el_manyE.word.val.word[rotated], 
     prefer_last, solve_type, linarith, (unfold load_byte_minus_simps)?, rewrite) |
  (erule step_exp_store_el_manyE.is_val3[rotated 4],
     prefer_last, solve_is_val,
     prefer_last, solve_is_wordI,
     prefer_last, solve_is_val,
     prefer_last, solve_type, 
     linarith, (unfold load_byte_minus_simps)?, rewrite) |
  (erule step_exp_store_singleE.is_val3[rotated 4],
     prefer_last, solve_is_val,
     prefer_last, solve_is_wordI,
     prefer_last, solve_is_val,
     prefer_last, solve_type, 
     rewrite) |
  (erule step_exp_store_step_addr_strictE.word step_exp_store_step_addr_strictE,
     solves fastforce, recurs) |
  (erule step_exp_store_step_val_strictE, fastforce, recurs) |
  (erule step_exp_store_step_mem_strictE.is_val2[rotated 2], fastforce,
     prefer_last, solve_is_val,
     prefer_last, solve_is_val,
     recurs) |

\<comment> \<open>Load\<close>
  (erule step_exp_load_byte_from_nextE.word.storage, solve_word_neq add: add, rewrite) |
  (erule step_exp_load_byte_from_nextE.is_word_val[rotated 2],
     prefer_last, solve_is_val,
     prefer_last, solve_is_wordI,
     solve_word_neq add: add, rewrite) |
  (erule step_exp_load_word_el_memE, linarith, (unfold load_byte_minus_simps)?, rewrite) |
  (erule step_exp_load_word_el_memE.is_word[rotated], linarith, (unfold load_byte_minus_simps)?,
     prefer_last, solve_is_wordI, rewrite) |
  (erule step_exp_load_byte_eqE.is_word_val[rotated 2],
     prefer_last, solve_is_val, 
     prefer_last, solve_is_wordI, 
     rewrite) |
  (erule step_exp_load_step_mem_strictE.is_val[rotated],
           prefer_last, solve_is_val, fastforce, recurs) |
  (erule step_exp_load_step_addr_strictE, fastforce, recurs) |

\<comment> \<open>Concatenate\<close>
  (erule step_exp_concatE.is_word2[rotated 2],
           prefer_last, solve_is_wordI,
           prefer_last, solve_is_wordI, rewrite) |
  (erule step_exp_concat_lhs_stepE.is_val[rotated], solves clarify,
     prefer_last, solve_is_val,
     recurs) |
  (erule step_exp_concat_rhs_stepE, solves clarify, recurs)
)

method solve_expE uses add
  \<open>Method for deconstructing expression relations as premises (elimination rules)\<close> = (
  solve_expE_scaffold \<open>solve_expE add: add\<close> \<open>solve_is_valI add: add\<close> \<open>solve_typeI add: add\<close> add: add
)

end
