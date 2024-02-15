theory Val_Instance
  imports BIL_Syntax Bitvector_Instance
begin

instantiation val :: val
begin

definition
  word_constructor_val :: \<open>nat \<Rightarrow> nat \<Rightarrow> val\<close>
where
  \<open>(num \<Colon> sz) = (Immediate (num \<Colon> sz))\<close>

definition
  unknown_constructor_val :: \<open>string \<Rightarrow> Type \<Rightarrow> val\<close>
where
  \<open>(unknown[str]: sz) = Unknown str sz\<close>

definition
  storage_constructor_val :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> val\<close>
where
  \<open>(v[a \<leftarrow> v', sz]) = Storage v a v' sz\<close>

definition 
  true_val :: val
where
  \<open>true_val = (Immediate true)\<close>

definition 
  false_val :: val
where
  \<open>false_val = (Immediate false)\<close>

lemma true_not_false_val[simp]: \<open>(true::val) \<noteq> false\<close>
  unfolding false_val_def true_val_def
  using not_true_eq_false by (metis val.inject(1))

lemma valI:
  fixes v :: val
  assumes imm: \<open>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q\<close>
      and unk: \<open>\<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q\<close>
      and mem: \<open>\<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q\<close>
    shows Q
  apply (cases v rule: val.exhaust)
  subgoal for w 
    apply (cases w rule: word_exhaust)
    subgoal for num sz apply (rule imm[of num sz])
      by (simp add: word_constructor_val_def)
    .
  subgoal by (rule unk, unfold unknown_constructor_val_def)
  subgoal by (rule mem, unfold storage_constructor_val_def)
  .

function
  type_val :: \<open>val \<Rightarrow> Type\<close>
where
  \<open>type_val (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close> |
  \<open>type_val (unknown[str]: t) = t\<close> |
  \<open>type_val (mem[(num \<Colon> sz\<^sub>1) \<leftarrow> v, sz\<^sub>2]) = mem\<langle>sz\<^sub>1, sz\<^sub>2\<rangle>\<close>
  subgoal for P x 
    apply (rule valI[of x])
    prefer 3 subgoal for mem w v' sz 
      apply (cases w rule: word_exhaust) 
      by simp
    by simp_all
  unfolding storage_constructor_val_def word_constructor_val_def unknown_constructor_val_def
  by simp_all
termination by (standard, auto)

instance 
  apply standard
  apply simp_all
  unfolding storage_constructor_val_def word_constructor_val_def unknown_constructor_val_def
  apply (simp_all add: true_val_def false_val_def)
  apply (metis val.exhaust word_exhaust)
  by (metis val.exhaust word_exhaust)

end

lemmas Immediate_simp[simp] = word_constructor_val_def[symmetric]

lemma storage_not_nested_val[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz] \<noteq> v\<close>
  unfolding storage_constructor_val_def by simp

end