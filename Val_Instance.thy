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

instance 
  apply standard 
  unfolding storage_constructor_val_def word_constructor_val_def unknown_constructor_val_def
  apply (simp_all add: true_val_def false_val_def)
  apply (simp add: true_word_def)
  apply (simp add: false_word_def)
  apply (metis val.exhaust word_exhaust)
  by (metis val.exhaust word_exhaust)

end

lemmas Immediate_simp[simp] = word_constructor_val_def[symmetric]

lemma storage_not_nested_val[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz] \<noteq> v\<close>
  unfolding storage_constructor_val_def by simp

end