theory Mem16
  imports "../ExpressionSemantics/Expression_Syntax_Locales"
begin

\<comment> \<open>Memory Extensions for 16bit words\<close>



context storage_constructor
begin

abbreviation 
  storage_el16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8])
\<close>
lemmas storage_el16_def = refl
abbreviation 
  storage_be16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8])
\<close>
lemmas storage_be16_def = refl
end

lemma type_storage_el16[simp]: \<open>type (storage_el16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps storage_el16_def by (rule type_storageI)

lemma type_storage_be16[simp]: \<open>type (storage_be16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps storage_be16_def by (rule type_storageI)

(* TODO move *)
lemma nested_extract_within: 
  assumes \<open>sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o \<le> sz\<^sub>h\<^sub>i\<close>
    shows \<open>(ext (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) \<sim> hi : (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o) \<sim> lo : sz\<^sub>l\<^sub>o') = (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : (sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o))\<close>
  using assms using nested_extract_within'[where sz\<^sub>h\<^sub>i'= \<open>sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<close> and sz\<^sub>l\<^sub>o = sz\<^sub>l\<^sub>o and sz\<^sub>l\<^sub>o' = sz\<^sub>l\<^sub>o' and sz\<^sub>h\<^sub>i = sz\<^sub>h\<^sub>i and num = num and sz = sz]
  apply auto
  using add_le_imp_le_diff by blast

\<comment> \<open>Little Endian\<close>

lemmas xtract16_8_0[simp] = xtract_concat_consecutive[of 8 15 0, simplified]


end
