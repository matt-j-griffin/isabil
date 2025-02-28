theory Mem16
  imports IsaBIL.Expression_Syntax_Locales
begin

\<comment> \<open>Memory Extensions for 16bit words\<close>



context storage_constructor
begin

definition 
  storage_el16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8])
\<close>

definition
  storage_be16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8])
\<close>

end

lemma type_storage_addr_el16[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_el16 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_el16_def by (solve_typeI add: assms)

lemma type_storage_el16[simp]: \<open>type (storage_el16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps storage_el16_def by (rule type_storageI)

lemma type_storage_addr_be16[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_be16 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be16_def by (solve_typeI add: assms)

lemma type_storage_be16[simp]: \<open>type (storage_be16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be16_def by (solve_typeI)

method solve_type16I_scaffold methods recurs = (
  (rule type_storage_el16 type_storage_be16) |
  (rule type_storage_addr_el16 type_storage_addr_be16, recurs) |
  solve_typeI_scaffold recurs
)

method solve_type16I uses add = (solves \<open>rule add\<close> | solve_type16I_scaffold \<open>solve_type16I add: add\<close>)

lemma storage_el16_is_val: \<open>storage_el16 mem w v = Val (storage_el16 mem w v)\<close>
  by (simp add: storage_el16_def storage_constructor_exp_def)
thm storage_el16_is_val[symmetric, simp]

lemma storage_be16_is_val: \<open>storage_be16 mem w v = Val (storage_be16 mem w v)\<close>
  by (simp add: storage_be16_def storage_constructor_exp_def)
thm storage_be16_is_val[symmetric, simp]

method solve_is_val16I uses add = (
  (rule storage_el16_is_val storage_be16_is_val) | 
  solve_is_valI add: add
)

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
