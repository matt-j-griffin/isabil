theory Mem32
  imports Mem16 
          \<comment> \<open>Why am I doing this? - it looks like you must preload "interpretation"s to add lemmas
              to the context. If interpretations and lemma adding happens in parallel then the lemmas 
              don't seem to make it to the interpretation\<close>
          "IsaBIL.Expressions_Intros"
          "IsaBIL.Solve_BitVector"
begin

\<comment> \<open>Memory Extensions for 32bit words\<close>

\<comment> \<open>Loading and storing 32bit words will require 4 separate memory operations (assuming the smallest 
   addressable memory size is 8 bits).
   These memory operations will target the current address and its 4 subsequent positions,
   which the solver can't currently handle.
   
   We therefore must add these rules to the solver.

   We start by introducing simplification rules for succ2 and succ3, which applies the successor
   function succ two and three times respectively, and add these to our syntax locales.
   \<close>

context word_constructor 
begin

abbreviation \<open>succ2 w \<equiv> succ (succ w)\<close>
abbreviation \<open>succ3 w \<equiv> succ (succ2 w)\<close>

lemma word_neq_succI:
  assumes \<open>x \<noteq> Suc y\<close> \<open>sz > 0\<close> \<open>Suc y < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto

lemma word_neq_succ2I:
  assumes \<open>x \<noteq> Suc (Suc y)\<close> \<open>sz > 0\<close> \<open>Suc (Suc y) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ2 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto

lemma word_neq_succ3I:
  assumes \<open>x \<noteq> Suc (Suc (Suc y))\<close> \<open>sz > 0\<close> \<open>Suc (Suc (Suc y)) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ3 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto

definition
  no_address_overlap_32_32 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_32_32 w\<^sub>1 w\<^sub>2 \<equiv> (
    w\<^sub>1 \<noteq> w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ2 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ3 w\<^sub>2 \<and>
    succ w\<^sub>1 \<noteq> w\<^sub>2 \<and> 
    succ2 w\<^sub>1 \<noteq> w\<^sub>2 \<and>
    succ3 w\<^sub>1 \<noteq> w\<^sub>2
)\<close>

lemma no_address_overlap_32_32: 
  assumes \<open>no_address_overlap_32_32 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ2 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ3 w\<^sub>2\<close> 
          \<open>succ w\<^sub>1 \<noteq> w\<^sub>2\<close>
          \<open>succ2 w\<^sub>1 \<noteq> w\<^sub>2\<close>
          \<open>succ3 w\<^sub>1 \<noteq> w\<^sub>2\<close>
  using assms unfolding no_address_overlap_32_32_def  by auto


lemmas succ_plus_lhs_succ = succ_plus_lhs_is_word[where w\<^sub>1 = \<open>_ \<Colon> 64\<close> and w\<^sub>2 = \<open>succ (_ \<Colon> 64)\<close>,
    simplified, OF refl succ_is_word, simplified]
lemmas succ_plus_lhs_succ2 = succ_plus_lhs_is_word[where w\<^sub>1 = \<open>_ \<Colon> 64\<close> and w\<^sub>2 = \<open>succ2 (_ \<Colon> 64)\<close>,
    simplified, OF refl succ_is_word[OF succ_is_word], simplified]


lemma no_address_overlap_32_32_plusI:
  assumes y_is_ok: \<open>Suc (Suc (Suc y)) < 2 ^ 64\<close> and z_is_ok: \<open>Suc (Suc (Suc z)) < 2 ^ 64\<close> 
      and neq: \<open>Suc (Suc (Suc z)) < y \<or> Suc (Suc (Suc y)) < z\<close>
    shows \<open>no_address_overlap_32_32 ((x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64)) ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))\<close>
  unfolding succ_plus_lhs succ_plus_lhs_succ2 succ_plus_lhs_succ no_address_overlap_32_32_def
  apply (intro conjI bv_plus_neq_lhsI bv_plus_neq_lhs_is_wordI is_word succ_is_word word_is_okI 
               y_is_ok z_is_ok succ_is_okI[where sz = 64] word_neq_succI word_neq_succI[symmetric]
               word_neq_succ2I word_neq_succ2I[symmetric] word_neq_succ3I word_neq_succ3I[symmetric]
               Suc_lessD[where m = y] Suc_lessD[where m = z] 
               Suc_lessD[where m = \<open>Suc _\<close>])
  using neq by auto
end

\<comment> \<open>Now we add an abbreviation for 32bit words in storage.\<close>

context storage_constructor
begin

definition
  storage_el32 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el32 mem w v \<equiv> (storage_el16 mem w v)
    [succ2 w \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ3 w \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
\<close>

definition
  storage_be32 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be32 mem w v \<equiv> (storage_be16 (mem
     [     w \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
     [succ w \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8])
   (succ2 w) v)
\<close>

end

lemma type_storage_addr_el32[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_el32 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_el32_def by (solve_type16I add: assms)

lemma type_storage_el32[simp]: \<open>type (storage_el32 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_el32_def by solve_type16I

lemma type_storage_addr_be32[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_be32 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be32_def by (solve_type16I add: assms)

lemma type_storage_be32[simp]: \<open>type (storage_be32 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be32_def by solve_type16I

method solve_type32I_scaffold methods recurs = (
  (rule type_storage_el32 type_storage_be32) |
  (rule type_storage_addr_el32 type_storage_addr_be32, recurs) |
  solve_type16I_scaffold recurs
)                 

method solve_type32I uses add = (
  (solves \<open>rule add\<close>) | 
  solve_type32I_scaffold \<open>solve_type32I add: add\<close>
)

lemma storage_el32_is_val: \<open>storage_el32 mem w v = Val (storage_el32 mem w v)\<close>
  unfolding storage_el32_def by solve_is_val16I
thm storage_el32_is_val[symmetric, simp]

lemma storage_be32_is_val: \<open>storage_be32 mem w v = Val (storage_be32 mem w v)\<close>
  unfolding storage_be32_def by solve_is_val16I
thm storage_be32_is_val[symmetric, simp]

method solve_is_val32I uses add = (
  (rule storage_el32_is_val storage_be32_is_val) | 
  solve_is_val16I add: add
)

lemmas xtract32_24_16[simp] = xtract_concat_consecutive[of 24 31 16, simplified]
lemmas xtract32_16_8 [simp] = xtract_concat_consecutive[of 16 31 8, simplified]
lemmas xtract32_8_0  [simp] = xtract_concat_consecutive[of 8 31 0, simplified]
lemmas xtract23_16_0 [simp] = xtract_concat_consecutive[of 16 23 0, simplified]
lemmas xtract32_24_0 [simp] = xtract_concat_consecutive[of 24 31 0, simplified]
lemmas xtract32 = xtract32_24_16 xtract32_24_0 xtract32_16_8 xtract32_8_0 xtract23_16_0
                  xtract16_8_0

lemmas xtract_nested_31_0_23_0 [simp] = nested_extract_within'[of  0 23  0 31, simplified]
lemmas xtract_nested_31_0_31_24[simp] = nested_extract_within'[of 24 31  0 31, simplified]
lemmas xtract_nested_31_8_7_0  [simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 8 and sz\<^sub>h\<^sub>i' = 7 and sz\<^sub>l\<^sub>o' = 0, simplified]
lemmas xtract_nested_31_8_23_8 [simp] = nested_extract_within [where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 8 and sz\<^sub>l\<^sub>o' = 8, simplified]
lemmas xtract_nested_31_16_15_8[simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 16 and sz\<^sub>h\<^sub>i' = 15 and sz\<^sub>l\<^sub>o' = 8, simplified]
lemmas xtract_nested_31_16_7_0[simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 16 and sz\<^sub>h\<^sub>i' = 7 and sz\<^sub>l\<^sub>o' = 0, simplified]
lemmas xtract_nested_23_0_15_0 [simp] = nested_extract_within'[of  0 15  0 23, simplified]
lemmas xtract_nested_23_0_23_16[simp] = nested_extract_within'[of 16 23  0 23, simplified]
lemmas xtract_nested_15_0_7_0  [simp] = nested_extract_within'[of  0  7  0 15, simplified]
lemmas xtract_nested_15_0_15_8 [simp] = nested_extract_within'[of  8 15  0 15, simplified]
lemmas xtract_nested32 = 
  xtract_nested_31_0_23_0  xtract_nested_31_0_31_24 xtract_nested_31_8_7_0  xtract_nested_31_8_23_8 
  xtract_nested_31_16_15_8 xtract_nested_31_16_7_0  xtract_nested_23_0_15_0 xtract_nested_23_0_23_16
  xtract_nested_15_0_7_0   xtract_nested_15_0_15_8

lemma xtract_31_0_63_0:
  assumes \<open>num < 2 ^ 32\<close>
    shows \<open>(ext (ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0) \<sim> hi : 63 \<sim> lo : 0) = (num \<Colon> 64)\<close>
  unfolding xtract.simps apply simp
  using assms take_bit_nat_eq_self by blast

end
