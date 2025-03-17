theory Mem64
  imports Mem32
begin

\<comment> \<open>Memory Extensions for 64bit words\<close>

\<comment> \<open>Loading and storing 64bit words will require 8 separate memory operations (assuming the smallest 
   addressable memory size is 8 bits).
   These memory operations will target the current address and its 8 subsequent positions,
   which the solver can't currently handle.
   
   We therefore must add these rules to the solver.

   We start by introducing simplification rules for succ4-7, which applies the successor
   function succ four to seven times respectively, and add these to our syntax locales.
   \<close>

context word_constructor
begin 

abbreviation \<open>succ4 w \<equiv> succ (succ3 w)\<close>
abbreviation \<open>succ5 w \<equiv> succ (succ4 w)\<close>
abbreviation \<open>succ6 w \<equiv> succ (succ5 w)\<close>
abbreviation \<open>succ7 w \<equiv> succ (succ6 w)\<close>

lemma word_neq_succ4I:
  assumes \<open>x \<noteq> Suc (Suc (Suc (Suc y)))\<close> \<open>sz > 0\<close> \<open>Suc (Suc (Suc (Suc y))) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ4 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto


lemma word_neq_succ5I:
  assumes \<open>x \<noteq> Suc (Suc (Suc (Suc (Suc y))))\<close> \<open>sz > 0\<close> \<open>Suc (Suc (Suc (Suc (Suc y)))) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ5 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto


lemma word_neq_succ6I:
  assumes \<open>x \<noteq> Suc (Suc (Suc (Suc (Suc (Suc y)))))\<close> \<open>sz > 0\<close> \<open>Suc (Suc (Suc (Suc (Suc (Suc y))))) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ6 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto


lemma word_neq_succ7I:
  assumes \<open>x \<noteq> Suc (Suc (Suc (Suc (Suc (Suc (Suc y))))))\<close> \<open>sz > 0\<close> 
          \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < 2 ^ sz\<close>
    shows \<open>x \<Colon> sz \<noteq> succ7 (y \<Colon> sz)\<close>
  using assms unfolding succ.simps bv_plus.simps by auto

definition 
  no_address_overlap_64_32 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_32 w\<^sub>1 w\<^sub>2 \<equiv> (
    no_address_overlap_32_32 w\<^sub>1 w\<^sub>2 \<and> succ4 w\<^sub>1 \<noteq> w\<^sub>2 \<and> succ5 w\<^sub>1 \<noteq> w\<^sub>2 \<and> succ6 w\<^sub>1 \<noteq> w\<^sub>2 \<and>
    succ7 w\<^sub>1 \<noteq> w\<^sub>2
)\<close>

lemma no_address_overlap_64_32: 
  assumes \<open>no_address_overlap_64_32 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ2 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ3 w\<^sub>2\<close> \<open>succ w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ2 w\<^sub>1 \<noteq> w\<^sub>2\<close> 
          \<open>succ3 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ4 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ5 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ6 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ7 w\<^sub>1 \<noteq> w\<^sub>2\<close>
  apply (intro no_address_overlap_32_32[OF conjunct1[OF assms[unfolded no_address_overlap_64_32_def]]])+
  using assms unfolding no_address_overlap_64_32_def by auto

lemma no_address_overlap_64_32': (* TODO *)
  assumes \<open>no_address_overlap_64_32 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>2 \<noteq> w\<^sub>1\<close> \<open>succ w\<^sub>2 \<noteq> w\<^sub>1\<close> \<open>succ2 w\<^sub>2 \<noteq> w\<^sub>1\<close> \<open>succ3 w\<^sub>2 \<noteq> w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ2 w\<^sub>1\<close>
          \<open>w\<^sub>2 \<noteq> succ3 w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ4 w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ5 w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ6 w\<^sub>1\<close> \<open>w\<^sub>2 \<noteq> succ7 w\<^sub>1\<close>
  using no_address_overlap_64_32[OF assms] by auto

definition 
  no_address_overlap_64_64 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_64 w\<^sub>1 w\<^sub>2 \<equiv> (
    no_address_overlap_64_32 w\<^sub>1 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ4 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ5 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ6 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ7 w\<^sub>2
)\<close>

lemma no_address_overlap_64_64_swapI:
  assumes \<open>no_address_overlap_64_64 w1 w2\<close>
    shows \<open>no_address_overlap_64_64 w2 w1\<close>
  using assms unfolding no_address_overlap_64_64_def no_address_overlap_64_32_def apply auto
  by (rule no_address_overlap_32_32_swapI)


lemma no_address_overlap_64_64: 
  assumes \<open>no_address_overlap_64_64 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ2 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ3 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ4 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ5 w\<^sub>2\<close>
          \<open>w\<^sub>1 \<noteq> succ6 w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ7 w\<^sub>2\<close> \<open>succ w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ2 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ3 w\<^sub>1 \<noteq> w\<^sub>2\<close>
          \<open>succ4 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ5 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ6 w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>succ7 w\<^sub>1 \<noteq> w\<^sub>2\<close>
  apply (intro no_address_overlap_64_32[OF conjunct1[OF assms[unfolded no_address_overlap_64_64_def]]])+
  defer defer defer defer
  apply (intro no_address_overlap_64_32[OF conjunct1[OF assms[unfolded no_address_overlap_64_64_def]]])+
  using assms unfolding no_address_overlap_64_64_def by auto

lemma no_address_overlap_64_32_plusI:
  assumes y_is_ok: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < 2 ^ 64\<close> 
      and z_is_ok: \<open>Suc (Suc (Suc z)) < 2 ^ 64\<close> 
      and neq: \<open>Suc (Suc (Suc z)) < y \<or> Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < z\<close>
    shows \<open>no_address_overlap_64_32 ((x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64)) ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))\<close>
unfolding no_address_overlap_64_32_def proof (rule conjI)
  show "no_address_overlap_32_32 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))"
  proof (intro no_address_overlap_32_32_plusI conjI y_is_ok z_is_ok Suc_lessD [where m = \<open>Suc _\<close>])
    show "Suc (Suc (Suc z)) < y \<or> Suc (Suc (Suc y)) < z"
      using neq by linarith
  qed
next
  show "succ4 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) \<noteq> (x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64) \<and> succ5 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) \<noteq> (x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64) \<and> succ6 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) \<noteq> (x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64) \<and> succ7 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) \<noteq> (x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64)"
  unfolding succ_plus_lhs succ_plus_lhs_succ2 succ_plus_lhs_succ
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ3 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ4 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ5 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ6 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ7 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]]]], 
                                  simplified]
  apply (intro bv_plus_neq_lhs_is_wordI is_word succ_is_word word_is_okI succ_is_okI[where sz = 64]
              word_neq_succ4I[symmetric] word_neq_succ5I[symmetric] word_neq_succ6I[symmetric] 
              word_neq_succ7I[symmetric] y_is_ok z_is_ok Suc_lessD[where m = y] Suc_lessD[where m = z] 
              Suc_lessD[where m = \<open>Suc _\<close>] conjI)
  using neq by auto
qed

lemma no_address_overlap_64_64_plusI:
  assumes y_is_ok: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < 2 ^ 64\<close> 
      and z_is_ok: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc z)))))) < 2 ^ 64\<close> 
      and neq: \<open>Suc (Suc (Suc (Suc (Suc (Suc (Suc z)))))) < y \<or> 
                Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < z\<close>
    shows \<open>no_address_overlap_64_64 ((x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64)) ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))\<close>
unfolding no_address_overlap_64_64_def proof (rule conjI)
  show "no_address_overlap_64_32 ((x \<Colon> 64::'a) +\<^sub>b\<^sub>v (y \<Colon> 64)) ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))"
  proof (intro no_address_overlap_64_32_plusI conjI y_is_ok z_is_ok Suc_lessD [where m = \<open>Suc _\<close>])
    show "Suc (Suc (Suc z)) < y \<or> Suc (Suc (Suc (Suc (Suc (Suc (Suc y)))))) < z"
      using neq by linarith
  qed
next
  show "(x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64) \<noteq> succ4 ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64)) \<and> 
        (x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64) \<noteq> succ5 ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64)) \<and> 
        (x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64) \<noteq> succ6 ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64)) \<and> 
        (x \<Colon> 64) +\<^sub>b\<^sub>v (y \<Colon> 64) \<noteq> succ7 ((x \<Colon> 64) +\<^sub>b\<^sub>v (z \<Colon> 64))"
  unfolding succ_plus_lhs succ_plus_lhs_succ2 succ_plus_lhs_succ
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ3 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ4 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ5 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ6 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]]], 
                                  simplified]
  unfolding succ_plus_lhs_is_word[where w\<^sub>1 = \<open>x \<Colon> 64\<close> and w\<^sub>2 = \<open>succ7 (_ \<Colon> 64)\<close>, simplified, 
                                  OF refl succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word[OF succ_is_word]]]]]], 
                                  simplified]
  apply (intro bv_plus_neq_lhs_is_wordI is_word succ_is_word word_is_okI succ_is_okI[where sz = 64]
              word_neq_succ4I word_neq_succ5I word_neq_succ6I
              word_neq_succ7I y_is_ok z_is_ok Suc_lessD[where m = y] Suc_lessD[where m = z] 
              Suc_lessD[where m = \<open>Suc _\<close>] conjI)
  using neq by auto
qed

end

\<comment> \<open>Now we add an abbreviation for 64bit words in storage.\<close>

context storage_constructor
begin

definition 
  storage_el64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el64 mem w v \<equiv> (storage_el32 mem w v)
    [succ4 w \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ5 w \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ6 w \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ7 w \<leftarrow> ext v \<sim> hi : 63 \<sim> lo : 56, 8]
\<close>

definition
  storage_be64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be64 mem w v \<equiv> (storage_be32 (mem
     [      w \<leftarrow> ext v \<sim> hi : 63 \<sim> lo : 56, 8]
     [succ  w \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
     [succ2 w \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
     [succ3 w \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8])
    (succ4 w) v)
\<close>

end

lemma type_storage_addr_el64[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_el64 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_el64_def by (solve_type32I add: assms)

lemma type_storage_el64[simp]: \<open>type (storage_el64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_el64_def by solve_type32I

lemma type_storage_addr_be64[simp]: 
  assumes \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>type (storage_be64 mem w val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be64_def by (solve_type32I add: assms)

lemma type_storage_be64[simp]: \<open>type (storage_be64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding storage_be64_def by solve_type32I

method solve_type64I_scaffold methods recurs = (
  (rule type_storage_el64 type_storage_be64) |
  (rule type_storage_addr_el64 type_storage_addr_be64, recurs) |
  solve_type32I_scaffold recurs
)                 

method solve_type64I uses add = (
  (solves \<open>rule add\<close>) | 
  solve_type64I_scaffold \<open>solve_type64I add: add\<close>
)

lemma storage_el64_is_val: \<open>storage_el64 mem w v = Val (storage_el64 mem w v)\<close>
  unfolding storage_el64_def by solve_is_val32I
thm storage_el64_is_val[symmetric, simp]

lemma storage_be64_is_val: \<open>storage_be64 mem w v = Val (storage_be64 mem w v)\<close>
  unfolding storage_be64_def by solve_is_val32I
thm storage_be64_is_val[symmetric, simp]

method solve_is_val64I uses add = (
  (rule storage_el64_is_val storage_be64_is_val) | 
  solve_is_val32I add: add
)

lemmas xtract64_56_48[simp] = xtract_concat_consecutive[of 56 63 48, simplified]
lemmas xtract64_48_40[simp] = xtract_concat_consecutive[of 48 63 40, simplified]
lemmas xtract64_40_32[simp] = xtract_concat_consecutive[of 40 63 32, simplified]
lemmas xtract64_32_24[simp] = xtract_concat_consecutive[of 32 63 24, simplified]
lemmas xtract64_24_16[simp] = xtract_concat_consecutive[of 24 63 16, simplified]
lemmas xtract64_16_8 [simp] = xtract_concat_consecutive[of 16 63 8, simplified]
lemmas xtract64_8_0  [simp] = xtract_concat_consecutive[of 8 63 0, simplified]
lemmas xtract40_32_0 [simp] = xtract_concat_consecutive[of 32 39 0, simplified]
lemmas xtract48_40_0 [simp] = xtract_concat_consecutive[of 40 47 0, simplified]
lemmas xtract56_48_0 [simp] = xtract_concat_consecutive[of 48 55 0, simplified]
lemmas xtract64_56_0 [simp] = xtract_concat_consecutive[of 56 63 0, simplified]
lemmas xtract64 = xtract64_56_48 xtract64_48_40 xtract64_40_32 xtract64_32_24 xtract64_24_16
                  xtract64_16_8  xtract64_8_0

lemmas xtract_nested_63_8_55_8[simp]  = nested_extract_within [of  8  8 63, simplified]
lemmas xtract_nested_63_16_47_8[simp] = nested_extract_within [of  8 16 63, simplified]
lemmas xtract_nested_63_24_39_8[simp] = nested_extract_within [of  8 24 63, simplified]
lemmas xtract_nested_63_32_31_8[simp] = nested_extract_within [of  8 32 63, simplified]
lemmas xtract_nested_63_40_23_8[simp] = nested_extract_within [of  8 40 63, simplified]
lemmas xtract_nested_63_48_15_8[simp] = nested_extract_within [of  8 48 63, simplified]
lemmas xtract_nested_55_0_47_0[simp]  = nested_extract_within'[of  0 47  0 55, simplified]
lemmas xtract_nested_47_0_39_0[simp]  = nested_extract_within'[of  0 39  0 47, simplified]
lemmas xtract_nested_39_0_31_0[simp]  = nested_extract_within'[of  0 31  0 39, simplified]
lemmas xtract_nested_63_8_7_0[simp]   = nested_extract_within'[of  0  7  8 63,  simplified]
lemmas xtract_nested_63_16_7_0[simp]  = nested_extract_within'[of  0  7 16 63, simplified]
lemmas xtract_nested_63_24_7_0[simp]  = nested_extract_within'[of  0  7 24 63, simplified]
lemmas xtract_nested_63_32_7_0[simp]  = nested_extract_within'[of  0  7 32 63, simplified]
lemmas xtract_nested_63_40_7_0[simp]  = nested_extract_within'[of  0  7 40 63, simplified]
lemmas xtract_nested_63_48_7_0[simp]  = nested_extract_within'[of  0  7 48 63, simplified]
lemmas xtract_nested_55_0_55_48[simp] = nested_extract_within'[of 48 55  0 55, simplified]
lemmas xtract_nested_47_0_47_40[simp] = nested_extract_within'[of 40 47  0 47, simplified]
lemmas xtract_nested_39_0_39_32[simp] = nested_extract_within'[of 32 39  0 39, simplified]

lemma xtract_num_lt:
  assumes num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>(ext num \<Colon> sz \<sim> hi : 63 \<sim> lo : 0) = num \<Colon> 64\<close>
  using extract_concat64 num_lt by auto


lemmas solve_exps_mem64_simps = 
  xtract64_56_48 xtract64_48_40 xtract64_40_32 xtract64_32_24 xtract64_24_16 xtract64_16_8 
  xtract64_8_0   xtract40_32_0  xtract48_40_0  xtract56_48_0  xtract64_56_0

  xtract_nested_63_8_55_8  xtract_nested_63_16_47_8 xtract_nested_63_24_39_8 
  xtract_nested_63_32_31_8 xtract_nested_63_40_23_8 xtract_nested_63_48_15_8
  xtract_nested_55_0_47_0  xtract_nested_47_0_39_0  xtract_nested_39_0_31_0
  xtract_nested_63_8_7_0   xtract_nested_63_16_7_0  xtract_nested_63_24_7_0
  xtract_nested_63_32_7_0  xtract_nested_63_40_7_0  xtract_nested_63_48_7_0
  xtract_nested_55_0_55_48 xtract_nested_47_0_47_40 xtract_nested_39_0_39_32

end
