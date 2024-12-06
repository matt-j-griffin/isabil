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

abbreviation \<open>succ4 w \<equiv> succ2 (succ2 w)\<close>
abbreviation \<open>succ5 w \<equiv> succ4 (succ w)\<close>
abbreviation \<open>succ6 w \<equiv> succ2 (succ4 w)\<close>
abbreviation \<open>succ7 w \<equiv> succ6 (succ w)\<close>

context exp_val_word_sz_syntax
begin

lemma succ4: \<open>PROP P (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ5: \<open>PROP P (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ6: \<open>PROP P (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ7: \<open>PROP P (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

end

context exp2_val_word_sz_syntax
begin

sublocale succ4: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

sublocale succ5: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

sublocale succ6: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

sublocale succ7: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

end

context exp2_val_syntax
begin

sublocale succ4: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ4 (num \<Colon> sz)) e (succ4 (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ5: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ5 (num \<Colon> sz)) e (succ5 (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ6: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ6 (num \<Colon> sz)) e (succ6 (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ7: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ7 (num \<Colon> sz)) e (succ7 (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

end

context exp_val2_word_sz1_syntax
begin

sublocale succ4: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) (succ4 (num \<Colon> sz)) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ5: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) (succ5 (num \<Colon> sz)) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ6: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) (succ6 (num \<Colon> sz)) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ7: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) (succ7 (num \<Colon> sz)) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

end

context store_multiple_syntax
begin

sublocale succ4: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ4 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ4 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ4 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

sublocale succ5: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ5 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ5 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ5 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

sublocale succ6: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ6 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ6 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ6 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

sublocale succ7: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ7 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ7 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ7 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

end

context word_constructor
begin 

abbreviation 
  no_address_overlap_64_32 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_32 w\<^sub>1 w\<^sub>2 \<equiv> (
    w\<^sub>1 \<noteq> w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ (succ w\<^sub>2) \<and>
    w\<^sub>1 \<noteq> succ (succ (succ w\<^sub>2)) \<and>
    succ w\<^sub>1 \<noteq> w\<^sub>2 \<and> 
    succ (succ w\<^sub>1) \<noteq> w\<^sub>2 \<and>
    succ (succ (succ w\<^sub>1)) \<noteq> w\<^sub>2 \<and>
    succ (succ (succ (succ w\<^sub>1))) \<noteq> w\<^sub>2 \<and>
    succ (succ (succ (succ (succ w\<^sub>1)))) \<noteq> w\<^sub>2 \<and>
    succ (succ (succ (succ (succ (succ w\<^sub>1))))) \<noteq> w\<^sub>2 \<and>
    succ (succ (succ (succ (succ (succ (succ w\<^sub>1)))))) \<noteq> w\<^sub>2
)\<close>

lemma no_address_overlap_64_32: 
  assumes \<open>no_address_overlap_64_32 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ (succ w\<^sub>2)\<close> \<open>w\<^sub>1 \<noteq> succ (succ (succ w\<^sub>2))\<close> 
          \<open>succ w\<^sub>1 \<noteq> w\<^sub>2\<close>
          \<open>succ (succ w\<^sub>1) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ w\<^sub>1)) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ w\<^sub>1))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ w\<^sub>1)))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ (succ w\<^sub>1))))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ (succ (succ w\<^sub>1)))))) \<noteq> w\<^sub>2\<close>
  using assms by auto

abbreviation 
  no_address_overlap_64_64 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_64 w\<^sub>1 w\<^sub>2 \<equiv> (
    no_address_overlap_64_32 w\<^sub>1 w\<^sub>2 \<and>
    w\<^sub>1 \<noteq> succ (succ (succ (succ w\<^sub>2))) \<and>
    w\<^sub>1 \<noteq> succ (succ (succ (succ (succ w\<^sub>2)))) \<and>
    w\<^sub>1 \<noteq> succ (succ (succ (succ (succ (succ w\<^sub>2))))) \<and>
    w\<^sub>1 \<noteq> succ (succ (succ (succ (succ (succ (succ w\<^sub>2))))))
)\<close>

lemma no_address_overlap_64_64: 
  assumes \<open>no_address_overlap_64_64 w\<^sub>1 w\<^sub>2\<close> 
    shows \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ w\<^sub>2\<close> \<open>w\<^sub>1 \<noteq> succ (succ w\<^sub>2)\<close> \<open>w\<^sub>1 \<noteq> succ (succ (succ w\<^sub>2))\<close> 
          \<open>w\<^sub>1 \<noteq> succ (succ (succ (succ w\<^sub>2)))\<close> \<open>w\<^sub>1 \<noteq> succ (succ (succ (succ (succ w\<^sub>2))))\<close>
          \<open>w\<^sub>1 \<noteq> succ (succ (succ (succ (succ (succ w\<^sub>2)))))\<close> 
          \<open>w\<^sub>1 \<noteq> succ (succ (succ (succ (succ (succ (succ w\<^sub>2))))))\<close>
          \<open>succ w\<^sub>1 \<noteq> w\<^sub>2\<close>
          \<open>succ (succ w\<^sub>1) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ w\<^sub>1)) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ w\<^sub>1))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ w\<^sub>1)))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ (succ w\<^sub>1))))) \<noteq> w\<^sub>2\<close>
          \<open>succ (succ (succ (succ (succ (succ (succ w\<^sub>1)))))) \<noteq> w\<^sub>2\<close>
  using assms by auto

end

\<comment> \<open>Now we add an abbreviation for 64bit words in storage.\<close>

context storage_constructor
begin

abbreviation 
  storage_el64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el64 mem w v \<equiv> (storage_el32 mem w v)
    [succ4 w \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ5 w \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ6 w \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ7 w \<leftarrow> ext v \<sim> hi : 63 \<sim> lo : 56, 8]
\<close>

abbreviation 
  storage_be64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be64 mem w v \<equiv> mem
    [      w \<leftarrow> ext v \<sim> hi : 63 \<sim> lo : 56, 8]
    [succ  w \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ2 w \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ3 w \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ4 w \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
    [succ5 w \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ6 w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo : 8, 8]
    [succ7 w \<leftarrow> ext v \<sim> hi : 7 \<sim> lo : 0, 8]
\<close>

end

lemma type_storage_el64[simp]: \<open>type (storage_el64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_be64[simp]: \<open>type (storage_be64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

method solve_type_succ64I_scaffold methods recurs = (
  rule type_storage_el64 type_storage_be64 |
  solve_type_succ32I_scaffold recurs
) 

method solve_type_succ64I = (
  solve_type_succ64I_scaffold solve_type_succ64I
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
    shows \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = num \<Colon> 64\<close>
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
