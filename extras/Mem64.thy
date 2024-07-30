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

lemma type_storage_el64: \<open>type (storage_el64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_be64: \<open>type (storage_be64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

method solve_type_succ64I_scaffold methods recurs = (
  rule type_storage_el64 type_storage_be64 |
  solve_type_succ32I_scaffold recurs
) 

method solve_type_succ64I = (
  solve_type_succ64I_scaffold solve_type_succ64I
) 

end
