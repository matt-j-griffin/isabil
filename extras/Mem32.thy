theory Mem32
  imports Mem16 
          \<comment> \<open>Why am I doing this? - it looks like you must preload "interpretation"s to add lemmas
              to the context. If interpretations and lemma adding happens in parallel then the lemmas 
              don't seem to make it to the interpretation\<close>
          "../ExpressionSemantics/Expressions_Intros"
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

abbreviation \<open>succ2 w \<equiv> succ (succ w)\<close>
abbreviation \<open>succ3 w \<equiv> succ2 (succ w)\<close>

context exp_val_word_sz_syntax
begin

lemma succ2: \<open>PROP P (succ2 (num \<Colon> sz)) (succ2 (num \<Colon> sz)) (succ2 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ2_plus: \<open>PROP P (succ2 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ2 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ2 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) sz\<close>
  unfolding bv_plus.simps succ.simps by (rule word)

lemma succ3: \<open>PROP P (succ3 (num \<Colon> sz)) (succ3 (num \<Colon> sz)) (succ3 (num \<Colon> sz)) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ3_plus: \<open>PROP P (succ3 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ3 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ3 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) sz\<close>
  unfolding bv_plus.simps succ.simps by (rule word)

end

context exp2_val_word_sz_syntax
begin

sublocale succ2: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ2 (num \<Colon> sz)) (succ2 (num \<Colon> sz)) (succ2 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

sublocale succ3: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ3 (num \<Colon> sz)) (succ3 (num \<Colon> sz)) (succ3 (num \<Colon> sz)) sz e v w sz'\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word.is_word)

end

context exp2_val_syntax
begin

sublocale succ2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (num \<Colon> sz))) e (succ (succ (num \<Colon> sz))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ3: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (num \<Colon> sz)))) e (succ (succ (succ (num \<Colon> sz)))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

end

context exp_val2_word_sz1_syntax
begin


sublocale succ2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P(succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale succ3: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) sz e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

end

context store_multiple_syntax
begin

sublocale succ2: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

sublocale succ3: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) (succ (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) (succ (succ (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def succ.simps bv_plus.simps by (rule store_val)

end

\<comment> \<open>Now we add an abbreviation for 32bit words in storage.\<close>

context storage_constructor
begin

abbreviation
  storage_el32 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el32 mem w v \<equiv> (storage_el16 mem w v)
    [succ2 w \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ3 w \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
\<close>

abbreviation
  storage_be32 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be32 mem w v \<equiv> (storage_be16 (mem
     [     w \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
     [succ w \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8])
   (succ2 w) v)
\<close>

end

lemma type_storage_el32: \<open>type (storage_el32 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_be32: \<open>type (storage_be32 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

method solve_type_succ32I_scaffold methods recurs = (
  rule type_storage_el32 type_storage_be32 |
  solve_typeI_scaffold recurs
) 

method solve_type_succ32I = (
  solve_type_succ32I_scaffold solve_type_succ32I
) 

end
