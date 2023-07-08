theory Bitvector_Instance
  imports Bitvector_Syntax
begin

instantiation word :: word 
begin

definition
  word_constructor_word :: \<open>nat \<Rightarrow> nat \<Rightarrow> word\<close>
where
  \<open>(val \<Colon> sz) = Word val sz\<close>

definition
  true_word :: word
where
  \<open>true_word \<equiv> (1 \<Colon> 1)\<close>

definition
  false_word :: word
where
  \<open>false_word = (0 \<Colon> 1)\<close>

lemma true_neq_false_word: \<open>(true::word) \<noteq> false\<close>
  unfolding true_word_def false_word_def word_constructor_word_def by simp

lemma wordI:
  fixes w :: word 
  shows \<open>(\<And>a b. w = (a \<Colon> b) \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
  by (metis word.exhaust_sel word_constructor_word_def)

instance proof 
  show \<open>(true::word) \<noteq> false\<close>
    by (rule true_neq_false_word)
next 
  show \<open>\<And>nat sz nat' sz'. (((nat \<Colon> sz)::word) = (nat' \<Colon> sz')) = (nat = nat' \<and> sz = sz')\<close>
    by (simp add: word_constructor_word_def true_neq_false_word)
next
  show \<open>(true::word) = (1 \<Colon> 1)\<close>
    by (simp add: true_word_def)
next 
  show \<open>(false::word) = (0 \<Colon> 1)\<close>
    by (simp add: false_word_def)
next 
  show \<open>\<And>(w::word) Q. (\<And>a b. Q (a \<Colon> b)) \<Longrightarrow> Q w\<close>
    by (metis (mono_tags) wordI)
next
  show \<open>\<And>(w::word) Q. (\<And>a b. w = (a \<Colon> b) \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
    using wordI by auto
qed


end

lemma Word_simp: \<open>Word a b = (a \<Colon> b)\<close>
  by (simp add: word_constructor_word_def)

lemma bits_Word[simp]: "bits ((a \<Colon> b)::word) = b"
  unfolding word_constructor_word_def by auto


end