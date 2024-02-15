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

lemma wordI:
  fixes w :: word assumes \<open>\<And>a b. w = (a \<Colon> b) \<Longrightarrow> Q\<close> shows Q
  using assms by (cases w, unfold word_constructor_word_def, blast)

function
  type_word :: \<open>word \<Rightarrow> Type\<close>
where
  \<open>type_word (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close>
  subgoal for P x by (rule wordI)
  subgoal unfolding word_constructor_word_def by auto
  .
termination by (standard, auto)

lemma true_neq_false_word: \<open>(true::word) \<noteq> false\<close>
  unfolding true_word_def false_word_def word_constructor_word_def by simp

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
qed auto


end

lemmas Word_simp = word_constructor_word_def[symmetric]

lemma word_szD: 
  assumes \<open>(num1 \<Colon> sz) \<noteq> (num2 \<Colon> sz)\<close>
    shows \<open>num1 \<noteq> num2\<close>
  using assms by simp

end