theory Bitvector_Instance
  imports Bitvector_Syntax
begin

instantiation word :: word 
begin

definition
  word_constructor_word :: \<open>nat \<Rightarrow> nat \<Rightarrow> word\<close>
where
  \<open>(val \<Colon> sz) = Word val sz\<close>
(*
definition
  true_word :: word
where
  \<open>true_word \<equiv> (1 \<Colon> 1)\<close>

definition
  false_word :: word
where
  \<open>false_word = (0 \<Colon> 1)\<close>
*)
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
termination by lexicographic_order


function
  is_ok_word :: \<open>word \<Rightarrow> bool\<close>
where 
  \<open>is_ok_word (num \<Colon> sz) = (0 < sz \<and> num < 2 ^ sz)\<close>
  subgoal for P x by (rule wordI)
  unfolding word_constructor_word_def by auto
termination by lexicographic_order

function 
  typed_ok_word :: \<open>TypingContext \<Rightarrow> word \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typed_ok_word \<Gamma> (num \<Colon> sz) t = (((num \<Colon> sz)::word) is ok \<and> \<Gamma> is ok \<and> t = imm\<langle>sz\<rangle>)\<close>
  subgoal for P x 
    apply (cases x, auto)
    subgoal for \<Gamma> w t
      unfolding word_constructor_word_def by (cases w, auto)
    .
  unfolding word_constructor_word_def by auto
termination by (standard, auto)

instance proof
  fix \<Gamma> t and a :: word
  assume typed_ok: "\<Gamma> \<turnstile> a :: t"
  show "t is ok"
  proof (cases a)
    case (Word x1 x2)
    show ?thesis 
      using typed_ok unfolding Word word_constructor_word_def[symmetric] by auto
  qed
next
  fix nat sz nat' sz' :: nat
  show "(nat \<Colon> sz::word) = nat' \<Colon> sz' \<equiv> nat = nat' \<and> sz = sz'"
    by (simp add: word_constructor_word_def)
next
  fix w :: word
    and Q :: "word \<Rightarrow> bool"
  assume "\<And>a b. Q (a \<Colon> b)"
  thus "Q w"
    by (metis (mono_tags) wordI)
next
  fix w :: word
    and Q :: bool
  assume "\<And>a b. w = a \<Colon> b \<Longrightarrow> Q"
  thus Q
    by (rule wordI) 
qed auto

end

lemmas Word_simp = word_constructor_word_def[symmetric]

lemma word_szD: 
  assumes \<open>(num1 \<Colon> sz) \<noteq> (num2 \<Colon> sz)\<close>
    shows \<open>num1 \<noteq> num2\<close>
  using assms by simp

method typec_word = (
  rule T_INT, typec_context, rule TWF_WORD, linarith, fastforce
)

end