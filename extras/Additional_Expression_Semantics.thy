
section \<open>Additional Expression Semantics\<close>

text \<open>Additional big step semantics for expressions, designed to reduce the proof burden. 
      This theory is in development and subject to change.\<close>

theory Additional_Expression_Semantics
  imports "../ExpressionSemantics/Expression_Intros"
begin

no_notation HOL.Not (\<open>~ _\<close> [40] 40)
no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)

text \<open>Succinct representation of big and little endian storage\<close>

context storage_constructor
begin

fun 
  nested_succ :: \<open>val \<Rightarrow> nat \<Rightarrow> val\<close>
where
  \<open>nested_succ w 0 = w\<close> |
  \<open>nested_succ w (Suc n) = nested_succ (succ w) n\<close>

abbreviation 
  storage32 :: \<open>val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close>
where
  \<open>storage32 mem num\<^sub>1 num\<^sub>2 \<equiv> (mem
    [num\<^sub>1 \<Colon> 64 \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ (num\<^sub>1 \<Colon> 64) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ (num\<^sub>1 \<Colon> 64)) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ (num\<^sub>1 \<Colon> 64))) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8])
\<close>

abbreviation 
  storage64 :: \<open>val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close>
where
  \<open>storage64 mem num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>2 \<equiv> (mem
    [num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24, 8]
    [succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ (succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56, 8])
\<close>

end

declare eval_exps_pred_exp.simps[simp del]
declare step_pred_exp.simps[simp del]

lemma refl_load_wordI: \<open>\<Delta> \<turnstile> v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>v \<Colon> sz, sz][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, ed]:usz \<leadsto>* (num\<^sub>v \<Colon> sz)\<close>
  apply (rule_tac REDUCE[of _ _ \<open>num\<^sub>v \<Colon> sz\<close>])
  apply solve_exp
  by (rule REFL_WORD)

lemmas word8_refl_load_word8I = refl_load_wordI[of _ _ _ _ _ 8]

lemma mod_Suc_neqI:
  assumes \<open>num\<^sub>1 mod sz\<^sub>1 \<noteq> num\<^sub>2 mod sz\<^sub>1\<close>
    shows \<open>Suc num\<^sub>1 mod sz\<^sub>1 \<noteq> Suc num\<^sub>2 mod sz\<^sub>1\<close>
  using assms mod_Suc by auto

lemma mod_lt_neqI:
  fixes num\<^sub>1 :: nat
  assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> and \<open>num\<^sub>1 < sz\<^sub>1\<close> and \<open>num\<^sub>2 < sz\<^sub>1\<close>
    shows \<open>num\<^sub>1 mod sz\<^sub>1 \<noteq> num\<^sub>2 mod sz\<^sub>1\<close>
  using assms mod_Suc by auto

lemma succ_lt_neqI: 
  assumes \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq> num\<^sub>2 \<Colon> sz\<^sub>2\<close> and \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>num\<^sub>2 < 2 ^ sz\<^sub>1\<close>
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding succ.simps bv_plus.simps apply auto
  using assms mod_Suc_neqI mod_lt_neqI by force

lemma succ_left_neqI: 
    fixes w :: word
  assumes \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> and \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close>
    shows \<open>succ (succ w) \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using mod_Suc_neqI by auto
qed

lemma succ_right_neqI: 
    fixes w :: word
  assumes \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ w\<close> and \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close>
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (succ w)\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using mod_Suc_neqI by auto
qed

lemma succ_succ_neqI: 
    fixes w :: word
  assumes \<open>succ w \<noteq> succ w'\<close>
    shows \<open>succ (succ w) \<noteq> succ (succ w')\<close>
proof (cases w rule: word_exhaust)
  case w: (1 num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    proof (cases w' rule: word_exhaust)
      case w': (1 num\<^sub>2 sz\<^sub>2)
      show ?thesis 
        using w w' assms apply safe
        unfolding succ.simps bv_plus.simps apply auto
        using mod_Suc_neqI by auto
    qed
qed

lemma refl8_load_storage_skip64I:
  assumes \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<^sub>4\<close>
      and \<open>w\<^sub>2 \<noteq> (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))))\<close>
    shows \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>1 \<leftarrow> v\<^sub>2, 8][w\<^sub>2 \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<^sub>4\<close>
  apply (insert assms)
  unfolding eval_exps_pred_exp.simps eval_exp.simps eval_exp_storage eval_exp.simps by simp

lemma refl8_load_skip64I:
  assumes \<open>\<Delta> \<turnstile> (Val v\<^sub>1)[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<^sub>4\<close> and \<open>type v\<^sub>1 = mem\<langle>64, 8\<rangle>\<close>
      and \<open>w\<^sub>2 \<noteq> (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close> 
      and \<open>w\<^sub>2 \<noteq> succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))\<close>
      and \<open>w\<^sub>2 \<noteq> succ (succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))))\<close>
    shows \<open>\<Delta> \<turnstile> v\<^sub>1[w\<^sub>2 \<leftarrow> v\<^sub>3, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<^sub>4\<close>
proof (cases v\<^sub>1 rule: val_exhaust)
  case (1 num sz)
  then show ?thesis 
    using assms(2) by simp
next
  case (2 str t)
  then show ?thesis 
    using assms unfolding eval_exps_pred_exp.simps eval_exp.simps eval_exp_storage eval_exp.simps by simp
next
  case (3 mem w v' sz)
  then show ?thesis 
    using assms apply clarify
    apply (cases w rule: word_exhaust, simp)
    apply (rule refl8_load_storage_skip64I)
    unfolding Val_simp_storage by blast+
qed

method solve_succ_neq = 
  match conclusion in \<open>succ (succ _) \<noteq> succ (succ _)\<close> \<Rightarrow> \<open>rule succ_succ_neqI, solve_succ_neq\<close>
                    \<bar> \<open>succ (succ _) \<noteq> succ _\<close> \<Rightarrow> \<open>rule succ_left_neqI, assumption, assumption\<close>
                    \<bar> \<open>succ _ \<noteq> succ (succ _)\<close> \<Rightarrow> \<open>rule succ_right_neqI, assumption, assumption\<close>
                    \<bar> \<open>succ _ \<noteq> succ _\<close> \<Rightarrow> \<open>rule succ_lt_neqI, assumption, assumption, assumption\<close>
                    \<bar> \<open>succ _ \<noteq> (_ \<Colon> _)\<close> \<Rightarrow> \<open>assumption\<close>
                    \<bar> \<open>(_ \<Colon> _) \<noteq> succ _\<close> \<Rightarrow> \<open>assumption\<close>
                    \<bar> \<open>(_ \<Colon> _) \<noteq> (_ \<Colon> _)\<close> \<Rightarrow> \<open>assumption\<close>

text \<open>64bit read skipping a 32bit word\<close>

abbreviation 
  no_address_overlap_64_32 :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_32 num\<^sub>1 num\<^sub>2 sz \<equiv> (
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> (num\<^sub>2 \<Colon> sz) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (num\<^sub>2 \<Colon> sz) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (num\<^sub>2 \<Colon> sz)) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (succ (num\<^sub>2 \<Colon> sz))) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (succ (succ (num\<^sub>2 \<Colon> sz)))) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (succ (succ (succ (num\<^sub>2 \<Colon> sz))))) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (succ (succ (succ (succ (num\<^sub>2 \<Colon> sz)))))) \<and>
    ((num\<^sub>1 \<Colon> sz)::word) \<noteq> succ (succ (succ (succ (succ (succ (succ (num\<^sub>2 \<Colon> sz))))))) \<and>
    succ ((num\<^sub>1 \<Colon> sz)::word) \<noteq> (num\<^sub>2 \<Colon> sz) \<and> 
    succ (succ ((num\<^sub>1 \<Colon> sz)::word)) \<noteq> (num\<^sub>2 \<Colon> sz) \<and>
    succ (succ (succ ((num\<^sub>1 \<Colon> sz)::word))) \<noteq>(num\<^sub>2 \<Colon> sz)
)\<close>

lemma refl32_load_rev_cut64I:
  assumes \<open>\<Delta> \<turnstile> mem[w' \<leftarrow> v', 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
      and \<open>num\<^sub>1 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and \<open>num\<^sub>3 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and \<open>no_address_overlap_64_32 num\<^sub>1 num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> mem[w' \<leftarrow> v', 8][(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, 8][succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, 8][succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> v\<^sub>3, 8][succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> v\<^sub>4, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
  apply (insert assms, elim conjE)
  apply (rule refl8_load_storage_skip64I)+
  apply assumption
  by solve_succ_neq+

lemma refl32_load_all_rev_cut64I:
  assumes \<open>\<Delta> \<turnstile> (Val mem)[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close> and \<open>type mem = mem\<langle>64, 8\<rangle>\<close>
      and \<open>num\<^sub>1 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and \<open>num\<^sub>3 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and \<open>no_address_overlap_64_32 num\<^sub>1 num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> mem[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, 8][succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, 8][succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> v\<^sub>3, 8][succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> v\<^sub>4, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
  apply (insert assms, elim conjE)
  apply (rule refl8_load_storage_skip64I)+
  apply (rule refl8_load_skip64I)
  apply assumption+
  by solve_succ_neq+

text \<open>64bit read skipping a 64bit word\<close>

abbreviation 
  no_address_overlap_64_64 :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>
where 
  \<open>no_address_overlap_64_64 num\<^sub>1 num\<^sub>2 sz \<equiv> (
    no_address_overlap_64_32 num\<^sub>1 num\<^sub>2 sz \<and>
    succ (succ (succ (succ ((num\<^sub>1 \<Colon> sz)::word)))) \<noteq> (num\<^sub>2 \<Colon> sz) \<and>
    succ (succ (succ (succ (succ ((num\<^sub>1 \<Colon> sz)::word))))) \<noteq> (num\<^sub>2 \<Colon> sz) \<and>
    succ (succ (succ (succ (succ (succ ((num\<^sub>1 \<Colon> sz)::word)))))) \<noteq> (num\<^sub>2 \<Colon> sz) \<and>
    succ (succ (succ (succ (succ (succ (succ ((num\<^sub>1 \<Colon> sz)::word))))))) \<noteq> (num\<^sub>2 \<Colon> sz)
)\<close>

lemma refl64_load_rev_cut64I:
  assumes \<open>\<Delta> \<turnstile> mem[w' \<leftarrow> v', 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
      and \<open>num\<^sub>1 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and \<open>num\<^sub>3 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and \<open>no_address_overlap_64_64 num\<^sub>1 num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> 
    shows \<open>\<Delta> \<turnstile> mem[w' \<leftarrow> v', 8][(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, 8][succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, 8][succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> v\<^sub>3, 8][succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> v\<^sub>4, 8][succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> v\<^sub>5, 8][succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> v\<^sub>6, 8][succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> v\<^sub>7, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))) \<leftarrow> v\<^sub>8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
  apply (insert assms, elim conjE)
  apply (rule refl32_load_rev_cut64I | rule refl8_load_storage_skip64I)+
  apply assumption+
  apply (intro conjI)
  apply assumption+
  by solve_succ_neq+

lemma refl64_load_all_rev_cut64I:
  assumes \<open>\<Delta> \<turnstile> (Val mem)[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close> and \<open>type mem = mem\<langle>64, 8\<rangle>\<close>
      and \<open>num\<^sub>1 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and \<open>num\<^sub>3 < 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and \<open>no_address_overlap_64_64 num\<^sub>1 num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> 
    shows \<open>\<Delta> \<turnstile> mem[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>1, 8][succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>2, 8][succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> v\<^sub>3, 8][succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> v\<^sub>4, 8][succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> v\<^sub>5, 8][succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> v\<^sub>6, 8][succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> v\<^sub>7, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))) \<leftarrow> v\<^sub>8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* v\<close>
  apply (insert assms, elim conjE)
  apply (rule refl32_load_all_rev_cut64I | rule refl8_load_storage_skip64I)+
  apply assumption+
  apply (intro conjI)
  apply assumption+
  by solve_succ_neq+


subsection \<open>Big-step load evaluation\<close>

lemma Suc_3: "3 + x = Suc (Suc (Suc x))"
  by auto

lemma Suc_4: "4 + x = Suc (Suc (Suc (Suc x)))"
  by auto

lemma Suc_5: "5 + x = Suc (Suc (Suc (Suc (Suc x))))"
  by auto

lemma Suc_6: "6 + x = Suc (Suc (Suc (Suc (Suc (Suc x)))))"
  by auto


lemma word8_refl_load_rev_word32I: \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* (((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) \<cdot> (num\<^sub>2 \<Colon> 8)) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps by simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER) using LOAD_BYTE_FROM_NEXT_MEM_INTER
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps by simp
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    by (rule LOAD_BYTE_WORD)
  apply (rule REDUCE[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>((nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4)) \<Colon> 8 + 8) \<cdot> (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>(nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4))))) \<Colon> 8 + 8 + 8) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps by (rule REFL_WORD)

lemma word8_refl_load_rev_ext_concat_word32: 
  assumes \<open>num < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* (num \<Colon> 32)\<close>
  apply (subgoal_tac \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* ((((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) \<cdot>
      ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
     ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8) \<cdot>
    ext num \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0)\<close>)
  apply (metis assms extract_concat32)
  unfolding xtract.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  using word8_refl_load_rev_word32I by blast


lemma word8_refl_load_rev_word64I: \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (((((((num\<^sub>8 \<Colon> 8) \<cdot> (num\<^sub>7 \<Colon> 8)) \<cdot> (num\<^sub>6 \<Colon> 8)) \<cdot> (num\<^sub>5 \<Colon> 8)) \<cdot> (num\<^sub>4 \<Colon> 8)) \<cdot> (num\<^sub>3 \<Colon> 8)) \<cdot> (num\<^sub>2 \<Colon> 8)) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps apply (rule exI[of _ "Suc (Suc (Suc (Suc (Suc (Suc
   (Suc num\<^sub>a mod 18446744073709551616) mod
  18446744073709551616) mod
                        18446744073709551616) mod
                   18446744073709551616) mod
              18446744073709551616) mod
         18446744073709551616) mod
    18446744073709551616"])
    by simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(64 - 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps by simp
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(56 - 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64))))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(48 - 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64)))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u(40 - 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq Suc_3
  apply (rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64), el]:u(32 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64))) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64), el]:u(32 - 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq Suc_3 Suc_4
  apply (rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq Suc_3 Suc_4 Suc_5
  apply (rule REDUCE[of _ _ \<open>(((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule LOAD_WORD_EL_MEM_INTER, linarith, linarith)
    unfolding succ.simps bv_plus.simps
    by simp
  apply (rule REDUCE[of _ _ \<open>(((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8)) @ (v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>7 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    apply (rule LOAD_BYTE_FROM_NEXT_MEM_INTER)
    unfolding succ.simps bv_plus.simps apply simp_all
    unfolding mod_Suc_eq 
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(((((((v[num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc (Suc (Suc num\<^sub>a))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>5 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc num\<^sub>a)))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>6 \<Colon> 8, 8][Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>7 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>8 \<Colon> 8, 8][succ (Suc (Suc (Suc (Suc (Suc (Suc num\<^sub>a))))) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8)) @ (num\<^sub>7 \<Colon> 8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_RHS)
    by (rule LOAD_BYTE_WORD)
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq Suc_3 Suc_4 Suc_5 Suc_6
  apply (rule REDUCE[of _ _ \<open>(((((((num\<^sub>8 \<Colon> 8) @ (num\<^sub>7 \<Colon> 8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  subgoal
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    apply (rule CONCAT_LHS_WORD)
    by (rule LOAD_BYTE_WORD)
  apply (rule REDUCE[of _ _ \<open>(((((((num\<^sub>8 \<Colon> 8) \<cdot> (num\<^sub>7 \<Colon> 8)) @ (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>((((((nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8)) \<Colon> 8 + 8) \<cdot> (num\<^sub>6 \<Colon> 8)) @ (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>(((((nat (concat_bit 8 (int num\<^sub>6) (int (nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8))))) \<Colon> 8 + 8 + 8) \<cdot> (num\<^sub>5 \<Colon> 8)) @ (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>((((nat (concat_bit 8 (int num\<^sub>5) (int (nat (concat_bit 8 (int num\<^sub>6) (int (nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8)))))))) \<Colon> 8 + 8 + 8 + 8) \<cdot> (num\<^sub>4 \<Colon> 8)) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>(((nat (concat_bit 8 (int num\<^sub>4) (int (nat (concat_bit 8 (int num\<^sub>5) (int (nat (concat_bit 8 (int num\<^sub>6) (int (nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8))))))))))) \<Colon> 8 + 8 + 8 + 8 + 8) \<cdot> (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>((nat (concat_bit 8 (int num\<^sub>3) (int (nat (concat_bit 8 (int num\<^sub>4) (int (nat (concat_bit 8 (int num\<^sub>5) (int (nat (concat_bit 8 (int num\<^sub>6) (int (nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8)))))))))))))) \<Colon> 8 + 8 + 8 + 8 + 8 + 8) \<cdot> (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>(nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int (nat (concat_bit 8 (int num\<^sub>4) (int (nat (concat_bit 8 (int num\<^sub>5) (int (nat (concat_bit 8 (int num\<^sub>6) (int (nat (concat_bit 8 (int num\<^sub>7) (int num\<^sub>8))))))))))))))))) \<Colon> 8 + 8 + 8 + 8 + 8 + 8 + 8) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps by (rule REFL_WORD)



lemma word8_refl_load_rev_ext_concat_word64I: 
  assumes \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage64 v num\<^sub>a 64 num)[num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (num \<Colon> 64)\<close>
  apply (subgoal_tac \<open>\<Delta> \<turnstile> v[num\<^sub>a \<Colon> 64 \<leftarrow> ext num \<Colon> 64 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32, 8][succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40, 8][succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64)))))) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48, 8][succ (succ (succ (succ (succ (succ (succ (num\<^sub>a \<Colon> 64))))))) \<leftarrow> ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56, 8][num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (((((((ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56 \<cdot>
          ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) \<cdot>
         ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) \<cdot>
        ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) \<cdot>
       ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) \<cdot>
      ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
     ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo : 8) \<cdot>
    ext num \<Colon> 64 \<sim> hi : 7 \<sim> lo : 0)\<close>)
  apply (metis assms extract_concat64)
  unfolding xtract.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  using word8_refl_load_rev_word64I by blast
(*
lemma word8_refl_load_word32I: \<open>\<Delta> \<turnstile> v[succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u32 \<leadsto>* (((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) \<cdot> (num\<^sub>2 \<Colon> 8)) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>
  apply (rule REDUCE[of _ _ \<open>(v[succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (v[succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][num\<^sub>a \<Colon> 64, el]:u8)\<close>])
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>(v[succ (succ (succ (num\<^sub>a \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (succ (num\<^sub>a \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (num\<^sub>a \<Colon> 64), el]:u(32 - 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  apply (rule REDUCE[of _ _ \<open>((v[succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][(Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>((v[succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (v[succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][(Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  apply (metis dvd_mod dvd_mod_imp_dvd even_Suc even_numeral)
  apply (rule REDUCE[of _ _ \<open>((v[succ (succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>((v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>((v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  subgoal
    unfolding mod_Suc_eq
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  subgoal
    unfolding mod_Suc_eq
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>a \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding succ.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
  unfolding mod_Suc_eq
  apply (rule REDUCE[of _ _ \<open>((v[(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc num\<^sub>a mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u8 @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  subgoal
    unfolding mod_Suc_eq
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc num\<^sub>a) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u8 @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  subgoal
    unfolding mod_Suc_eq
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>((v[(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][(Suc (Suc (Suc num\<^sub>a)) mod 18446744073709551616 \<Colon> 64), el]:u8 @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  subgoal
    unfolding mod_Suc_eq
    apply (induct num\<^sub>a)
    unfolding mod_Suc by simp_all
  apply (rule REDUCE[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>(((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>((nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4)) \<Colon> 8 + 8) \<cdot> (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>(nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4))))) \<Colon> 8 + 8 + 8) \<cdot> (num\<^sub>1 \<Colon> 8)\<close>])
  apply solve_exp
  unfolding bv_concat.simps[symmetric]
  by simp
*)
lemma word8_refl_load_extend_word32I:
  \<open>\<Delta> \<turnstile> extend:64[mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8]
                      [succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8]
                      [succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8]
                      [succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8]
                      [addr \<Colon> 64, el]:u32] \<leadsto>* (exts (((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) \<cdot> (num\<^sub>2 \<Colon> 8)) \<cdot> (num\<^sub>1 \<Colon> 8) \<sim> hi : 63 \<sim> lo : 0)\<close>
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (addr \<Colon> 64), el]:u(32 - 8)) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][addr \<Colon> 64, el]:u8)]\<close>])
  apply (rule CAST_REDUCE)
  apply (rule LOAD_WORD_EL_MEM_SUCC3, linarith, linarith)
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (addr \<Colon> 64), el]:u(32 - 8)) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][addr \<Colon> 64, el]:u8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct addr)
    unfolding Suc_3 mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (addr \<Colon> 64), el]:u(32 - 8)) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][addr \<Colon> 64, el]:u8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct addr)
    unfolding mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (addr \<Colon> 64), el]:u(32 - 8)) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][addr \<Colon> 64, el]:u8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct addr)
    unfolding mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][succ (addr \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (succ (addr \<Colon> 64)) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (succ (addr \<Colon> 64))) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (addr \<Colon> 64), el]:u(32 - 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps
    by solve_exp
  apply simp
  unfolding succ.simps(1)[of addr] bv_plus.simps mod_simps apply simp
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][(Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc addr mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc addr mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  apply (rule CAST_REDUCE)
  apply (rule CONCAT_LHS_WORD)
  apply (rule LOAD_WORD_EL_MEM_SUCC2, linarith, linarith)
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][(Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc addr mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct \<open>Suc addr mod 18446744073709551616\<close>, simp)
    unfolding mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][(Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc addr mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct \<open>Suc addr mod 18446744073709551616\<close>, simp)
    unfolding mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[(mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][(Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>2 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (succ (Suc addr mod 18446744073709551616 \<Colon> 64)) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc addr mod 18446744073709551616 \<Colon> 64), el]:u(24 - 8) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps
    by solve_exp
  apply simp
  unfolding succ.simps(1)[of \<open>Suc addr mod 18446744073709551616\<close>] bv_plus.simps mod_simps apply simp
  unfolding mod_simps
  apply (rule REDUCE[of _ _ \<open>extend:64[((mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  apply (rule CAST_REDUCE)
  apply (rule CONCAT_LHS_WORD)
  apply (rule CONCAT_LHS_WORD)
  apply (rule LOAD_WORD_EL_MEM_SUCC, linarith, linarith)
  apply (rule REDUCE[of _ _ \<open>extend:64[((mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64, el]:u8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps apply solve_exp
    apply simp
    apply (induct \<open>Suc addr mod 18446744073709551616\<close>, simp)
    unfolding mod_Suc by auto
  apply (rule REDUCE[of _ _ \<open>extend:64[((mem'[addr \<Colon> 64 \<leftarrow> num\<^sub>1 \<Colon> 8, 8][Suc addr mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>2 \<Colon> 8, 8][Suc (Suc addr) mod 18446744073709551616 \<Colon> 64 \<leftarrow> num\<^sub>3 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64) \<leftarrow> num\<^sub>4 \<Colon> 8, 8][succ (Suc (Suc addr) mod 18446744073709551616 \<Colon> 64), el]:u(16 - 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  subgoal
    unfolding succ.simps bv_plus.simps mod_simps
    by solve_exp
  apply simp
  unfolding succ.simps(1)[of \<open>Suc (Suc addr) mod 18446744073709551616\<close>] bv_plus.simps mod_simps apply simp
  unfolding mod_simps
  apply (rule REDUCE[of _ _ \<open>extend:64[(((num\<^sub>4 \<Colon> 8) @ (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>extend:64[(((num\<^sub>4 \<Colon> 8) \<cdot> (num\<^sub>3 \<Colon> 8)) @ (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>extend:64[((nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4)) \<Colon> 8 + 8) \<cdot> (num\<^sub>2 \<Colon> 8)) @ (num\<^sub>1 \<Colon> 8)]\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply (rule REDUCE[of _ _ \<open>extend:64[(nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4))))) \<Colon> 8 + 8 + 8) \<cdot> (num\<^sub>1 \<Colon> 8)]\<close>])
  apply solve_exp
  unfolding bv_concat.simps
  apply solve_exp
  apply (rule REDUCE[of _ _ \<open>exts (nat (concat_bit 8 (int num\<^sub>1) (int (nat (concat_bit 8 (int num\<^sub>2) (int (nat (concat_bit 8 (int num\<^sub>3) (int num\<^sub>4)))))))) \<Colon> 8 + 8 + 8 + 8) \<sim> hi : (64 - 1) \<sim> lo : 0\<close>])
  apply solve_exp
  unfolding sxtract.simps
  unfolding bv_concat.simps[symmetric] by simp

lemma word8_refl_load_rev_ext_concat_word32I:
  assumes \<open>val < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> extend:64[(storage32 mem' addr val)[addr \<Colon> 64, el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
  apply (subgoal_tac \<open>\<Delta> \<turnstile> extend:64[(storage32 mem' addr val)[addr \<Colon> 64, el]:u32] \<leadsto>* exts ((((ext val \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) \<cdot> (ext val \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16)) \<cdot> (ext val \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8)) \<cdot> (ext val \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0)) \<sim> hi : 63 \<sim> lo : 0\<close>)
  subgoal 
    apply (insert assms)
    unfolding extract_concat32[of val] sxtract_lt_extend by blast
  subgoal
    unfolding xtract.simps apply (simp add: bv_plus.simps del: bv_concat.simps)
    by (rule word8_refl_load_extend_word32I)
  .
  
subsection \<open>Store word\<close>

lemma refl_store_wordI:
  assumes \<open>0 < sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>
  apply (insert assms)
  apply (rule_tac REDUCE[of _ _ \<open>v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  apply solve_exp
  by (rule REFL_STORAGE)

lemma refl_store_word_in_memI:
  assumes \<open>0 < sz\<^sub>m\<^sub>e\<^sub>m\<close>
    shows \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>
  apply (insert assms)
  apply (frule refl_store_wordI[of _ \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>])
  unfolding Val_simp_storage by simp_all

lemma word8_refl_store_word8I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:u8 \<leftarrow> (num\<^sub>4 \<Colon> 8) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> 8, 8]\<close>
  apply (rule refl_store_wordI)
  apply linarith
  apply (insert assms)
  by assumption

lemma word8_refl_store_word8_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:u8 \<leftarrow> (num\<^sub>4 \<Colon> 8) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> 8, 8]\<close>
  apply (rule refl_store_word_in_memI) 
  by linarith

lemma word8_refl_store_el_word16I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>4 \<Colon> 16) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8, 8]\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 16]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u16 - 8 \<leftarrow> high:16 - 8[num\<^sub>4 \<Colon> 16]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 16]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 16 - 1 \<sim> lo : 16 - 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 16) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8\<close>])
  apply solve_exp
  unfolding succ.simps xtract.simps bv_plus.simps apply simp
  by (rule word8_refl_store_word8_in_memI)

lemma word8_refl_store_el_word16_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>4 \<Colon> 16) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 15 \<sim> lo : 8, 8]\<close>
  using word8_refl_store_el_word16I by (simp add: storage_constructor_exp_def)

lemma word8_refl_store_el_word24I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u24 \<leftarrow> (num\<^sub>4 \<Colon> 24) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 23 \<sim> lo : 16, 8]\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 24]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u24 - 8 \<leftarrow> high:24 - 8[num\<^sub>4 \<Colon> 24]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 24]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u16 \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 24 - 1 \<sim> lo : 24 - 16\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 24) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u16 \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 23 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 16 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u16 \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 23 \<sim> lo : 8\<close>])
  subgoal
    unfolding succ.simps xtract.simps bv_plus.simps apply simp
    by solve_exp
  using word8_refl_store_el_word16_in_memI[of \<Delta> v num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r "take_bit 8 num\<^sub>4" "Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r" "take_bit 16 (drop_bit 8 num\<^sub>4)"]
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 8 16 \<open>drop_bit 8 num\<^sub>4\<close>] drop_bit_drop_bit take_bit_take_bit 
  by simp

lemma word8_refl_store_el_word24_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u24 \<leftarrow> (num\<^sub>4 \<Colon> 24) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 24 \<sim> hi : 23 \<sim> lo : 16, 8]\<close>
  using word8_refl_store_el_word24I by (simp add: storage_constructor_exp_def)

method refl_store = 
  (match conclusion in \<open>_ \<turnstile> e with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz) \<leadsto>* _\<close> for e num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>4 \<Rightarrow>
     \<open>rule REDUCE[of _ _ \<open>(e with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> sz]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - 8 \<leftarrow> high:sz - 8[num\<^sub>4 \<Colon> sz]\<close>]\<close>,
   solve_exp,
   simp)

lemma word8_refl_store_el_word32I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>4 \<Colon> 32) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8]\<close>
  apply (insert assms)
  apply refl_store
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 32]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u24 \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 32 - 1 \<sim> lo : 32 - 24\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 32) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u24 \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u24 \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 8\<close>])
  subgoal
    unfolding succ.simps xtract.simps bv_plus.simps apply simp
    by solve_exp
  using word8_refl_store_el_word24_in_memI[of \<Delta> v num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<open>take_bit 8 num\<^sub>4\<close> \<open>Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> \<open>take_bit 24 (drop_bit 8 num\<^sub>4)\<close>]
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 16 24 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 8 24 \<open>drop_bit 8 num\<^sub>4\<close>]
            drop_bit_drop_bit take_bit_take_bit 
  by simp

lemma word8_refl_store_el_word32_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>4 \<Colon> 32) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8]\<close>
  using word8_refl_store_el_word32I by (simp add: storage_constructor_exp_def)

lemma word8_refl_store_el_word40I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u40 \<leftarrow> (num\<^sub>4 \<Colon> 40) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 39 \<sim> lo : 32, 8]\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 40]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u40 - 8 \<leftarrow> high:40 - 8[num\<^sub>4 \<Colon> 40]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 40]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u32 \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 40 - 1 \<sim> lo : 40 - 32\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 40) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u32 \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 39 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u32 \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 39 \<sim> lo : 8\<close>])
  unfolding succ.simps xtract.simps bv_plus.simps apply simp
  apply solve_exp
  unfolding drop_bit_mask_eq apply simp
  using word8_refl_store_el_word32_in_memI[of \<Delta> \<open>v\<close> num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<open>take_bit 8 num\<^sub>4\<close> "Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r" "take_bit 32 (drop_bit 8 num\<^sub>4)"] 
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 24 32 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 16 32 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 8 32 \<open>drop_bit 8 num\<^sub>4\<close>]
            drop_bit_drop_bit take_bit_take_bit 
  by simp  

lemma word8_refl_store_el_word40_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u40 \<leftarrow> (num\<^sub>4 \<Colon> 40) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 39 \<sim> lo : 32, 8]\<close>
  using word8_refl_store_el_word40I by (simp add: storage_constructor_exp_def)

lemma word8_refl_store_el_word48I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u48 \<leftarrow> (num\<^sub>4 \<Colon> 48) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 39 \<sim> lo : 32, 8][succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 47 \<sim> lo : 40, 8]\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 48]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u48 - 8 \<leftarrow> high:48 - 8[num\<^sub>4 \<Colon> 48]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 48]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u40 \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 48 - 1 \<sim> lo : 48 - 40\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>((Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 48) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u40 \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 47 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 40 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u40 \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 47 \<sim> lo : 8\<close>])
  unfolding succ.simps xtract.simps bv_plus.simps apply simp
  apply solve_exp
  unfolding drop_bit_mask_eq apply simp
  using word8_refl_store_el_word40_in_memI[of \<Delta> \<open>v\<close> num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r "take_bit 8 num\<^sub>4" "Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r" "take_bit 40 (drop_bit 8 num\<^sub>4)"]
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 32 40 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 24 40 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 16 40 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 8 40 \<open>drop_bit 8 num\<^sub>4\<close>]
            drop_bit_drop_bit take_bit_take_bit 
  by simp  

lemma word8_refl_store_el_word48_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u48 \<leftarrow> (num\<^sub>4 \<Colon> 48) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 39 \<sim> lo : 32, 8][succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>4 \<Colon> 48 \<sim> hi : 47 \<sim> lo : 40, 8]\<close>
  using word8_refl_store_el_word48I by (simp add: storage_constructor_exp_def)

lemma word8_refl_store_el_word56I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u56 \<leftarrow> (num\<^sub>4 \<Colon> 56) \<leadsto>* v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 39 \<sim> lo : 32, 8][succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 47 \<sim> lo : 40, 8][succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 55 \<sim> lo : 48, 8]\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 56]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56 - 8 \<leftarrow> high:56 - 8[num\<^sub>4 \<Colon> 56]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 56]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u48 \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 56 - 1 \<sim> lo : 56 - 48\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 56) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u48 \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 55 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u48 \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 55 \<sim> lo : 8\<close>])
  unfolding succ.simps xtract.simps bv_plus.simps apply simp
  apply solve_exp
  unfolding drop_bit_mask_eq apply simp
  using word8_refl_store_el_word48_in_memI[of \<Delta> v num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r "take_bit 8 num\<^sub>4" "Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r" "take_bit 48 
               (drop_bit 8 num\<^sub>4)"]
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 40 48 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 32 48 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 24 48 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 16 48 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 8 48 \<open>drop_bit 8 num\<^sub>4\<close>]
            drop_bit_drop_bit take_bit_take_bit 
  by simp

lemma word8_refl_store_el_word56_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u56 \<leftarrow> (num\<^sub>4 \<Colon> 56) \<leadsto>* v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 7 \<sim> lo : 0, 8][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 15 \<sim> lo : 8, 8][succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 23 \<sim> lo : 16, 8][succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 31 \<sim> lo : 24, 8][succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 39 \<sim> lo : 32, 8][succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 47 \<sim> lo : 40, 8][succ (succ (succ (succ (succ (succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> ext num\<^sub>4 \<Colon> 56 \<sim> hi : 55 \<sim> lo : 48, 8]\<close>
  using word8_refl_store_el_word56I by (simp add: storage_constructor_exp_def)

lemma word8_refl_store_el_word64I:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v) with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>4 \<Colon> 64) \<leadsto>* storage64 v num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>4\<close>
  apply (insert assms)
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 64]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u64 - 8 \<leftarrow> high:64 - 8[num\<^sub>4 \<Colon> 64]\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> low:8[num\<^sub>4 \<Colon> 64]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56 \<leftarrow> ext num\<^sub>4 \<Colon> 64 \<sim> hi : 64 - 1 \<sim> lo : 64 - 56\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(Val v with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 \<leftarrow> (ext (num\<^sub>4 \<Colon> 64) \<sim> hi : 8 - 1 \<sim> lo : 0)) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56 \<leftarrow> ext num\<^sub>4 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 8\<close>])
  apply solve_exp
  apply simp
  apply (rule REDUCE[of _ _ \<open>(v[num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>4 \<Colon> 64 \<sim> hi : 7 \<sim> lo : 0, 8]) with [succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u56 \<leftarrow> ext num\<^sub>4 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 8\<close>])
  unfolding succ.simps xtract.simps bv_plus.simps apply simp
  apply solve_exp
  unfolding drop_bit_mask_eq apply simp
  using word8_refl_store_el_word56_in_memI[of \<Delta> v num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r "take_bit 8 num\<^sub>4" "Suc num\<^sub>3 mod 2 ^ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r" "take_bit 56 (drop_bit 8 num\<^sub>4)"]
  unfolding succ.simps bv_plus.simps mod_simps xtract.simps
  apply simp
  unfolding drop_bit_take_bit[of 48 56 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 40 56 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 32 56 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 24 56 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 16 56 \<open>drop_bit 8 num\<^sub>4\<close>] 
            drop_bit_take_bit[of 8 56 \<open>drop_bit 8 num\<^sub>4\<close>]
            drop_bit_drop_bit take_bit_take_bit 
  by simp

lemma word8_refl_store_el_word64_in_memI:
  \<open>\<Delta> \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>4 \<Colon> 64) \<leadsto>* 
      storage64 (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> 8, 8]) num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>4\<close>
  using word8_refl_store_el_word64I by (simp add: storage_constructor_exp_def)

(* TODO - remove? *)
lemma refl_var_inI: \<open>\<Delta>(var :\<^sub>t t \<mapsto> val) \<turnstile> var :\<^sub>t t \<leadsto>* val\<close>
  apply (rule REDUCE[of _ _ \<open>Val val\<close>])
  apply (rule VAR_IN)
  apply (rule var_in_addI)
  by (rule REFL)


(* use raw ML instead *)
method solve_exps = (
  (unfold var_simps)?, (
  rule REFL_WORD | rule REFL_TRUE | rule REFL_FALSE | rule REFL_STORAGE | rule REFL_UNKNOWN | 
  rule REFL | rule refl_var_inI | 

  rule word8_refl_store_el_word64_in_memI | (rule word8_refl_store_el_word64I, blast?) |
  rule word8_refl_store_el_word32_in_memI | (rule word8_refl_store_el_word32I, blast?) |

  (match conclusion in

    \<comment> \<open>Reducible Variables\<close>
    \<open>_ \<turnstile> (_ :\<^sub>t _) \<leadsto>* (num \<Colon> sz)\<close> for num sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(num \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (_ :\<^sub>t _) \<leadsto>* v\<close> for v \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>Val v\<close>]\<close>

    \<comment> \<open>Reducible Pad\<close>
  \<bar> \<open>_ \<turnstile> pad:sz'[num \<Colon> sz] \<leadsto>* (_ \<Colon> _)\<close> for sz' sz num \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>ext num \<Colon> sz \<sim> hi : sz' - 1 \<sim> lo : 0\<close>]\<close>

  \<bar> \<open>_ \<turnstile> extend:sz\<^sub>1[low:sz\<^sub>2[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r]] \<leadsto>* _\<close> for sz\<^sub>1 sz\<^sub>2 num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow>  \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[ext num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<sim> hi : sz\<^sub>2 - 1 \<sim> lo : 0]\<close>]\<close>
  \<bar> \<open>_ \<turnstile> extend:sz\<^sub>1[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] \<leadsto>* _\<close> for sz\<^sub>1 num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow>  \<open>rule REDUCE[of _ _ \<open>exts num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<sim> hi : sz\<^sub>1 - 1 \<sim> lo : 0\<close>]\<close>

   \<comment> \<open>LOAD_BYTE + LOAD_NEXT\<close>
  \<bar> \<open>_ \<turnstile> ((((((_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>8 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz @ (num\<^sub>7 \<Colon> sz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 num\<^sub>8 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((((num\<^sub>8 \<Colon> sz) @ (num\<^sub>7 \<Colon> sz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>8 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz @ (num\<^sub>7 \<Colon> sz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for v num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 num\<^sub>8 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>8 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz) @ (num\<^sub>7 \<Colon> sz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((((e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>7 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((((e @ (num\<^sub>7 \<Colon> sz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>7 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>7 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (((((e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>6 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((e @ (num\<^sub>6 \<Colon> sz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>6 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>6 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>5 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((e @ (num\<^sub>5 \<Colon> sz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>5 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>5 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (((e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((e @ (num\<^sub>4 \<Colon> sz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>3 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((e @ (num\<^sub>3 \<Colon> sz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>3 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>3 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(e @ (num\<^sub>2 \<Colon> sz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>1 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)) @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> e @ (_[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e @ (num\<^sub>1 \<Colon> sz)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz, sz][_ \<Colon> _ \<leftarrow> _ \<Colon> _, _][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz e v en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz, sz][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz)\<close>]\<close>


   \<comment> \<open>LOAD_EL\<close>
  \<bar> \<open>_ \<turnstile> (((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>6 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>5 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>6 num\<^sub>5 num\<^sub>4 num\<^sub>3 num\<^sub>2 num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>6 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>5 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>5 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>5 num\<^sub>4 num\<^sub>3 num\<^sub>2 num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))) @ (num\<^sub>5 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>4 num\<^sub>3 num\<^sub>2 num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))) @ (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> ((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>3 num\<^sub>2 num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))) @ (num\<^sub>3 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>2 num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))) @ (num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close>  for v num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num sz\<^sub>m\<^sub>e\<^sub>m num\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz num\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (v[num\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))) @ (num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>
  \<bar> \<open>_ \<turnstile> v[num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz v \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(v[num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m) @ (v[num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>1 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m)\<close>]\<close>

    \<comment> \<open>Reducible Store\<close>
  \<bar> \<open>_ \<turnstile> v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, _]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m) \<leadsto>* _\<close> for v num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>4 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]\<close>]\<close>
  \<bar> \<open>_ \<turnstile> (v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> low:sz\<^sub>m\<^sub>e\<^sub>m[num\<^sub>4 \<Colon> sz\<^sub>1]) with [num\<^sub>5 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>2 \<leftarrow> num\<^sub>6 \<Colon> sz\<^sub>2 \<leadsto>* _\<close> for v num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>1 sz\<^sub>2 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [num\<^sub>3 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (ext (num\<^sub>4 \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m - 1 \<sim> lo : 0)) with [num\<^sub>5 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>2 \<leftarrow> num\<^sub>6 \<Colon> sz\<^sub>2\<close>]\<close>

  \<bar> \<open>_ \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (low:sz[num\<^sub>1 \<Colon> sz\<^sub>1]) \<leadsto>* _\<close> for e\<^sub>1 e\<^sub>2 en sz num\<^sub>1 sz\<^sub>1 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz - 1 \<sim> lo : 0\<close>]\<close>
  \<bar> \<open>_ \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (high:sz[val \<Colon> sz']) \<leadsto>* _\<close> for e\<^sub>1 e\<^sub>2 en sz val sz' \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [e\<^sub>2, el]:usz \<leftarrow> (ext val \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : sz' - sz)\<close>]\<close>  
, solve_exp) 
  |
  (match conclusion in

    \<comment> \<open>Reducible Bops\<close>
    \<open>\<Delta> \<turnstile> BinOp (var :\<^sub>t t) bop e \<leadsto>* _\<close> for \<Delta> var t bop e \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>BinOp (Val (the (\<Delta> (var :\<^sub>t t)))) bop e\<close>], (solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?)\<close>
  \<bar> \<open>\<Delta> \<turnstile> BinOp (num \<Colon> sz) bop (var :\<^sub>t t) \<leadsto>* _\<close> for \<Delta> num sz var t bop \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>BinOp (num \<Colon> sz) bop (Val (the (\<Delta> (var :\<^sub>t t))))\<close>], (solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?)\<close>

    \<comment> \<open>Reducible Plus\<close>
  \<bar> \<open>\<Delta> \<turnstile> (var :\<^sub>t t) + (num \<Colon> sz) \<leadsto>* _\<close> for \<Delta> var t num sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>Val (the (\<Delta> (var :\<^sub>t t))) + (num \<Colon> sz)\<close>], (solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?)\<close>
  \<bar> \<open>_ \<turnstile> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>], solve_exp, unfold bv_plus.simps\<close>

    \<comment> \<open>Reducible Eq\<close>
  \<bar> \<open>_ \<turnstile> BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>], solve_exp, (unfold bv_eq_def, simp (no_asm))[1]\<close>

  \<bar> \<open>\<Delta> \<turnstile> extend:sz\<^sub>1[mem[(var :\<^sub>t t) + (num \<Colon> sz\<^sub>2), en]:usz\<^sub>3] \<leadsto>* _\<close> for \<Delta> mem var t num sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[mem[Val (the (\<Delta> (var :\<^sub>t t))) + (num \<Colon> sz\<^sub>2), en]:usz\<^sub>3]\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>_ \<turnstile> extend:sz\<^sub>1[mem[(num\<^sub>1 \<Colon> sz\<^sub>2) + (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz\<^sub>3] \<leadsto>* _\<close> for mem num\<^sub>1 num\<^sub>2 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[mem[(num\<^sub>1 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz\<^sub>3]\<close>], solve_exp, unfold bv_plus.simps\<close>
  \<bar> \<open>\<Delta> \<turnstile> extend:sz\<^sub>1[(var :\<^sub>t t)[(num \<Colon> sz\<^sub>2), en]:usz\<^sub>3] \<leadsto>* _\<close> for \<Delta> var t num sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 en \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[Val (the (\<Delta> (var :\<^sub>t t)))[(num \<Colon> sz\<^sub>2), en]:usz\<^sub>3]\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>

  \<bar> \<open>\<Delta> \<turnstile> extend:sz\<^sub>1[low:sz\<^sub>2[(var :\<^sub>t t) + (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)]] \<leadsto>* _\<close> for \<Delta> var t num sz\<^sub>1 sz\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow>  \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[low:sz\<^sub>2[Val (the (\<Delta> (var :\<^sub>t t))) + (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)]]\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>_ \<turnstile> extend:sz\<^sub>1[low:sz\<^sub>2[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) + (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)]] \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 sz\<^sub>1 sz\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow>  \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[low:sz\<^sub>2[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)]]\<close>], solve_exp, unfold bv_plus.simps\<close>

  \<bar> \<open>\<Delta> \<turnstile> extend:sz\<^sub>1[low:sz\<^sub>2[(var :\<^sub>t t)]] \<leadsto>* _\<close> for \<Delta> var t sz\<^sub>1 sz\<^sub>2 \<Rightarrow>  \<open>rule REDUCE[of _ _ \<open>extend:sz\<^sub>1[low:sz\<^sub>2[Val (the (\<Delta> (var :\<^sub>t t)))]]\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>

   \<comment> \<open>LOAD_STEP_ADDR\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1[(var :\<^sub>t t), en]:usz \<leadsto>* _\<close> for \<Delta> e\<^sub>1 var t en sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1[(Val (the (\<Delta> (var :\<^sub>t t)))), en]:usz\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1[(var :\<^sub>t t) + e\<^sub>2, en]:usz \<leadsto>* _\<close> for \<Delta> e\<^sub>1 var t e\<^sub>2 en sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1[(Val (the (\<Delta> (var :\<^sub>t t)))) + e\<^sub>2, en]:usz\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>_ \<turnstile> e\<^sub>1[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) + (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz \<leadsto>* _\<close> for e\<^sub>1 num\<^sub>1 num\<^sub>2 en sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz\<close>], solve_exp, unfold bv_plus.simps\<close>


   \<comment> \<open>LOAD_STEP_MEM\<close>
  \<bar> \<open>\<Delta> \<turnstile> (var :\<^sub>t t)[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz \<leadsto>* _\<close> for \<Delta> var t num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r en sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(Val (the (\<Delta> (var :\<^sub>t t))))[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>

   \<comment> \<open>LOAD_BYTE + LOAD_NEXT\<close>

   \<comment> \<open>LOAD_EL\<close>

    \<comment> \<open>Reducible Store\<close>


  \<bar> \<open>\<Delta> \<turnstile> (var :\<^sub>t t) with [num\<^sub>2 \<Colon> sz\<^sub>2, en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz) \<leadsto>* _\<close> for \<Delta> var t num\<^sub>2 sz\<^sub>2 en sz num\<^sub>3 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(Val (the (\<Delta> (var :\<^sub>t t)))) with [num\<^sub>2 \<Colon> sz\<^sub>2, en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz)\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (var :\<^sub>t t) \<leadsto>* _\<close> for \<Delta> e\<^sub>1 e\<^sub>2 en sz var t \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val (the (\<Delta> (var :\<^sub>t t))))\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1 with [(var :\<^sub>t t), en]:usz \<leftarrow> (num \<Colon> sz) \<leadsto>* _\<close> for \<Delta> e\<^sub>1 var t en num sz \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [(Val (the (\<Delta> (var :\<^sub>t t)))), en]:usz \<leftarrow> (num \<Colon> sz)\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1 with [(var :\<^sub>t t) + (num\<^sub>1 \<Colon> sz\<^sub>1), en]:usz\<^sub>2 \<leftarrow> (num\<^sub>2 \<Colon> sz\<^sub>2) \<leadsto>* _\<close> for \<Delta> e\<^sub>1 var t num\<^sub>1 sz\<^sub>1 en num\<^sub>2 sz\<^sub>2 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [(Val (the (\<Delta> (var :\<^sub>t t)))) + (num\<^sub>1 \<Colon> sz\<^sub>1), en]:usz\<^sub>2 \<leftarrow> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>1 \<Colon> sz\<^sub>1) + (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz\<^sub>3 \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<leadsto>* _\<close> for \<Delta> e\<^sub>1 num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 en num\<^sub>3 sz\<^sub>3 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [(num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz\<^sub>3 \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>], solve_exp, unfold bv_plus.simps, simp del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (low:sz[var :\<^sub>t t]) \<leadsto>* _\<close> for \<Delta> e\<^sub>1 e\<^sub>2 en sz var t \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> low:sz[(Val (the (\<Delta> (var :\<^sub>t t))))]\<close>], solve_exp, rule var_in_val_the_var, assumption?, (unfold in_vars_the_simp)?\<close>

    \<comment> \<open>Reducible Concat\<close>
  \<bar> \<open>_ \<turnstile> (((((((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6)) @ (num\<^sub>7 \<Colon> sz\<^sub>7)) @ (num\<^sub>8 \<Colon> sz\<^sub>8) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 num\<^sub>8 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4 sz\<^sub>5 sz\<^sub>6 sz\<^sub>7 sz\<^sub>8 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6)) @ (num\<^sub>7 \<Colon> sz\<^sub>7)) @ (num\<^sub>8 \<Colon> sz\<^sub>8)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> ((((((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6)) @ (num\<^sub>7 \<Colon> sz\<^sub>7) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 num\<^sub>7 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4 sz\<^sub>5 sz\<^sub>6 sz\<^sub>7 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6)) @ (num\<^sub>7 \<Colon> sz\<^sub>7)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> (((((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 num\<^sub>6 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4 sz\<^sub>5 sz\<^sub>6 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)) @ (num\<^sub>6 \<Colon> sz\<^sub>6)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> ((((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 num\<^sub>5 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4 sz\<^sub>5 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)) @ (num\<^sub>5 \<Colon> sz\<^sub>5)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> (((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 num\<^sub>4 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)) @ (num\<^sub>4 \<Colon> sz\<^sub>4)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 num\<^sub>3 sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) @ (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
  \<bar> \<open>_ \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2) \<leadsto>* _\<close> for num\<^sub>1 num\<^sub>2 sz\<^sub>1 sz\<^sub>2 \<Rightarrow> \<open>rule REDUCE[of _ _ \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>], solve_exp, unfold bv_concat.simps, simp (no_asm) del: dvd_imp_mod_0 mod_less\<close>
)),
  (unfold var_simps)?, solve_exps?  
)

lemmas REFL_STORE_WORD_IN_MEM = refl_store_word_in_memI

end
