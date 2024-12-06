theory Expression_Syntax_Locales
  imports Expression_Syntax
begin

lemma word_is_word':
  assumes \<open>sz' = sz\<close>
    shows \<open>\<exists>num. (num' \<Colon> sz') = (num \<Colon> sz) \<and> (num' \<Colon> sz') = (num \<Colon> sz) \<and> (num' \<Colon> sz') = (num \<Colon> sz)\<close>
  using assms by blast

lemmas word_is_word = word_is_word'[OF refl]

locale uop_is_word =
  fixes bv_fun1 :: \<open>exp \<Rightarrow> exp\<close> 
    and bv_fun2 :: \<open>val \<Rightarrow> val\<close>
    and bv_fun3 :: \<open>word \<Rightarrow> word\<close>
    and sz sz' :: nat
  assumes bv_fun_is_word: \<open>\<And>num\<^sub>1. \<exists>num. (bv_fun1 (num\<^sub>1 \<Colon> sz)) = (num \<Colon> sz') \<and>
                                 (bv_fun2 (num\<^sub>1 \<Colon> sz)) = (num \<Colon> sz') \<and> 
                                 (bv_fun3 (num\<^sub>1 \<Colon> sz)) = (num \<Colon> sz')\<close>
begin

lemma is_word:
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz) \<and> v\<^sub>1 = (num \<Colon> sz) \<and> w\<^sub>1 = (num \<Colon> sz)\<close>
    shows \<open>\<exists>num. (bv_fun1 e\<^sub>1) = (num \<Colon> sz') \<and> (bv_fun2 v\<^sub>1) = (num \<Colon> sz') 
               \<and> (bv_fun3 w\<^sub>1) = (num \<Colon> sz')\<close>
using assms proof clarify
  fix num :: nat
  show "\<exists>numb. bv_fun1 (num \<Colon> sz) = numb \<Colon> sz' \<and> 
               bv_fun2 (num \<Colon> sz) = numb \<Colon> sz' \<and> 
               bv_fun3 (num \<Colon> sz) = numb \<Colon> sz'"
    using bv_fun_is_word by blast
qed

lemma is_valI:
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz) \<and> v\<^sub>1 = (num \<Colon> sz) \<and> w\<^sub>1 = (num \<Colon> sz)\<close>
    shows \<open>(bv_fun1 e\<^sub>1) = Val (bv_fun2 v\<^sub>1)\<close>
  using assms apply auto
  using Val_simp_word bv_fun_is_word by metis

end

locale bop_is_word =
  fixes bv_fun1 :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> 
    and bv_fun2 :: \<open>val \<Rightarrow> val \<Rightarrow> val\<close>
    and bv_fun3 :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close>
    and sz\<^sub>1 sz\<^sub>2 sz' :: nat
  assumes bv_fun_is_word: \<open>\<And>num\<^sub>1 num\<^sub>2. \<exists>num. (bv_fun1 (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)) = (num \<Colon> sz') \<and>
                                 (bv_fun2 (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)) = (num \<Colon> sz') \<and> 
                                 (bv_fun3 (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)) = (num \<Colon> sz')\<close>
begin

lemma is_word:
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num \<Colon> sz\<^sub>1)\<close>
          \<open>\<exists>num. e\<^sub>2 = (num \<Colon> sz\<^sub>2) \<and> v\<^sub>2 = (num \<Colon> sz\<^sub>2) \<and> w\<^sub>2 = (num \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<exists>num. (bv_fun1 e\<^sub>1 e\<^sub>2) = (num \<Colon> sz') \<and> (bv_fun2 v\<^sub>1 v\<^sub>2) = (num \<Colon> sz') 
               \<and> (bv_fun3 w\<^sub>1 w\<^sub>2) = (num \<Colon> sz')\<close>
using assms proof clarify
  fix num numa :: nat
  show "\<exists>numb. bv_fun1 (num \<Colon> sz\<^sub>1) (numa \<Colon> sz\<^sub>2) = numb \<Colon> sz' \<and> 
               bv_fun2 (num \<Colon> sz\<^sub>1) (numa \<Colon> sz\<^sub>2) = numb \<Colon> sz' \<and> 
               bv_fun3 (num \<Colon> sz\<^sub>1) (numa \<Colon> sz\<^sub>2) = numb \<Colon> sz'"
    using bv_fun_is_word by blast
qed

lemma is_valI:
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num \<Colon> sz\<^sub>1)\<close>
      and \<open>\<exists>num. e\<^sub>2 = (num \<Colon> sz\<^sub>2) \<and> v\<^sub>2 = (num \<Colon> sz\<^sub>2) \<and> w\<^sub>2 = (num \<Colon> sz\<^sub>2)\<close>
    shows \<open>(bv_fun1 e\<^sub>1 e\<^sub>2) = Val (bv_fun2 v\<^sub>1 v\<^sub>2)\<close>
  using assms apply auto
  using Val_simp_word bv_fun_is_word by metis

end

interpretation plus: bop_is_word \<open>(+\<^sub>b\<^sub>v)\<close> \<open>(+\<^sub>b\<^sub>v)\<close> \<open>(+\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_plus.simps(1) by metis

interpretation minus: bop_is_word \<open>(-\<^sub>b\<^sub>v)\<close> \<open>(-\<^sub>b\<^sub>v)\<close> \<open>(-\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_minus.simps(1) by metis

interpretation times: bop_is_word \<open>(*\<^sub>b\<^sub>v)\<close> \<open>(*\<^sub>b\<^sub>v)\<close> \<open>(*\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_times.simps(1) by metis

interpretation divide: bop_is_word \<open>(div\<^sub>b\<^sub>v)\<close> \<open>(div\<^sub>b\<^sub>v)\<close> \<open>(div\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_divide.simps(1) by metis

interpretation sdivide: bop_is_word \<open>(div\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(div\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(div\<^sub>s\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_sdivide.simps(1) by metis

interpretation land: bop_is_word \<open>(&\<^sub>b\<^sub>v)\<close> \<open>(&\<^sub>b\<^sub>v)\<close> \<open>(&\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_land.simps(1) by metis

interpretation lor: bop_is_word \<open>(|\<^sub>b\<^sub>v)\<close> \<open>(|\<^sub>b\<^sub>v)\<close> \<open>(|\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_lor.simps(1) by metis

interpretation xor: bop_is_word \<open>(xor\<^sub>b\<^sub>v)\<close> \<open>(xor\<^sub>b\<^sub>v)\<close> \<open>(xor\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_xor.simps(1) by metis

interpretation mod: bop_is_word \<open>(%\<^sub>b\<^sub>v)\<close> \<open>(%\<^sub>b\<^sub>v)\<close> \<open>(%\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_mod\<^sub>b\<^sub>v.simps(1) by metis

interpretation smod: bop_is_word \<open>(%\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(%\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(%\<^sub>s\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_smod.simps(1) by metis

interpretation lsl: bop_is_word \<open>(<<\<^sub>b\<^sub>v)\<close> \<open>(<<\<^sub>b\<^sub>v)\<close> \<open>(<<\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_lsl.simps(1) by metis

interpretation lsr: bop_is_word \<open>(>>\<^sub>b\<^sub>v)\<close> \<open>(>>\<^sub>b\<^sub>v)\<close> \<open>(>>\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_lsr.simps(1) by metis

interpretation asr: bop_is_word \<open>(>>>\<^sub>b\<^sub>v)\<close> \<open>(>>>\<^sub>b\<^sub>v)\<close> \<open>(>>>\<^sub>b\<^sub>v)\<close> sz sz sz
  apply (unfold_locales)
  unfolding bv_asr.simps(1) by metis

interpretation lt: bop_is_word \<open>(<\<^sub>b\<^sub>v)\<close> \<open>(<\<^sub>b\<^sub>v)\<close> \<open>(<\<^sub>b\<^sub>v)\<close> sz sz \<open>Suc 0\<close>
  apply (unfold_locales)
  using bv_lt.simps(1) by metis

interpretation slt: bop_is_word \<open>(<\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(<\<^sub>s\<^sub>b\<^sub>v)\<close> \<open>(<\<^sub>s\<^sub>b\<^sub>v)\<close> sz sz \<open>Suc 0\<close>
  apply (unfold_locales)
  using bv_slt.simps(1) by metis

interpretation concat: bop_is_word \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> sz\<^sub>1 sz\<^sub>2 \<open>sz\<^sub>1 + sz\<^sub>2\<close>
  apply (unfold_locales)
  unfolding bv_concat.simps(1) by metis

lemma eq_is_word:
  fixes e :: exp
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz) \<and> v\<^sub>1 = (num \<Colon> sz) \<and> w\<^sub>1 = (num \<Colon> sz)\<close>
      and \<open>\<exists>num. e\<^sub>2 = (num \<Colon> sz) \<and> v\<^sub>2 = (num \<Colon> sz) \<and> w\<^sub>2 = (num \<Colon> sz)\<close>
    shows \<open>\<exists>num. (e\<^sub>1 =\<^sub>b\<^sub>v e\<^sub>2) = (num \<Colon> Suc 0) \<and> (v\<^sub>1 =\<^sub>b\<^sub>v v\<^sub>2) = (num \<Colon> Suc 0) \<and> (w\<^sub>1 =\<^sub>b\<^sub>v w\<^sub>2) = (num \<Colon> Suc 0)\<close>
  using assms unfolding bv_eq_def by auto

interpretation succ: uop_is_word succ succ succ sz sz
  apply (unfold_locales)
  using succ.simps(1) plus.is_word word_is_word
  by (smt (verit, ccfv_threshold) plus.bv_fun_is_word)

interpretation not: uop_is_word bv_negation bv_negation bv_negation sz sz
  apply (unfold_locales)
  using bv_negation.simps(1) by metis

interpretation neg: uop_is_word bv_uminus bv_uminus bv_uminus sz sz
  apply (unfold_locales)
  using bv_uminus.simps(1) by metis

lemma xtract_is_word': 
  assumes \<open>Suc (sz\<^sub>1 - sz\<^sub>2) = sz\<close>
      and \<open>\<exists>num. e = (num \<Colon> sz') \<and> v = (num \<Colon> sz') \<and> w = (num \<Colon> sz')\<close>
    shows \<open>\<exists>num. (ext e \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> sz) \<and>
                 (ext v \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> sz) \<and> 
                 (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> sz)\<close>
  using assms apply auto
  unfolding xtract.simps by auto

lemmas xtract_is_word = xtract_is_word'[OF refl]
lemma xtract_is_wordv: 
  assumes \<open>\<exists>num. e = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2)) \<and> v = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2)) \<and> w = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2))\<close>
    shows \<open>\<exists>num. (ext e \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2)) \<and>
                 (ext v \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2)) \<and> 
                 (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = (num \<Colon> Suc (sz\<^sub>1 - sz\<^sub>2))\<close>
  using assms by (rule xtract_is_word)

lemma capture_avoid_is_word:
  fixes e :: exp and v :: val and w :: word
  assumes \<open>\<exists>num. e = (num \<Colon> sz) \<and> v = (num \<Colon> sz) \<and> w = (num \<Colon> sz)\<close> 
    shows \<open>\<exists>num. ([v\<sslash>(nm :\<^sub>t t)](nm :\<^sub>t t)) = (num \<Colon> sz) \<and> v = (num \<Colon> sz) \<and> 
                 w = (num \<Colon> sz)\<close>
  using assms apply (elim exE conjE, clarify)
  using Val_simp_word by force

method solve_is_wordI = 
  (rule word_is_word) |
  (rule xtract_is_word', linarith, solve_is_wordI) |
  (rule plus.is_word minus.is_word times.is_word divide.is_word
        sdivide.is_word land.is_word lor.is_word xor.is_word mod.is_word smod.is_word lsl.is_word 
        lsr.is_word asr.is_word lt.is_word slt.is_word eq_is_word concat.is_word, 
     solve_is_wordI, solve_is_wordI) |
  (rule succ.is_word not.is_word neg.is_word xtract_is_word capture_avoid_is_word 
        eq_is_word, 
     solve_is_wordI)

locale exp_val_word_fixed_sz_is_ok_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close> and sz :: nat
  assumes word_is_ok: \<open>\<And>num. num < 2 ^ sz \<Longrightarrow> PROP P (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) sz\<close>
begin

lemma mod_nat_pow2_lt:
  fixes x :: nat
    shows \<open>x mod 2 ^ sz < 2 ^ sz\<close>
  using take_bit_eq_mod take_bit_nat_less_exp by fastforce


lemma plus: \<open>PROP P ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_plus.simps by (intro mod_nat_pow2_lt word_is_ok)

lemma succ: \<open>PROP P (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) sz\<close> 
  unfolding succ.simps by (rule plus)
(*
lemma minus: \<open>num\<^sub>1 < 2 ^ sz \<Longrightarrow> PROP P ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_minus.simps 
  apply (rule word_is_ok)
  by (cases \<open>num\<^sub>1 < num\<^sub>2\<close>,auto)
*)
lemma lsl: \<open>PROP P ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) sz\<close>
  unfolding bv_lsl.simps by (intro mod_nat_pow2_lt word_is_ok)
(*
lemma lsr: \<open>num\<^sub>1 < 2 ^ sz \<Longrightarrow> PROP P ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) sz\<close>
  unfolding bv_lsr.simps apply (intro mod_nat_pow2_lt word_is_ok)
  using div_le_dividend order.strict_trans1 by blast

lemma land: \<open>PROP P ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_land.simps by (intro mod_nat_pow2_lt word_is_ok)

lemma lor: \<open>PROP P ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_lor.simps by (intro mod_nat_pow2_lt word_is_ok)
*)
lemma true_sz:
  assumes sz: \<open>sz = Suc 0\<close> 
    shows \<open>PROP P true true true (Suc 0)\<close>
  unfolding true_word apply (intro word_is_ok[unfolded sz])
  by simp

lemma false_sz:
  assumes sz: \<open>sz = Suc 0\<close> 
    shows \<open>PROP P false false false (Suc 0)\<close>
  unfolding false_word apply (intro word_is_ok[unfolded sz])
  by simp

lemma leq_sz: 
  assumes sz: \<open>sz = Suc 0\<close> 
    shows \<open>PROP P ((num\<^sub>1 \<Colon> sz') \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz') \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz') \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) (Suc 0)\<close>
  unfolding bv_leq_true_or_false apply (intro word_is_ok[unfolded sz])
  by simp

lemma lt_sz: 
  assumes sz: \<open>sz = Suc 0\<close> 
    shows \<open>PROP P ((num\<^sub>1 \<Colon> sz') <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz') <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz') <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) (Suc 0)\<close>
  unfolding bv_lt_true_or_false apply (intro word_is_ok[unfolded sz])
  by simp

lemma xtract_sz:
  assumes sz: \<open>sz = Suc (sz\<^sub>1 - sz\<^sub>2)\<close> 
    shows \<open>PROP P (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (Suc (sz\<^sub>1 - sz\<^sub>2))\<close> 
  unfolding xtract.simps apply (intro word_is_ok[unfolded sz])
  using take_bit_nat_less_exp by blast

lemma xtract_full: \<open>sz > 0 \<Longrightarrow> PROP P (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0) (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0) (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0) sz\<close> 
  unfolding xtract.simps apply simp
  by (intro word_is_ok take_bit_nat_less_exp)

(* TODO are these uglies needed? *)
(*
lemma succ_plus: \<open>PROP P (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) sz\<close>
  unfolding bv_plus.simps succ.simps by (rule word_is_ok)

lemma xtract2_sz: 
  assumes sz: \<open>sz = sz\<^sub>3 - sz\<^sub>4 + (Suc 0)\<close> 
    shows \<open>PROP P (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (sz\<^sub>3 - sz\<^sub>4 + 1)\<close> 
  unfolding xtract.simps by (rule word_is_ok[unfolded sz])

lemma xtract_plus_sz: 
  assumes sz: \<open>sz = sz\<^sub>1 - sz\<^sub>2 + (Suc 0)\<close> 
    shows \<open>PROP P (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (Suc (sz\<^sub>1 - sz\<^sub>2))\<close> 
  unfolding xtract.simps bv_plus.simps by (rule word[unfolded sz])

lemma xtract2_plus_sz: 
  assumes sz: \<open>sz = sz\<^sub>3 - sz\<^sub>4 + (Suc 0)\<close> 
    shows \<open>PROP P (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (sz\<^sub>3 - sz\<^sub>4 + 1)\<close> 
  unfolding xtract.simps bv_plus.simps  by (rule word[unfolded sz])
(* TODO *)
*)

end

locale exp_val_word_fixed_sz_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close> and sz :: nat
  assumes is_sz_word: \<open>\<exists>num. e = (num \<Colon> sz) \<and> v = (num \<Colon> sz) \<and> w = (num \<Colon> sz) \<Longrightarrow> PROP P e v w sz\<close>
begin

lemma word: \<open>PROP P (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) sz\<close> 
  by (intro is_sz_word word_is_word)

sublocale exp_val_word_fixed_sz_is_ok_syntax
  apply standard apply (rule word)
  done

lemma minus: \<open>PROP P ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_minus.simps 
  apply (rule is_sz_word)
  by (cases \<open>num\<^sub>1 < num\<^sub>2\<close>,auto)

lemma lsr: \<open>PROP P ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) sz\<close>
  unfolding bv_lsr.simps apply (intro mod_nat_pow2_lt is_sz_word)
  using div_le_dividend order.strict_trans1 by blast

lemma land: \<open>PROP P ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_land.simps apply (intro mod_nat_pow2_lt is_sz_word)
  by blast

lemma lor: \<open>PROP P ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_lor.simps apply (intro mod_nat_pow2_lt is_sz_word)
  by blast

lemma xor: \<open>PROP P ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_xor.simps apply (intro mod_nat_pow2_lt is_sz_word)
  by blast


(* TODO are these uglies needed? *)

lemma succ_plus: \<open>PROP P (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) (succ ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))) sz\<close>
  unfolding bv_plus.simps succ.simps by (rule word)

lemma xtract2_sz: 
  assumes sz: \<open>sz = Suc (sz\<^sub>3 - sz\<^sub>4)\<close> 
    shows \<open>PROP P (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz') \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (Suc (sz\<^sub>3 - sz\<^sub>4))\<close> 
  unfolding xtract.simps by (rule word[unfolded sz])

lemma xtract_plus_sz: 
  assumes sz: \<open>sz = Suc (sz\<^sub>1 - sz\<^sub>2)\<close> 
    shows \<open>PROP P (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (Suc (sz\<^sub>1 - sz\<^sub>2))\<close> 
  unfolding xtract.simps bv_plus.simps by (rule word[unfolded sz])

lemma xtract2_plus_sz: 
  assumes sz: \<open>sz = Suc (sz\<^sub>3 - sz\<^sub>4)\<close> 
    shows \<open>PROP P (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext ((num\<^sub>1 \<Colon> sz') +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz')) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (Suc (sz\<^sub>3 - sz\<^sub>4))\<close> 
  unfolding xtract.simps bv_plus.simps  by (rule word[unfolded sz])

end





locale exp_val_word_sz_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes is_word: \<open>\<And>sz. \<exists>num. e = (num \<Colon> sz) \<and> v = (num \<Colon> sz) \<and> w = (num \<Colon> sz) \<Longrightarrow> PROP P e v w sz\<close>
begin

sublocale exp_val_word_fixed_sz_syntax
  by standard (rule is_word)

lemmas true = true_sz[OF refl]
lemmas false = false_sz[OF refl]
lemmas leq = leq_sz[OF refl]
lemmas lt = lt_sz[OF refl]
lemmas xtract = xtract_sz[OF refl]

(* TODO Uglies *)
lemmas xtract2 = xtract2_sz[OF refl]
lemmas xtract_plus = xtract_plus_sz[OF refl]
lemmas xtract2_plus = xtract2_plus_sz[OF refl]

end

locale exp_val_is_imm_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val_imm': \<open>\<And>v sz e. e = (Val v) \<Longrightarrow> type v = imm\<langle>sz\<rangle> \<Longrightarrow> PROP P e v sz\<close>
begin

lemma val_imm: \<open>type v = imm\<langle>sz\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<close>
  by (intro refl val_imm')

sublocale exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v _ sz. P e v sz\<close>
  apply standard
  unfolding word_constructor_exp_def 
  apply (rule val_imm')
  apply blast
  by force

lemma unknown_imm: \<open>PROP P (unknown[str]: imm\<langle>sz\<rangle>) (unknown[str]: imm\<langle>sz\<rangle>) sz\<close>
  unfolding unknown_constructor_exp_def 
  apply (rule val_imm)
  by (rule type_unknownI)

lemmas word_syntaxs = word true false unknown_imm

end

locale exp_val_storage_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val_mem: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

lemma storage: \<open>PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding storage_constructor_exp_def
  by (rule val_mem)

lemma unknown: \<open>PROP P (unknown[str]: t) (unknown[str]: t) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding unknown_constructor_exp_def 
  by (rule val_mem)

lemmas storage_syntaxs = storage unknown

end

locale exp_val_is_mem_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val_mem: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

lemma storage: \<open>PROP P (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding storage_constructor_exp_def
  apply (rule val_mem)
  by (rule type_storageI)

lemma storage_addr: \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding storage_constructor_exp_def
  apply (rule val_mem)
  by (rule type_storage_addrI)

lemma unknown_mem: \<open>PROP P (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding unknown_constructor_exp_def 
  apply (rule val_mem)
  by (rule type_unknownI)

lemmas storage_syntaxs = storage unknown_mem storage_addr

end
(*
lemma succ_is_valI':
  fixes e :: exp
  assumes \<open>w\<^sub>v = (num \<Colon> sz)\<close> and \<open>e' = (Val w\<^sub>v)\<close>
    shows \<open>succ e' = Val (succ w\<^sub>v)\<close>
  using assms by (metis succ.is_word word_constructor_exp_def)
*)

(* Can these be generated via a locale? *)
lemma eq_is_valI:
  fixes e :: exp
  assumes \<open>\<exists>num. e\<^sub>1 = (num \<Colon> sz) \<and> v\<^sub>1 = (num \<Colon> sz) \<and> w\<^sub>1 = (num \<Colon> sz)\<close>
      and \<open>\<exists>num. e\<^sub>2 = (num \<Colon> sz) \<and> v\<^sub>2 = (num \<Colon> sz) \<and> w\<^sub>2 = (num \<Colon> sz)\<close>
    shows \<open>(e\<^sub>1 =\<^sub>b\<^sub>v e\<^sub>2) = Val (v\<^sub>1 =\<^sub>b\<^sub>v v\<^sub>2)\<close>
  using assms unfolding bv_eq_def sketch safe
proof safe
  fix num numa
  show "(if (num \<Colon> sz::exp) = numa \<Colon> sz then true else false) = Val (if (num \<Colon> sz::val) = numa \<Colon> sz then true else false)"
    by (cases \<open>num \<Colon> sz = numa \<Colon> sz\<close>, auto simp add: true_word false_word word_constructor_exp_def)
qed

lemma xtract_is_valI:
  assumes \<open>\<exists>num. e = (num \<Colon> sz) \<and> v = (num \<Colon> sz) \<and> w = (num \<Colon> sz)\<close>
    shows \<open>(ext e \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) = Val (ext v \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o)\<close>
  using assms by (metis bv_simps(51) word_constructor_exp_def)

lemmas Val_refl = refl[where t = \<open>Val _\<close>]

method solve_is_valI uses add
  \<open>Solve and optimise goals of the form ?e = Val ?v\<close> = ((unfold add)?,
  (rule word_constructor_exp_def storage_constructor_exp_def unknown_constructor_exp_def) |
  (rule plus.is_valI minus.is_valI times.is_valI
        divide.is_valI sdivide.is_valI land.is_valI lor.is_valI xor.is_valI mod.is_valI smod.is_valI 
        lsl.is_valI lsr.is_valI asr.is_valI lt.is_valI slt.is_valI eq_is_valI concat.is_valI, 
     solve_is_wordI, solve_is_wordI) |
  (rule succ.is_valI not.is_valI neg.is_valI xtract_is_valI,
    solve_is_wordI) |
  (rule Val_refl ) \<comment> \<open>Last case\<close>
)

locale exp_val_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes is_val: \<open>\<And>e v. e = (Val v) \<Longrightarrow> PROP P e v\<close>
begin

lemma val: \<open>PROP P (Val v) v\<close>
  by (intro is_val refl)

sublocale exp_val_is_imm_syntax
  where P = \<open>\<lambda>e v _. P e v\<close>
  apply standard
  unfolding word_constructor_exp_def by (rule is_val)

sublocale exp_val_storage_syntax
  where P = \<open>\<lambda>e v _ _. P e v\<close>
  apply standard
  unfolding storage_constructor_exp_def by (rule val)

end






















locale exp_val_word_fixed_sz_syntax2 =
    fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close> and sz\<^sub>1 sz\<^sub>2 :: nat
  assumes is_word2: \<open>\<lbrakk>
     \<exists>num\<^sub>1. e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1);
     \<exists>num\<^sub>2. e\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2) \<and> v\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2) \<and> w\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2)
   \<rbrakk> \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2\<close>
begin

sublocale is_word: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. (e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e v w sz')\<close> 
    and sz = sz\<^sub>2
  apply (standard)
  by (rule is_word2, auto)

sublocale word: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) sz\<^sub>1 e v w sz'\<close> 
    and sz = sz\<^sub>2
  apply (standard)
  by (rule is_word.is_sz_word, auto)

sublocale plus: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_plus.simps by (rule word.is_sz_word, auto)

sublocale succ: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close> 
    and sz = sz\<^sub>2
  apply (standard)
  unfolding succ.simps by (rule plus.is_sz_word, auto)

sublocale minus: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_minus.simps by (rule word.is_sz_word, auto)

sublocale lsl: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_lsl.simps by (rule word.is_sz_word, auto)

sublocale lsr: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_lsr.simps by (rule word.is_sz_word, auto)

sublocale land: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_land.simps by (rule word.is_sz_word, auto)

sublocale lor: exp_val_word_fixed_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_lor.simps by (rule word.is_sz_word, auto)

end

locale exp_val_word_fixed_sz_syntax_is_ok2 =
    fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close> and sz\<^sub>1 sz\<^sub>2 :: nat
  assumes word2_sz: \<open>\<And>num\<^sub>1 num\<^sub>2. \<lbrakk>num\<^sub>1 < 2 ^ sz\<^sub>1; num\<^sub>2 < 2 ^ sz\<^sub>2
   \<rbrakk> \<Longrightarrow> PROP P (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>1 \<Colon> sz\<^sub>1) sz\<^sub>1 (num\<^sub>2 \<Colon> sz\<^sub>2) (num\<^sub>2 \<Colon> sz\<^sub>2) (num\<^sub>2 \<Colon> sz\<^sub>2) sz\<^sub>2\<close>
begin

sublocale word: exp_val_word_fixed_sz_is_ok_syntax
  where P = \<open>\<lambda>e v w sz'. (num < 2 ^ sz\<^sub>1 \<Longrightarrow> PROP P (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) sz\<^sub>1 e v w sz')\<close> 
    and sz = sz\<^sub>2
  apply (standard)
  unfolding succ.simps bv_plus.simps apply (rule word2_sz) oops

sublocale succ: exp_val_word_fixed_sz_is_ok_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close> 
    and sz = sz\<^sub>2
  apply (standard)
  unfolding succ.simps bv_plus.simps apply (rule word2_sz)
  by simp

sublocale plus: exp_val_word_fixed_sz_is_ok_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
    and sz = sz\<^sub>2
  apply (standard)
  unfolding bv_plus.simps apply (rule word2_sz)
  by simp
end


locale exp2_val_word_sz_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes is_word2: \<open>\<And>sz\<^sub>1 sz\<^sub>2. \<lbrakk>
     \<exists>num\<^sub>1. e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1);
     \<exists>num\<^sub>2. e\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2) \<and> v\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2) \<and> w\<^sub>2 = (num\<^sub>2 \<Colon> sz\<^sub>2)
   \<rbrakk> \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2\<close>
begin

sublocale is_word: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. (\<exists>num\<^sub>1. e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e v w sz')\<close> 
  apply (standard)
  by (rule is_word2, auto)

sublocale word: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) sz\<^sub>1 e v w sz'\<close> 
  apply (standard)
  apply (rule is_word.is_word)
  by auto

sublocale plus: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close>
  apply (standard)
  unfolding bv_plus.simps by (rule word.is_word)

sublocale succ: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) sz\<^sub>1 e v w sz'\<close> 
  apply (standard)
  unfolding succ.simps by (rule plus.is_word)


sublocale xtract: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (Suc (sz\<^sub>1 - sz\<^sub>2)) e v w sz'\<close>
  apply (standard)
  unfolding xtract.simps by (rule word.is_word)

sublocale leq: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e v w sz'. P ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) (Suc 0) e v w sz'\<close>
  apply (standard)
  unfolding bv_leq_true_or_false by (rule word.is_word)

end

locale exp_val2_word_sz1_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes is_word2: \<open>\<And>sz\<^sub>1. \<lbrakk>\<exists>num\<^sub>1. e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1); 
     e\<^sub>2 = (Val v\<^sub>2)
   \<rbrakk> \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2\<close>
begin

sublocale is_word: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<exists>num\<^sub>1. e\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> v\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> w\<^sub>1 = (num\<^sub>1 \<Colon> sz\<^sub>1) \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e v)\<close> 
  apply (standard)
  by (rule is_word2, auto)

sublocale word: exp_val_syntax
  where P = \<open>\<lambda>e v. P (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) (num \<Colon> sz\<^sub>1) sz\<^sub>1 e v\<close> 
  apply (standard)
  apply (rule is_word.is_val)
  by auto

sublocale plus: exp_val_syntax
  where P = \<open>\<lambda>e v. P ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) ((num\<^sub>1 \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>1)) sz\<^sub>1 e v\<close>
  apply (standard)
  unfolding bv_plus.simps by (rule word.is_val)

sublocale succ: exp_val_syntax
  where P = \<open>\<lambda>e v. P (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) (succ (num \<Colon> sz\<^sub>1)) sz\<^sub>1 e v\<close> 
  apply (standard)
  unfolding succ.simps by (rule plus.is_val)

sublocale xtract: exp_val_syntax
  where P = \<open>\<lambda>e v. P (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (Suc (sz\<^sub>1 - sz\<^sub>2)) e v\<close>
  apply (standard)
  unfolding xtract.simps by (rule word.is_val)

sublocale leq: exp_val_syntax
  where P = \<open>\<lambda>e v. P ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) (Suc 0) e v\<close>
  apply (standard)
  unfolding bv_leq_true_or_false by (rule word.is_val)

end




























locale exp2_storage_val_syntax =
  fixes P2 :: \<open>exp \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes is_storage_val2: \<open>\<And>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = (Val v\<^sub>1); e\<^sub>2 = (Val v\<^sub>2)\<rbrakk> \<Longrightarrow> PROP P2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

sublocale val: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. type v' = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P2 (Val v') e v' v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply standard
  apply (rule is_storage_val2)
  by auto

sublocale storage_addr: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' w sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'' sz. type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P2 (v'[w \<leftarrow> v'', sz]) e (v'[w \<leftarrow> v'', sz]) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)\<close>
  unfolding storage_constructor_exp_def by (standard, intro val.is_val type_storage_addrI)

sublocale storage: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'' sz. PROP P2 (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) e (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)\<close>
  unfolding storage_constructor_exp_def by (standard, intro val.is_val type_storageI)

sublocale unknown: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. PROP P2 (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) e (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  unfolding unknown_constructor_exp_def by (standard, intro val.is_val type_unknownI)

(*
lemmas storage_syntaxs2 = storage.syntaxs unknown.syntaxs val.syntaxs
*)

end

locale exp2_val_syntax =
  fixes P2 :: \<open>exp \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes is_val2: \<open>\<And>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2. \<lbrakk>e\<^sub>1 = (Val v\<^sub>1); e\<^sub>2 = (Val v\<^sub>2)\<rbrakk> \<Longrightarrow> PROP P2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2\<close>
begin

sublocale val: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v'. PROP P2 (Val v') e v' v)\<close>
  by (standard, intro refl is_val2)

sublocale word: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP P2 (num \<Colon> sz) e (num \<Colon> sz) v)\<close>
  unfolding word_constructor_exp_def by (standard, rule val.is_val)

sublocale true: exp_val_syntax
  where P = \<open>\<lambda>e v. PROP P2 true e true v\<close>
  unfolding true_word word_constructor_exp_def by (standard, rule val.is_val)

sublocale false: exp_val_syntax
  where P = \<open>\<lambda>e v. PROP P2 false e false v\<close>
  unfolding false_word word_constructor_exp_def by (standard, rule val.is_val)

sublocale storage: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'' sz. PROP P2 (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) e (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) v)\<close>
  unfolding storage_constructor_exp_def by (standard, rule val.is_val)

sublocale unknown: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>str t. PROP P2 (unknown[str]: t) e (unknown[str]: t) v)\<close>
  unfolding unknown_constructor_exp_def by (standard, rule val.is_val)

sublocale xtract: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz sz\<^sub>1 sz\<^sub>2. PROP P2 (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) e (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) v)\<close>
  unfolding xtract.simps by (standard, rule word.is_val)

sublocale xtract2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4. PROP P2 (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) e (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) v)\<close> 
  unfolding xtract.simps by (standard, rule word.is_val)

sublocale succ: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (num \<Colon> sz)) e (succ (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.is_val)

sublocale plus: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num\<^sub>1 num\<^sub>2 sz. PROP (P2 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) e ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) v))\<close>
  apply standard unfolding bv_plus.simps
  by (rule word.is_val)

sublocale leq: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num\<^sub>1 num\<^sub>2 sz. PROP (P2 ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) e ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) v))\<close>
  apply standard
  unfolding bv_leq_true_or_false by (rule word.is_val)

end


(* can be replaced by 
locale word_exp_val_syntax =
  fixes PW :: \<open>('a::word_constructor) \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes wordPW: \<open>\<And>num sz v. PROP PW (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) (Val v) v\<close>
begin

sublocale word: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) e v))\<close>
  by (standard, rule wordPW)

sublocale plus: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num\<^sub>1 num\<^sub>2 sz. PROP (PW ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) e v))\<close>
  apply standard unfolding bv_plus.simps
  by (rule word.val)

sublocale succ: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)



(*
lemmas syntaxs = word.syntaxs succ.syntaxs succ2.syntaxs succ3.syntaxs succ4.syntaxs succ5.syntaxs
                 succ6.syntaxs succ7.syntaxs
*)

end
*)







locale load_multiple_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> prop\<close>
  assumes val_is_word: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e. \<lbrakk>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<exists>num. e = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<rbrakk> \<Longrightarrow> PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<close>
begin

sublocale storage: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' num sz\<^sub>m\<^sub>e\<^sub>m. PROP P (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (intro val_is_word type_storageI)
  by auto
 
sublocale storage_addr: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' w sz\<^sub>m\<^sub>e\<^sub>m. type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (intro val_is_word type_storage_addrI)
  by auto

sublocale unknown: exp_val_word_sz_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>str sz\<^sub>m\<^sub>e\<^sub>m. PROP P (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding unknown_constructor_exp_def 
  apply (intro val_is_word type_unknownI)
  by auto

end

locale store_multiple_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes is_val3: \<open>\<And>e\<^sub>1 v\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = (Val v\<^sub>1);
      \<exists>num. e\<^sub>2 = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<and> v\<^sub>2 = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<and> w\<^sub>2 = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r); e\<^sub>3 = (Val v\<^sub>3)\<rbrakk>
        \<Longrightarrow> PROP P e\<^sub>1 v\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

lemma store_val: (* legacy *)
  assumes \<open>type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>e\<^sub>1 = (Val v\<^sub>1)\<close>
      and \<open>e\<^sub>3 = (Val v\<^sub>3)\<close>
    shows \<open>PROP P e\<^sub>1 v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) e\<^sub>3 v\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  using assms by (intro is_val3 word_is_word)

sublocale word: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def by (rule store_val)

sublocale plus: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num\<^sub>1 num\<^sub>2. PROP P e\<^sub>1 v\<^sub>1 ((num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) ((num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) ((num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def bv_plus.simps by (rule store_val)

sublocale succ: exp2_storage_val_syntax
  where P2 = \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>num. PROP P e\<^sub>1 v\<^sub>1 (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) e\<^sub>2 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m )\<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule store_val)

end

locale store_gt8_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> prop\<close> and sz\<^sub>v\<^sub>a\<^sub>l :: nat
  assumes is_word_val2: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 w\<^sub>1 e\<^sub>2 v\<^sub>2. \<lbrakk>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>;
    \<exists>num\<^sub>1. e\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<and> w\<^sub>1 = num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
    \<exists>num\<^sub>2. e\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>v\<^sub>a\<^sub>l \<and> v\<^sub>2 = num\<^sub>2 \<Colon> sz\<^sub>v\<^sub>a\<^sub>l\<rbrakk> \<Longrightarrow>
        PROP P (Val v) v e\<^sub>1 w\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>2 v\<^sub>2\<close>
begin

sublocale val: exp_val_word_fixed_sz_syntax2
  where P = \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 _ sz\<^sub>2. (\<And>v. type v = mem\<langle>sz\<^sub>1, 8\<rangle> \<Longrightarrow> PROP P (Val v) v e\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2)\<close>
    and sz\<^sub>2 = sz\<^sub>v\<^sub>a\<^sub>l
  apply (standard)
  by (rule is_word_val2, auto)


sublocale storage: exp_val_word_fixed_sz_syntax2
  where P = \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 _ sz\<^sub>2. (\<And>num v v'. PROP P (v[(num \<Colon> sz\<^sub>1) \<leftarrow> v', 8]) (v[(num \<Colon> sz\<^sub>1) \<leftarrow> v', 8]) e\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2)\<close>
    and sz\<^sub>2 = sz\<^sub>v\<^sub>a\<^sub>l
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (intro is_word_val2 type_storageI)
  by auto

sublocale storage_addr: exp_val_word_fixed_sz_syntax2
  where P = \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 _ sz\<^sub>2. (\<And>w v v'. type w = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', 8]) (v[w \<leftarrow> v', 8]) e\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2)\<close>
    and sz\<^sub>2 = sz\<^sub>v\<^sub>a\<^sub>l
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (intro is_word_val2 type_storage_addrI)
  by auto

sublocale unknown: exp_val_word_fixed_sz_syntax2
  where P = \<open>\<lambda>e\<^sub>1 _ w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 _ sz\<^sub>2. (\<And>str. PROP P (unknown[str]: mem\<langle>sz\<^sub>1, 8\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>1, 8\<rangle>) e\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2)\<close>
    and sz\<^sub>2 = sz\<^sub>v\<^sub>a\<^sub>l
  apply (standard)
  unfolding unknown_constructor_exp_def
  apply (intro is_word_val2 type_unknownI)
  by auto

end

interpretation capture_avoid: exp_val_syntax \<open>\<lambda>e _. (\<And>val var. [val\<sslash>var]e = e)\<close>
  by (standard, simp)

end
