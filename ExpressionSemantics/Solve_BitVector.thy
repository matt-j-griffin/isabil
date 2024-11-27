theory Solve_BitVector
  imports Expression_Syntax_Locales
          "HOL-Eisbach.Eisbach_Tools"
begin


(* TODO move *)

lemmas solve_exp_simpset = (*mod_mod_trivial*) mod_Suc_eq not_dvd_plus_mod_neq not_dvd_Suc_Suc_mod_neq 
  not_dvd_Suc_mod_neq plus_mod_neq mod_Suc_neq
  plus_Suc_right_mod_neq plus_Suc_left_mod_neq 
  plus_Suc_Suc_right_mod_neq plus_Suc_Suc_left_mod_neq

lemma power_le_min: fixes x n N :: nat assumes \<open>n \<le> N\<close> and \<open>x < 2 ^ n\<close> shows \<open>x < 2 ^ N\<close>
  using assms order_less_le_trans by fastforce

lemma power_lt_min: fixes x n N :: nat assumes \<open>n < N\<close> and \<open>x < 2 ^ (Suc n)\<close> shows \<open>x < 2 ^ N\<close>
  using Suc_leI assms power_le_min by blast


interpretation succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 0 \<Longrightarrow> succ w \<noteq> w)\<close>
  apply standard
  apply auto
  by (simp add: solve_exp_simpset succ.simps bv_plus.simps)

interpretation succ2_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ w) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  
  apply (rule not_dvd_Suc_Suc_mod_neq)
  apply simp_all 
  by (metis less_exp not_less_eq numeral_2_eq_2)

interpretation succ2_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 0 \<Longrightarrow> succ (succ w) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ_neqI.succ)

interpretation succ3_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ w)) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 apply (rule mod_between_neq')
  apply auto
  by (metis Suc_lessI Suc_mask_eq_exp less_mask not_less_eq numeral_3_eq_3 order_less_trans)

interpretation succ3_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ w)) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ2_neqI.succ, simp)

interpretation succ4_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ w))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ4_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 1 \<Longrightarrow> succ (succ (succ (succ w))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ3_neqI.succ, simp)

interpretation succ5_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ w)))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ5_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ w)))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ4_neqI.succ, simp)

interpretation succ6_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ w))))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ6_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ w))))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ5_neqI.succ, simp)

interpretation succ7_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ (succ w)))))) \<noteq> w)\<close>
  apply (standard, elim exE)
  apply (simp add: solve_exp_simpset succ.simps bv_plus.simps)
  unfolding Suc3_eq_add_3 unfolding Suc_eq_plus1_left apply simp 
  apply (rule mod_between_neq')
  by (rule power_lt_min, auto)

interpretation succ7_succ_neqI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>_ _ w sz. (sz > 2 \<Longrightarrow> succ (succ (succ (succ (succ (succ (succ w)))))) \<noteq> succ w)\<close>
  by (standard, elim exE, simp, rule succ6_neqI.succ, simp)

lemma succ_lt_neqI:
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>num\<^sub>2 < 2 ^ sz\<^sub>2\<close> and \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq> num\<^sub>2 \<Colon> sz\<^sub>2\<close>
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding succ.simps bv_plus.simps apply auto
  using assms mod_lt_neqI Suc_mod_neq by force

interpretation succ_lt_neqI: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>_ _ w\<^sub>1 _ _ _ w\<^sub>2 _. (w\<^sub>1 \<noteq> w\<^sub>2 \<Longrightarrow> succ w\<^sub>1 \<noteq> succ w\<^sub>2)\<close>
  by (standard, rule succ_lt_neqI)

lemma succ_left_neqI:
    fixes w :: word
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
    shows \<open>succ (succ w) \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
proof (cases w rule: word_exhaust)
  case w: (Word num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using Suc_mod_neq by auto
qed

interpretation succ_left_neqI: exp_val_word_fixed_sz_is_ok_syntax
\<open>\<lambda>_ _ w\<^sub>1 _. (\<And>w::word. succ w \<noteq> w\<^sub>1 \<Longrightarrow> succ (succ w) \<noteq> succ w\<^sub>1)\<close>
  by (standard, rule succ_left_neqI)

lemma succ_right_neqI: 
    fixes w :: word
  assumes \<open>num\<^sub>1 < 2 ^ sz\<^sub>1\<close> and \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ w\<close> 
    shows \<open>succ (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> succ (succ w)\<close>
proof (cases w rule: word_exhaust)
  case w: (Word num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    using w assms apply safe
    unfolding succ.simps bv_plus.simps apply auto
    using Suc_mod_neq by auto
qed

interpretation succ_right_neqI: exp_val_word_fixed_sz_is_ok_syntax
  \<open>\<lambda>_ _ w\<^sub>1 _. (\<And>w::word. w\<^sub>1 \<noteq> succ w \<Longrightarrow> succ w\<^sub>1 \<noteq> succ (succ w))\<close>
  by (standard, rule succ_right_neqI)

lemma succ_succ_neqI: 
    fixes w :: word
  assumes \<open>succ w \<noteq> succ w'\<close>
    shows \<open>succ (succ w) \<noteq> succ (succ w')\<close>
proof (cases w rule: word_exhaust)
  case w: (Word num\<^sub>1 sz\<^sub>1)
  show ?thesis 
    proof (cases w' rule: word_exhaust)
      case w': (Word num\<^sub>2 sz\<^sub>2)
      show ?thesis 
        using w w' assms apply safe
        unfolding succ.simps bv_plus.simps apply auto
        using Suc_mod_neq by auto
    qed
  qed

method solve_lt_power uses add = (rule add | ((unfold power_numeral Num.pow.simps Num.sqr.simps)[1], linarith))

method solve_word_neq uses add = (
  (rule succ_neqI.word  succ_neqI.word [symmetric] succ_neqI.plus  succ_neqI.plus [symmetric]
        succ2_neqI.word succ2_neqI.word[symmetric] succ2_neqI.plus succ2_neqI.plus[symmetric]
        succ3_neqI.word succ3_neqI.word[symmetric] succ3_neqI.plus succ3_neqI.plus[symmetric]
        succ4_neqI.word succ4_neqI.word[symmetric] succ4_neqI.plus succ4_neqI.plus[symmetric]
        succ5_neqI.word succ5_neqI.word[symmetric] succ5_neqI.plus succ5_neqI.plus[symmetric]
        succ6_neqI.word succ6_neqI.word[symmetric] succ6_neqI.plus succ6_neqI.plus[symmetric]
        succ7_neqI.word succ7_neqI.word[symmetric] succ7_neqI.plus succ7_neqI.plus[symmetric]
        succ2_succ_neqI.word succ2_succ_neqI.word[symmetric] succ2_succ_neqI.plus succ2_succ_neqI.plus[symmetric]
        succ3_succ_neqI.word succ3_succ_neqI.word[symmetric] succ3_succ_neqI.plus succ3_succ_neqI.plus[symmetric]
        succ4_succ_neqI.word succ4_succ_neqI.word[symmetric] succ4_succ_neqI.plus succ4_succ_neqI.plus[symmetric]
        succ5_succ_neqI.word succ5_succ_neqI.word[symmetric] succ5_succ_neqI.plus succ5_succ_neqI.plus[symmetric]
        succ6_succ_neqI.word succ6_succ_neqI.word[symmetric] succ6_succ_neqI.plus succ6_succ_neqI.plus[symmetric]
        succ7_succ_neqI.word succ7_succ_neqI.word[symmetric] succ7_succ_neqI.plus succ7_succ_neqI.plus[symmetric],
   linarith) |

  ( rule succ_succ_neqI, solve_word_neq add: add) |
  ( rule succ_left_neqI, solve_lt_power add: add, solve_word_neq add: add) |
  ( rule succ_left_neqI.plus, solve_word_neq add: add) |
  (rule succ_right_neqI, solve_lt_power add: add, solve_word_neq add: add) |
  (rule succ_right_neqI.plus, solve_word_neq add: add) |
  (rule succ_lt_neqI.plus.plus, solve_word_neq add: add) |
  (rule succ_lt_neqI.plus.word_is_ok, solve_lt_power add: add, solve_word_neq add: add) |
  (rule succ_lt_neqI, solve_lt_power add: add, solve_lt_power add: add, solve_word_neq add: add) |
  (solves \<open>rule add\<close> | (
    solves \<open>simp (no_asm) add: add solve_exp_simpset succ.simps bv_plus.simps\<close>))
) (* match conclusion in P for P  \<Rightarrow> \<open>print_term P\<close>, *)

method solve_bv_neqI = (rule bv_not_eq_same_sz_true, solves simp)

lemma load_byte_minus_simps:
  \<open>16 - (8::nat) = 8\<close>  \<open>24 - (8::nat) = 16\<close> \<open>32 - (8::nat) = 24\<close> \<open>40 - (8::nat) = 32\<close> 
  \<open>48 - (8::nat) = 40\<close> \<open>56 - (8::nat) = 48\<close> \<open>64 - (8::nat) = 56\<close>
  by auto

end