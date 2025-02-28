theory Prelims
  imports Main 
          "Eisbach-Match-Schematics.Match_Inline" 
begin


method solve_set_inI uses add =
  (solves \<open>rule add\<close>) |
  (rule singletonI insertI1) |
  (rule insertI2, solve_set_inI) |
  (rule UnI1, solve_set_inI add: add) |
  (rule UnI2, solve_set_inI add: add) |
  \<comment> \<open>Without the guard this will loop indefinitely\<close>
  (match_schematics add in subset: \<open>_ \<subseteq> _\<close> \<Rightarrow> \<open>(rule set_mp, solves \<open>rule subset\<close>, solve_set_inI add: add)\<close>)

lemma mod_Suc_neq: \<open>1 < y \<Longrightarrow> Suc x mod y \<noteq> x mod y\<close>
  unfolding mod_Suc by simp

lemma not_dvd_plus_mod_neq: fixes z :: \<open>'a::semiring_modulo\<close> shows \<open>\<not>(y dvd z) \<Longrightarrow> (z + x) mod y \<noteq> x\<close>
  by (metis add.commute add_left_cancel dvd_triv_left mod_mult_div_eq)

lemma mod_between_neq: fixes w :: nat shows "w < y \<Longrightarrow> 0 < w \<Longrightarrow> x \<noteq> (w + x) mod y"
  by (metis (no_types, opaque_lifting) add.assoc antisym_conv3 canonically_ordered_monoid_add_class.lessE less_nat_zero_code mod_add_left_eq mod_add_self2 mod_less mod_less_divisor mod_self)

lemmas mod_between_neq' = mod_between_neq[symmetric]

lemma not_dvd_Suc_Suc_mod_neq: \<open>y \<noteq> 1 \<Longrightarrow> y \<noteq> 2 \<Longrightarrow> Suc (Suc x) mod y \<noteq> x\<close>
  apply (cases "y = 0", simp)
  unfolding add_2_eq_Suc[symmetric] apply (rule mod_between_neq')
  by auto

lemma not_dvd_Suc_mod_neq: \<open>y \<noteq> 1 \<Longrightarrow> (Suc x) mod y \<noteq> x\<close>
  by (metis One_nat_def mod_Suc mod_Suc_eq n_not_Suc_n)



lemma Suc_mod_neq: \<open>a mod y \<noteq> b mod y \<Longrightarrow> Suc a mod y \<noteq> Suc b mod y\<close>
  by (simp add: mod_Suc)

lemma mod_lt_neqI:
  fixes num\<^sub>1 :: nat
  assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> and \<open>num\<^sub>1 < sz\<^sub>1\<close> and \<open>num\<^sub>2 < sz\<^sub>1\<close>
    shows \<open>num\<^sub>1 mod sz\<^sub>1 \<noteq> num\<^sub>2 mod sz\<^sub>1\<close>
  using assms mod_Suc by auto

lemma plus_mod_neq: fixes y :: nat shows "z < y \<Longrightarrow> w < y \<Longrightarrow> z \<noteq> w \<Longrightarrow> (z + x) mod y \<noteq> (w + x) mod y"
proof (induct z)
  case 0
  thus ?case 
    apply simp
    using mod_between_neq'[of w y \<open>x mod y\<close>] unfolding mod_add_right_eq by simp
next
  case (Suc z)
  thus ?case 
    apply simp
    apply (cases \<open>w = z\<close>, simp)
    apply (simp add: mod_Suc)
    apply simp
    apply (induct w)
    apply simp
    using mod_between_neq'[of \<open>Suc z\<close> y \<open>x mod y\<close>, symmetric] unfolding mod_add_right_eq
    apply simp
    apply simp
    subgoal for w
      apply (cases \<open>w = Suc z\<close>, simp_all)
      apply (simp add: mod_Suc)
      apply (rule Suc_mod_neq)
      by (metis (no_types, opaque_lifting) Suc_lessD Suc_lessE ab_semigroup_add_class.add_ac(1) mod_add_left_eq mod_less mod_mult_self2 mult.commute mult_Suc_right)
    .
qed

lemma plus_mod_neq_lhs: fixes y :: nat shows "z < y \<Longrightarrow> w < y \<Longrightarrow> z \<noteq> w \<Longrightarrow> (x + z) mod y \<noteq> (x + w) mod y"
  using plus_mod_neq by presburger

lemma plus_Suc_right_mod_neq:"z < y \<Longrightarrow> 1 < y \<Longrightarrow> z \<noteq> 1 \<Longrightarrow> (z + x) mod y \<noteq> Suc x mod y"
  unfolding plus_1_eq_Suc[symmetric] by (rule plus_mod_neq)

lemma plus_Suc_left_mod_neq:"z < y \<Longrightarrow> 1 < y \<Longrightarrow> z \<noteq> 1 \<Longrightarrow> Suc x mod y \<noteq> (z + x) mod y"
  unfolding plus_1_eq_Suc[symmetric] apply (rule plus_mod_neq)
  by simp_all

lemma plus_Suc_Suc_right_mod_neq:"z < y \<Longrightarrow> 2 < y \<Longrightarrow> z \<noteq> 1 \<Longrightarrow> z \<noteq> 2 \<Longrightarrow> (z + x) mod y \<noteq> Suc (Suc x) mod y"
  using plus_mod_neq by presburger
  
lemma plus_Suc_Suc_left_mod_neq:"z < y \<Longrightarrow> 2 < y \<Longrightarrow> z \<noteq> 1 \<Longrightarrow> z \<noteq> 2 \<Longrightarrow> Suc (Suc x) mod y \<noteq> (z + x) mod y"
  using plus_mod_neq by presburger


lemma push_bit_drop_bit_take_bit: \<open>push_bit n (drop_bit n (take_bit (m + n) x)) =
    take_bit (m + n) (push_bit n (drop_bit n x))\<close>
  unfolding take_bit_drop_bit[symmetric]
  unfolding push_bit_take_bit add.commute[of m] ..

lemma take_bit_plus_push_bit_drop_bit: \<open>take_bit (m + n) x = take_bit (m + n) (push_bit n (drop_bit n x)) + take_bit n x\<close>
  apply (subst bits_ident[of n \<open>take_bit (m + n) x\<close>, symmetric])
  unfolding take_bit_take_bit
  using push_bit_drop_bit_take_bit[of n m] by simp

lemma concat_take_drop_bit_eq_self:
  assumes \<open>0 \<le> x\<close> and \<open>x < 2 ^ (sz\<^sub>1 + sz\<^sub>2)\<close>
    shows \<open>x = concat_bit sz\<^sub>1 x (take_bit sz\<^sub>2 (drop_bit sz\<^sub>1 x))\<close>
  apply (insert assms)
  apply (drule take_bit_int_eq_self)
  apply blast
  unfolding concat_bit_eq
  unfolding add.commute[of \<open>take_bit sz\<^sub>1 x\<close>]
  unfolding take_bit_drop_bit
  unfolding add.commute[of \<open>sz\<^sub>2\<close>]
  apply simp
  unfolding bits_ident ..
  
lemma concat_take_drop_bit_nat_eq_self:
  assumes \<open>x < 2 ^ (sz\<^sub>1 + sz\<^sub>2)\<close>
    shows \<open>x = nat (concat_bit sz\<^sub>1 (int x) (take_bit sz\<^sub>2 (drop_bit sz\<^sub>1 (int x))))\<close>
  using assms concat_take_drop_bit_eq_self by auto

lemma concat_bit_drop_bit: \<open>concat_bit a x (concat_bit b (drop_bit a x) z) = concat_bit (a + b) x z\<close>
  using add.commute bits_ident concat_bit_assoc concat_bit_eq by (metis )

lemma concat_bit_take_bit_drop_bit: \<open>concat_bit n (take_bit n x) (take_bit m (drop_bit n x)) = take_bit (m + n) x\<close>
  unfolding concat_bit_eq 
  unfolding take_bit_take_bit min.idem
  unfolding push_bit_take_bit add.commute[of \<open>take_bit n _\<close>]
  apply (subst take_bit_plus_push_bit_drop_bit[of m n \<open>x\<close>])
  unfolding add.commute[of m] ..

lemma nat_concat_bit_take_bit_drop_bit: \<open>nat (concat_bit n (int (take_bit n x)) (int (take_bit m (drop_bit n x)))) = take_bit (m + n) x\<close>
  unfolding concat_bit_eq take_bit_of_nat push_bit_of_nat nat_int_add concat_bit_take_bit_drop_bit 
            take_bit_take_bit min.idem push_bit_take_bit add.commute[of \<open>take_bit n _\<close>]
  apply (subst take_bit_plus_push_bit_drop_bit[of m n \<open>x\<close>])
  unfolding add.commute[of m] ..

lemmas nat_concat_bit_take_bit_drop_bit2 = 
  nat_concat_bit_take_bit_drop_bit[of _ \<open>drop_bit _ _\<close> _, unfolded drop_bit_drop_bit]


lemma notin_unionI:
  assumes \<open>x \<notin> A\<close> and \<open>x \<notin> B\<close>
    shows \<open>x \<notin> A \<union> B\<close>
  using assms by simp

lemma insert_diffE:
  assumes \<open>a \<notin> insert b C\<close>
    shows \<open>a \<notin> C \<and> a \<noteq> b\<close>
  using assms by simp

lemma not_in_empty_set_list: \<open>z \<notin> set []\<close>
  by auto


lemma length_1: \<open>length [x] = 1\<close>
  by auto

lemma nat_lt2: \<open>((i::nat) < 1 + 1) = (i = 0 \<or> i = 1)\<close>
  by auto


lemma power_le_min: fixes x n N :: nat assumes \<open>n \<le> N\<close> and \<open>x < 2 ^ n\<close> shows \<open>x < 2 ^ N\<close>
  using assms order_less_le_trans by fastforce

lemma power_lt_min: fixes x n N :: nat assumes \<open>n < N\<close> and \<open>x < 2 ^ (Suc n)\<close> shows \<open>x < 2 ^ N\<close>
  using Suc_leI assms power_le_min by blast

text \<open>simp rules for solving nth numerals\<close>

lemmas nth_numeral_simps = nth_Cons_numeral One_nat_def nth_Cons_Suc diff_numeral_Suc diff_zero pred_numeral_simps 
            Num.BitM.simps(1) numeral_One nth_Cons_0

end
