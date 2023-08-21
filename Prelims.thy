theory Prelims
  imports Main
begin

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

text \<open>simp rules for solving nth numerals\<close>

lemmas nth_numeral_simps = nth_Cons_numeral One_nat_def nth_Cons_Suc diff_numeral_Suc diff_zero pred_numeral_simps 
            Num.BitM.simps(1) numeral_One nth_Cons_0


end