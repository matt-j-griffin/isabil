theory Mem64_Intros
  imports "../ExpressionSemantics/Expressions_Intros"
begin



text \<open>Memory extension\<close>

(* TODO *)
lemma step_concat_extractI: \<open>\<Delta> \<turnstile> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) @ ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2) \<leadsto> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) \<cdot> ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2)\<close>
  unfolding xtract.simps by (rule step_concatI)

lemma step_exps_concat_extractI: \<open>\<Delta> \<turnstile> ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) @ ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2) \<leadsto>* ((ext num\<^sub>1 \<Colon> sz\<^sub>1 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>1 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) \<cdot> ext num\<^sub>2 \<Colon> sz\<^sub>2 \<sim> hi : sz\<^sub>h\<^sub>i\<^sub>2 \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>2)\<close>
  unfolding xtract.simps by (rule step_exps_concatI)

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

lemma concat_2_bytes: \<open>\<lbrakk>0 < n; 0 < m\<rbrakk> \<Longrightarrow> ((ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + m + n - 1) \<sim> lo : (sz\<^sub>l\<^sub>o\<^sub>1 + n)) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + n - 1) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) = ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + m + n - 1) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1\<close>
  unfolding bv_concat.simps xtract.simps apply simp
  unfolding nat_concat_bit_take_bit_drop_bit[symmetric] drop_bit_drop_bit add.commute[of n]
  ..

lemma concat_2_8bytes: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 15) \<sim> lo : (sz\<^sub>l\<^sub>o\<^sub>1 + 8)) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 7) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1) = ext num\<^sub>v \<Colon> sz \<sim> hi : (sz\<^sub>l\<^sub>o\<^sub>1 + 15) \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>1\<close>
  using concat_2_bytes[of 8 8 num\<^sub>v sz sz\<^sub>l\<^sub>o\<^sub>1] apply simp
  unfolding add.commute[of _ sz\<^sub>l\<^sub>o\<^sub>1] by simp

lemma concat_32_16: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 16\<close>
  using concat_2_8bytes[of num\<^sub>v sz 16] by simp

lemma concat_32_8: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 16) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 8\<close>
  using concat_2_bytes[of 8 16 num\<^sub>v sz 8] by simp

lemma concat_32_0: \<open>((ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 8) \<cdot> ext num\<^sub>v \<Colon> sz \<sim> hi : 7 \<sim> lo : 0) = ext num\<^sub>v \<Colon> sz \<sim> hi : 31 \<sim> lo : 0\<close>
  using concat_2_bytes[of 8 24 num\<^sub>v sz 0] by simp

(*
lemma step_exps_concat_32elI:
  \<open>\<Delta> \<turnstile> ((((ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 15 \<sim> lo : 8) @ ext num\<^sub>v \<Colon> 32 \<sim> hi : 7 \<sim> lo : 0) \<leadsto>* (num\<^sub>v \<Colon> 32)\<close>
  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_16

  apply (rule step_exps_concat_lhs.extractI)
  apply (rule step_concat_extractI)
  unfolding concat_32_8

  unfolding concat_32_0[symmetric]
*)
find_theorems Suc "(mod)"
thm mod_add_right_eq mod_add_left_eq

lemmas Gggggsimps = succ.simps bv_plus.simps mod_add_right_eq mod_add_left_eq xtract.simps drop_bit_0 mod_Suc_eq Suc3_eq_add_3

thm step_load_addrI step_load_memI.syntaxs
thm step_load_byte_from_nextI.syntaxs
thm step_load_byteI
thm step_load_byteI.syntaxs
thm step_load_word_elI
lemmas nat_concat_bit_take_bit_drop_bit2 = 
  nat_concat_bit_take_bit_drop_bit[of _ \<open>drop_bit _ _\<close> _, unfolded drop_bit_drop_bit]

lemma xtract_concat_consecutive:
  assumes \<open>x2 > x3\<close> \<open>x3 > x4\<close>
    shows \<open>(ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x3) \<cdot> (ext num \<Colon> x1 \<sim> hi : x3 - 1 \<sim> lo : x4) = (ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x4)\<close>
unfolding xtract.simps bv_concat.simps proof auto
  have sz_simp1: \<open>(Suc (x2 - x3) + Suc (x3 - Suc x4)) = (Suc (x2 - x4))\<close>
    using assms by fastforce
  have sz_simp2: \<open>Suc (x3 - Suc x4) + x4 = x3\<close>
    using assms by fastforce
  show \<open>nat (concat_bit (Suc (x3 - Suc x4)) (int (take_bit (Suc (x3 - Suc x4)) (drop_bit x4 num)))
          (int (take_bit (Suc (x2 - x3)) (drop_bit x3 num)))) = take_bit (Suc (x2 - x4)) (drop_bit x4 num)\<close>
    using nat_concat_bit_take_bit_drop_bit2[of \<open>Suc (x3 - Suc x4)\<close> x4 num \<open>Suc (x2 - x3)\<close>, unfolded sz_simp1 sz_simp2]    
    by blast
next
  show \<open>Suc (x2 - x3 + (x3 - Suc x4)) = x2 - x4\<close>
    using assms by fastforce
qed

lemma xtract64_48_el[simp]: \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) \<cdot> (ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 48)\<close>
  by (rule xtract_concat_consecutive[of 56 63 48, simplified])
lemma xtract64_40_el[simp]: \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 48) \<cdot> (ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 40)\<close>
  by (rule xtract_concat_consecutive[of 48 63 40, simplified])
lemma xtract64_32_el[simp]: \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 40) \<cdot> (ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 32)\<close>
  by (rule xtract_concat_consecutive[of 40 63 32, simplified])
lemma xtract64_24_el[simp]: \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 32) \<cdot> (ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 24)\<close>
  by (rule xtract_concat_consecutive[of 32 63 24, simplified])
lemma xtract64_16_el[simp]: \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 24) \<cdot> (ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 16)\<close>
  by (rule xtract_concat_consecutive[of 24 63 16, simplified])
lemma xtract64_8_el[simp]:  \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 16) \<cdot> (ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo :  8)\<close>
  by (rule xtract_concat_consecutive[of 16 63 8, simplified])
lemma xtract64_0_el[simp]:  \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 8) \<cdot> (ext num \<Colon> 64 \<sim> hi : 7 \<sim> lo :  0) = (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo :  0)\<close>
  by (rule xtract_concat_consecutive[of 8 63 0, simplified])

lemmas xtract64_els = xtract64_48_el xtract64_40_el xtract64_32_el xtract64_24_el xtract64_16_el
                      xtract64_8_el  xtract64_0_el

lemma step_exps_concat_word64_elI: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) @ ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) @
  ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) @ ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) @
  ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) @ ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) @
  ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) @ ext num \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>  
  apply solve_expsI
  unfolding xtract64_els
  apply solve_expsI
  unfolding xtract64_els
  apply solve_expsI
  unfolding xtract64_els
  apply solve_expsI
  unfolding xtract64_els
  apply solve_expsI
  unfolding xtract64_els
  apply solve_expsI
  unfolding xtract64_els
  unfolding xtract64_0_el[symmetric]
  by (rule step_exps_concatI.xtract.xtract)

lemma step_exps_load_word64_elI: \<open>\<Delta> \<turnstile> (storage64 v num\<^sub>a 64 num\<^sub>v)[num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  apply solve_expsI
  apply simp
  apply solve_expsI
  sorry

lemma step_exps_store_word64_elI: 
  assumes \<open>type mem = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a \<Colon> 64, el]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage64 v num\<^sub>a 64 num\<^sub>v)\<close>
  using assms apply -
  apply solve_expsI
  using step_exps_store_word_elI.storage.word
  apply solve_expsI
  apply simp
  apply solve_expsI
  sorry

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


end