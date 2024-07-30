theory Mem64_Intros
  imports Mem64
          Mem32_Intros
begin

lemmas xtract64_56_48[simp] = xtract_concat_consecutive[of 56 63 48, simplified]
lemmas xtract64_48_40[simp] = xtract_concat_consecutive[of 48 63 40, simplified]
lemmas xtract64_40_32[simp] = xtract_concat_consecutive[of 40 63 32, simplified]
lemmas xtract64_32_24[simp] = xtract_concat_consecutive[of 32 63 24, simplified]
lemmas xtract64_24_16[simp] = xtract_concat_consecutive[of 24 63 16, simplified]
lemmas xtract64_16_8 [simp] = xtract_concat_consecutive[of 16 63 8, simplified]
lemmas xtract64_8_0  [simp] = xtract_concat_consecutive[of 8 63 0, simplified]
lemmas xtract40_32_0 [simp] = xtract_concat_consecutive[of 32 39 0, simplified]
lemmas xtract48_40_0 [simp] = xtract_concat_consecutive[of 40 47 0, simplified]
lemmas xtract56_48_0 [simp] = xtract_concat_consecutive[of 48 55 0, simplified]
lemmas xtract64_56_0 [simp] = xtract_concat_consecutive[of 56 63 0, simplified]
lemmas xtract64 = xtract64_56_48 xtract64_48_40 xtract64_40_32 xtract64_32_24 xtract64_24_16
                  xtract64_16_8  xtract64_8_0

lemmas xtract_nested_63_8_55_8[simp]  = nested_extract_within [of  8  8 63, simplified]
lemmas xtract_nested_63_16_47_8[simp] = nested_extract_within [of  8 16 63, simplified]
lemmas xtract_nested_63_24_39_8[simp] = nested_extract_within [of  8 24 63, simplified]
lemmas xtract_nested_63_32_31_8[simp] = nested_extract_within [of  8 32 63, simplified]
lemmas xtract_nested_63_40_23_8[simp] = nested_extract_within [of  8 40 63, simplified]
lemmas xtract_nested_63_48_15_8[simp] = nested_extract_within [of  8 48 63, simplified]
lemmas xtract_nested_55_0_47_0[simp]  = nested_extract_within'[of  0 47  0 55, simplified]
lemmas xtract_nested_47_0_39_0[simp]  = nested_extract_within'[of  0 39  0 47, simplified]
lemmas xtract_nested_39_0_31_0[simp]  = nested_extract_within'[of  0 31  0 39, simplified]
lemmas xtract_nested_63_8_7_0[simp]   = nested_extract_within'[of  0  7  8 63,  simplified]
lemmas xtract_nested_63_16_7_0[simp]  = nested_extract_within'[of  0  7 16 63, simplified]
lemmas xtract_nested_63_24_7_0[simp]  = nested_extract_within'[of  0  7 24 63, simplified]
lemmas xtract_nested_63_32_7_0[simp]  = nested_extract_within'[of  0  7 32 63, simplified]
lemmas xtract_nested_63_40_7_0[simp]  = nested_extract_within'[of  0  7 40 63, simplified]
lemmas xtract_nested_63_48_7_0[simp]  = nested_extract_within'[of  0  7 48 63, simplified]
lemmas xtract_nested_55_0_55_48[simp] = nested_extract_within'[of 48 55  0 55, simplified]
lemmas xtract_nested_47_0_47_40[simp] = nested_extract_within'[of 40 47  0 47, simplified]
lemmas xtract_nested_39_0_39_32[simp] = nested_extract_within'[of 32 39  0 39, simplified]

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word64_elI: \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) @ ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) @
  ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) @ ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) @
  ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) @ ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) @
  ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) @ ext num \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>  
  apply (solve_expsI, unfold xtract64)+
  by (unfold xtract64_8_0[symmetric], rule step_exps_concatI.xtract.xtract)

lemma xtract_num_lt:
  assumes num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>(ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = num \<Colon> 64\<close>
  using extract_concat64 num_lt by auto

lemma step_exps_concat_word64_el_num_ltI: 
  assumes num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> ((((((((
  ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) @ ext num \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) @
  ext num \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) @ ext num \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) @
  ext num \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) @ ext num \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) @
  ext num \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) @ ext num \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (num \<Colon> 64)\<close>  
  using step_exps_concat_word64_elI[where num = num and \<Delta> = \<Delta>]
  unfolding xtract_num_lt[OF num_lt] .

method solve_exp_succ64I_scaffold methods recurs solve_type uses add = (
  (rule step_load_byteI.word.succ4 step_load_byteI.word.succ5 step_load_byteI.word.succ6 
        step_load_byteI.word.succ7 

        step_load_byteI.succ.succ4 step_load_byteI.succ.succ5 step_load_byteI.succ.succ6
        step_load_byteI.succ.succ7

        step_load_byteI.succ4.word    step_load_byteI.succ4.true    step_load_byteI.succ4.false
        step_load_byteI.succ4.storage step_load_byteI.succ4.unknown step_load_byteI.succ4.xtract
        step_load_byteI.succ4.succ    step_load_byteI.succ4.succ2   step_load_byteI.succ4.succ3 
        step_load_byteI.succ4.succ4   step_load_byteI.succ4.succ5   step_load_byteI.succ4.succ6   
        step_load_byteI.succ4.succ7   step_load_byteI.succ4.val

        step_load_byteI.succ5.word    step_load_byteI.succ5.true    step_load_byteI.succ5.false
        step_load_byteI.succ5.storage step_load_byteI.succ5.unknown step_load_byteI.succ5.xtract
        step_load_byteI.succ5.succ    step_load_byteI.succ5.succ2   step_load_byteI.succ5.succ3
        step_load_byteI.succ5.succ4   step_load_byteI.succ5.succ5   step_load_byteI.succ5.succ6   
        step_load_byteI.succ5.succ7   step_load_byteI.succ5.val

        step_load_byteI.succ6.word    step_load_byteI.succ6.true    step_load_byteI.succ6.false 
        step_load_byteI.succ6.storage step_load_byteI.succ6.unknown step_load_byteI.succ6.xtract
        step_load_byteI.succ6.succ    step_load_byteI.succ6.succ2   step_load_byteI.succ6.succ3
        step_load_byteI.succ6.succ4   step_load_byteI.succ6.succ5   step_load_byteI.succ6.succ6   
        step_load_byteI.succ6.succ7   step_load_byteI.succ6.val

        step_load_byteI.succ7.word    step_load_byteI.succ7.true    step_load_byteI.succ7.false
        step_load_byteI.succ7.storage step_load_byteI.succ7.unknown step_load_byteI.succ7.xtract
        step_load_byteI.succ7.succ    step_load_byteI.succ7.succ2   step_load_byteI.succ7.succ3 
        step_load_byteI.succ7.succ4   step_load_byteI.succ7.succ5   step_load_byteI.succ7.succ6   
        step_load_byteI.succ7.succ7   step_load_byteI.succ7.val
        
        (*step_load_byteI.succ2.succ4   step_load_byteI.succ2.succ5   step_load_byteI.succ2.succ6
        step_load_byteI.succ2.succ7   step_load_byteI.succ3.succ4   step_load_byteI.succ3.succ5
        step_load_byteI.succ3.succ6   step_load_byteI.succ3.succ7*)

        step_load_byteI.plus.word step_load_byteI.plus.xtract


        step_store_valI.succ4.storage.xtract step_store_valI.succ5.storage.xtract
        step_store_valI.succ6.storage.xtract step_store_valI.succ7.storage.xtract) |


  (rule step_load_byte_from_nextI.succ4.storage step_load_byte_from_nextI.succ5.storage   
        step_load_byte_from_nextI.succ6.storage step_load_byte_from_nextI.succ7.storage, 
    solve_word_neq add: add) |

  (rule step_load_word_elI.storage.succ4 step_load_word_elI.storage.succ5 
        step_load_word_elI.storage.succ6 step_load_word_elI.storage.succ7 
        step_load_word_beI.storage.succ4 step_load_word_beI.storage.succ5
        step_load_word_beI.storage.succ6 step_load_word_beI.storage.succ7 | 
  (rule step_load_word_elI.storage_addr.succ4 step_load_word_elI.storage_addr.succ5
        step_load_word_elI.storage_addr.succ6 step_load_word_elI.storage_addr.succ7
        step_load_word_beI.storage_addr.succ4 step_load_word_beI.storage_addr.succ5
        step_load_word_beI.storage_addr.succ6 step_load_word_beI.storage_addr.succ7, 
   solve_type),
   (unfold load_byte_minus_simps)?,
   linarith) |

  (rule step_store_valI.succ4.storage_addr.xtract step_store_valI.succ4.val.xtract 
        step_store_valI.succ5.storage_addr.xtract step_store_valI.succ5.val.xtract
        step_store_valI.succ6.storage_addr.xtract step_store_valI.succ6.val.xtract
        step_store_valI.succ7.storage_addr.xtract step_store_valI.succ7.val.xtract, 
   solve_type) |

  (solve_exp_succ32I_scaffold recurs solve_type add: add)
)                     
(* (match conclusion in \<open>P\<close> for P  \<Rightarrow> \<open>print_term P\<close>),*)
method solve_exp_succ64I uses add = (
  solve_exp_succ64I_scaffold \<open>solve_exp_succ64I add: add\<close> solve_type_succ64I add: add
)


method solve_exps_succ64I_scaffold methods recurs solve_exp solve_type uses add = (
  (rule step_exps_concat_word64_el_num_ltI, (rule add | (((unfold power_numeral Num.pow.simps Num.sqr.simps)[1])?, linarith))) |
  (rule step_exps_concat_word64_elI) |

  (rule step_exps_store_valI.succ4.storage_addr.xtract step_exps_store_valI.succ5.storage_addr.xtract
        step_exps_store_valI.succ6.storage_addr.xtract step_exps_store_valI.succ7.storage_addr.xtract, 
   solve_type) |

  (rule step_exps_store_word_elI.succ7.storage.xtract step_exps_store_word_elI.succ6.storage.xtract
        step_exps_store_word_elI.succ5.storage.xtract step_exps_store_word_elI.succ4.storage.xtract 
        step_exps_store_word_beI.succ7.storage.xtract step_exps_store_word_beI.succ6.storage.xtract
        step_exps_store_word_beI.succ5.storage.xtract step_exps_store_word_beI.succ4.storage.xtract,
   linarith, standard, (recurs | succeed)) |

  (rule step_exps_store_word_elI.succ7.storage_addr.xtract 
        step_exps_store_word_elI.succ6.storage_addr.xtract 
        step_exps_store_word_elI.succ5.storage_addr.xtract 
        step_exps_store_word_elI.succ4.storage_addr.xtract 
        step_exps_store_word_beI.succ7.storage_addr.xtract 
        step_exps_store_word_beI.succ6.storage_addr.xtract 
        step_exps_store_word_beI.succ5.storage_addr.xtract 
        step_exps_store_word_beI.succ4.storage_addr.xtract, 
   solve_type, linarith, standard, (recurs | succeed)) |

  (rule step_exps_store_memI.succ7.xtract step_exps_store_memI.succ6.xtract
        step_exps_store_memI.succ5.xtract step_exps_store_memI.succ4.xtract, 
   solve_exp, (recurs | succeed)) |

  (solve_exps_mem32I_scaffold recurs solve_exp solve_type add: add)
)

method solve_exps_succ64I uses add = (
  solve_exps_succ64I_scaffold \<open>solve_exps_succ64I add: add\<close> \<open>solve_exp_succ64I add: add\<close> 
      solve_type_succ64I add: add
)

lemma step_exps_load_word64_elI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  using assms apply -
  by solve_exps_succ64I

interpretation step_exps_load_word64_elI: exp_val_word_fixed_sz_syntax2 
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _. (\<And>\<Delta> v. 2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, el]:u64 \<leadsto>* (ext e\<^sub>v \<sim> hi : 63 \<sim> lo : 0))\<close> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r 64
  apply standard
  using step_exps_load_word64_elI by blast

interpretation step_exps_load_word64_el64I: exp_val_word_fixed_sz_syntax2 
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>v v\<^sub>v w\<^sub>v _. (\<And>\<Delta> v.
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a v\<^sub>v)[e\<^sub>a, el]:u64 \<leadsto>* (ext e\<^sub>v \<sim> hi : 63 \<sim> lo : 0))\<close> 64 64
  apply standard
  using step_exps_load_word64_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified] by blast
  
lemma step_exps_load_word64_el_num_ltI: 
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and num_lt: \<open>num\<^sub>v < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64)\<close>
  using step_exps_load_word64_elI[OF assms(1), where num\<^sub>v=num\<^sub>v]
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_el_num_ltI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>e\<^sub>a _ w\<^sub>a sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>\<Delta> v num\<^sub>v. \<lbrakk>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r; num\<^sub>v < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64))\<close> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
  apply standard
  using step_exps_load_word64_el_num_ltI by blast

lemma step_exps_load_word64_el64_num_ltI:
  assumes \<open>num\<^sub>v < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 v (num\<^sub>a \<Colon> 64) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> 64, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64)\<close>
  apply (rule step_exps_load_word64_el_num_ltI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, OF _ assms])
  by linarith

lemma lt_2_64: \<open>2 < (64::nat)\<close> by simp

interpretation step_exps_load_word64_el64_num_ltI: exp_val_word_fixed_sz_syntax
\<open>\<lambda>e\<^sub>a _ w\<^sub>a _. (\<And>\<Delta> v num\<^sub>v. \<lbrakk>num\<^sub>v < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 v w\<^sub>a (num\<^sub>v \<Colon> 64))[e\<^sub>a, el]:u64 \<leadsto>* (num\<^sub>v \<Colon> 64))\<close> 64
  apply standard
  using step_exps_load_word64_el_num_ltI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, OF lt_2_64] by blast

lemma step_exps_load_word64_next_el64I: 
  assumes neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  by (solve_exps_succ64I add: addr_ok no_address_overlap_64_64[OF neq])

interpretation step_exps_load_word64_next_el64I: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta> v mem' num. \<lbrakk>no_address_overlap_64_64 w\<^sub>2 w\<^sub>1\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v)
             [e\<^sub>1, el]:u64 \<leadsto>* (ext num \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0))\<close> 64 64
  by (standard, rule step_exps_load_word64_next_el64I)

lemma step_exps_load_word64_next_el64_num_ltI: 
  assumes neq: \<open>no_address_overlap_64_64 ((addr\<^sub>2 \<Colon> 64)::word) (addr\<^sub>1 \<Colon> 64)\<close>
      and addr_ok: \<open>addr\<^sub>1 < 2 ^ 64\<close> \<open>addr\<^sub>2 < 2 ^ 64\<close> 
      and num_lt: \<open>num < 2 ^ 64\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' (addr\<^sub>1 \<Colon> 64) (num \<Colon> 64)) (addr\<^sub>2 \<Colon> 64) v)
             [(addr\<^sub>1 \<Colon> 64), el]:u64 \<leadsto>* (num \<Colon> 64)\<close>
  using step_exps_load_word64_next_el64I[OF neq addr_ok, where num=num]
  unfolding xtract_num_lt[OF num_lt] .

interpretation step_exps_load_word64_next_el64_num_ltI: exp_val_word_fixed_sz_syntax_is_ok2
\<open>\<lambda>e\<^sub>1 _ w\<^sub>1 _ e\<^sub>2 _ w\<^sub>2 _. (\<And>\<Delta> v mem' num. \<lbrakk>no_address_overlap_64_64 w\<^sub>2 w\<^sub>1; num < 2 ^ 64\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el64 (storage_el64 mem' w\<^sub>1 (num \<Colon> 64)) w\<^sub>2 v)
             [e\<^sub>1, el]:u64 \<leadsto>* (num \<Colon> 64))\<close> 64 64
  by (standard, rule step_exps_load_word64_next_el64_num_ltI)

lemma step_exps_store_word64_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_el64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  using assms apply -
  apply (solve_exps_succ64I, simp)+
  by solve_exps_succ64I

interpretation step_exps_store_word64_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  apply (standard)
  using step_exps_store_word64_elI by blast

\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word64_beI:
  assumes \<open>2 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be64 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leadsto>* (ext num\<^sub>v \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_exps_succ64I, simp)+
  unfolding xtract64_56_0[symmetric] by solve_exps_succ64I

lemmas step_exps_load_word64_be64I = step_exps_load_word64_beI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word64_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u64 \<leftarrow> (num\<^sub>v \<Colon> 64) \<leadsto>* (storage_be64 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 64))\<close>
  using assms apply -
  apply (solve_exps_succ64I, simp)+
  by solve_exps_succ64I

interpretation step_exps_store_word64_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u64 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be64 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 64
  apply standard
  using step_exps_store_word64_beI by blast

\<comment> \<open>The 64 bit solver scaffold\<close>
method solve_exps_mem64I_scaffold methods recurs solve_exp solve_type uses add = (
  (rule step_exps_load_word64_el64I.word.word step_exps_load_word64_el64I.succ.word
        step_exps_load_word64_el64I.plus.word) |

  (rule step_exps_load_word64_elI.word.word step_exps_load_word64_elI.succ.word 
        step_exps_load_word64_elI.plus.word 
        step_exps_load_word64_el64_num_ltI.word step_exps_load_word64_el64_num_ltI.succ
        step_exps_load_word64_el64_num_ltI.plus
        
        step_exps_load_word64_el_num_ltI.word step_exps_load_word64_el_num_ltI.succ
        step_exps_load_word64_el_num_ltI.plus; (rule add | linarith)) | 

  (rule step_exps_load_word64_next_el64_num_ltI.plus.plus; (rule add | linarith)) |

  (rule step_exps_load_word64_be64I) | (rule step_exps_load_word64_beI, linarith) |

  (rule step_exps_store_word64_elI.val.plus.word, solve_type) |
  (rule step_exps_store_word64_elI.val.word.xtract_sz, linarith, solve_type) |
  (rule step_exps_store_word64_elI, solve_type) |

  (rule step_exps_store_word64_beI.val.plus.word step_exps_store_word64_beI, solve_type) |
   
  (solve_exps_succ64I_scaffold recurs solve_exp solve_type add: add)
)

lemmas solve_exps_mem64_simps = 
  xtract64_56_48 xtract64_48_40 xtract64_40_32 xtract64_32_24 xtract64_24_16 xtract64_16_8 
  xtract64_8_0   xtract40_32_0  xtract48_40_0  xtract56_48_0  xtract64_56_0

  xtract_nested_63_8_55_8  xtract_nested_63_16_47_8 xtract_nested_63_24_39_8 
  xtract_nested_63_32_31_8 xtract_nested_63_40_23_8 xtract_nested_63_48_15_8
  xtract_nested_55_0_47_0  xtract_nested_47_0_39_0  xtract_nested_39_0_31_0
  xtract_nested_63_8_7_0   xtract_nested_63_16_7_0  xtract_nested_63_24_7_0
  xtract_nested_63_32_7_0  xtract_nested_63_40_7_0  xtract_nested_63_48_7_0
  xtract_nested_55_0_55_48 xtract_nested_47_0_47_40 xtract_nested_39_0_39_32


method solve_exps_mem64I uses add = (
  solve_exps_mem64I_scaffold \<open>solve_exps_mem64I add: add\<close> \<open>solve_exp_succ64I add: add\<close>
      solve_type_succ64I add: add
)

method solve_bil_mem64I uses add = (
  solve_bilI_scaffold \<open>solve_bil_mem64I add: add\<close> \<open>solve_exps_mem64I add: add\<close> add: add
)

context bil_syntax
begin

method solve_prog_mem64I uses add decoder = (
  solve_progI_scaffold \<open>solve_bil_mem64I add: add\<close> decoder: decoder
)

end

end
