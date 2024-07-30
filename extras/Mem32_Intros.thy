theory Mem32_Intros
  imports Mem32
          Mem16_Intros
begin

lemmas xtract32_24_16[simp] = xtract_concat_consecutive[of 24 31 16, simplified]
lemmas xtract32_16_8 [simp] = xtract_concat_consecutive[of 16 31 8, simplified]
lemmas xtract32_8_0  [simp] = xtract_concat_consecutive[of 8 31 0, simplified]
lemmas xtract23_16_0 [simp] = xtract_concat_consecutive[of 16 23 0, simplified]
lemmas xtract32_24_0 [simp] = xtract_concat_consecutive[of 24 31 0, simplified]
lemmas xtract32 = xtract32_24_16 xtract32_24_0 xtract32_16_8 xtract32_8_0 xtract23_16_0
                  xtract16_8_0

lemmas xtract_nested_31_0_23_0 [simp] = nested_extract_within'[of  0 23  0 31, simplified]
lemmas xtract_nested_31_0_31_24[simp] = nested_extract_within'[of 24 31  0 31, simplified]
lemmas xtract_nested_31_8_7_0  [simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 8 and sz\<^sub>h\<^sub>i' = 7 and sz\<^sub>l\<^sub>o' = 0, simplified]
lemmas xtract_nested_31_8_23_8 [simp] = nested_extract_within [where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 8 and sz\<^sub>l\<^sub>o' = 8, simplified]
lemmas xtract_nested_31_16_15_8[simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 16 and sz\<^sub>h\<^sub>i' = 15 and sz\<^sub>l\<^sub>o' = 8, simplified]
lemmas xtract_nested_31_16_7_0[simp] = nested_extract_within'[where sz\<^sub>h\<^sub>i = 31 and sz\<^sub>l\<^sub>o = 16 and sz\<^sub>h\<^sub>i' = 7 and sz\<^sub>l\<^sub>o' = 0, simplified]
lemmas xtract_nested_23_0_15_0 [simp] = nested_extract_within'[of  0 15  0 23, simplified]
lemmas xtract_nested_23_0_23_16[simp] = nested_extract_within'[of 16 23  0 23, simplified]
lemmas xtract_nested_15_0_7_0  [simp] = nested_extract_within'[of  0  7  0 15, simplified]
lemmas xtract_nested_15_0_15_8 [simp] = nested_extract_within'[of  8 15  0 15, simplified]
lemmas xtract_nested32 = 
  xtract_nested_31_0_23_0  xtract_nested_31_0_31_24 xtract_nested_31_8_7_0  xtract_nested_31_8_23_8 
  xtract_nested_31_16_15_8 xtract_nested_31_16_7_0  xtract_nested_23_0_15_0 xtract_nested_23_0_23_16
  xtract_nested_15_0_7_0   xtract_nested_15_0_15_8

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word32_elI: \<open>\<Delta> \<turnstile> ((((
  ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) @ ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) @
  ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8) @ ext num \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0) \<leadsto>* (ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0)\<close>
  apply (solve_expsI, unfold xtract32)+
  by (unfold xtract32_8_0[symmetric], rule step_exps_concatI.xtract.xtract)

lemma xtract_31_0_63_0:
  assumes \<open>num < 2 ^ 32\<close>
    shows \<open>(ext (ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0) \<sim> hi : 63 \<sim> lo : 0) = (num \<Colon> 64)\<close>
  unfolding xtract.simps apply simp
  using assms take_bit_nat_eq_self by blast

lemma step_exps_cast64_concat32_elI: 
  assumes num_lt: \<open>num < 2 ^ 32\<close>
    shows \<open>\<Delta> \<turnstile> extend:64[
   (((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24)  @ ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) @
      ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8)  @ ext num \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0] \<leadsto>* 
        (num \<Colon> 64)\<close>
  unfolding xtract_31_0_63_0[OF num_lt, symmetric]
  apply (solve_expsI, unfold xtract32)+
  by (rule step_exps_cast_signedI.xtract[where sz = 64, simplified])

method solve_exp_succ32I_scaffold methods recurs solve_type uses add = (
  (rule step_load_byteI.word.succ2    step_load_byteI.word.succ3    step_load_byteI.succ.succ2
        step_load_byteI.succ.succ3    step_load_byteI.succ2.word    step_load_byteI.succ2.true
        step_load_byteI.succ2.false   step_load_byteI.succ2.storage step_load_byteI.succ2.unknown
        step_load_byteI.succ2.xtract  step_load_byteI.succ2.succ    step_load_byteI.succ2.succ2
        step_load_byteI.succ2.succ3   step_load_byteI.succ2.val     step_load_byteI.succ3.word
        step_load_byteI.succ3.true    step_load_byteI.succ3.false   step_load_byteI.succ3.storage
        step_load_byteI.succ3.unknown step_load_byteI.succ3.xtract  step_load_byteI.succ3.succ 
        step_load_byteI.succ3.succ2   step_load_byteI.succ3.succ3   step_load_byteI.succ3.val) |

  (rule step_load_byte_from_nextI.succ2.storage step_load_byte_from_nextI.succ3.storage, 
   solve_word_neq add: add) |

  ((rule step_load_word_elI.storage.succ2 step_load_word_elI.storage.succ3
         step_load_word_beI.storage.succ2 step_load_word_beI.storage.succ3 | 
   (rule step_load_word_elI.storage_addr.succ2 step_load_word_elI.storage_addr.succ3
         step_load_word_beI.storage_addr.succ2 step_load_word_beI.storage_addr.succ3,
    solve_type)),
  (unfold load_byte_minus_simps)?,
  linarith) |



  (rule step_store_valI.succ2.storage.xtract) |
  (rule step_store_valI.succ2.storage_addr.xtract, solve_type) |
  (rule step_store_valI.succ2.val.xtract, solve_type) |
  (rule step_store_valI.succ3.storage.xtract) |
  (rule step_store_valI.succ3.storage_addr.xtract, solve_type) |
  (rule step_store_valI.succ3.val.xtract, solve_type) |

  (solve_expI_scaffold recurs solve_type add: add)
)

method solve_exp_succ32I uses add = (
  solve_exp_succ32I_scaffold \<open>solve_exp_succ32I add: add\<close> solve_typeI add: add
)

method solve_exps_succ32I_scaffold methods recurs solve_exp solve_type uses add = (
  (rule step_exps_concat_word32_elI) |
  (rule step_exps_store_valI.succ2.storage_addr.xtract
        step_exps_store_valI.succ3.storage_addr.xtract, solve_type) |

  (rule step_exps_store_word_elI.succ3.storage.xtract step_exps_store_word_elI.succ2.storage.xtract
        step_exps_store_word_beI.succ3.storage.xtract step_exps_store_word_beI.succ2.storage.xtract,
   linarith,
   standard, 
   (recurs | succeed)) |

  (rule step_exps_store_word_elI.succ3.storage_addr.xtract step_exps_store_word_elI.succ2.storage_addr.xtract 
        step_exps_store_word_beI.succ3.storage_addr.xtract step_exps_store_word_beI.succ2.storage_addr.xtract,
   solve_type, linarith, standard, (recurs | succeed)) |

  (rule step_exps_store_memI.succ3.xtract step_exps_store_memI.succ2.xtract, 
   solve_exp, (recurs | succeed)) |

  (rule step_exps_cast64_concat32_elI, (rule add | linarith)) |

  (solve_expsI_scaffold recurs solve_exp solve_type add: add)
)

method solve_exps_succ32I uses add = (
  solve_exps_succ32I_scaffold \<open>solve_exps_succ32I add: add\<close> \<open>solve_exp_succ32I add: add\<close> solve_typeI 
    add: add
)

lemma step_exps_load_word32_elI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leadsto>* (ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply -
  by solve_exps_succ32I
 
lemmas step_exps_load_word32_el32I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word32_el64I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word32_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (storage_el32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))\<close>
  using assms apply -
  apply (solve_exps_succ32I, simp)+
  by solve_exps_succ32I

interpretation step_exps_store_word32_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el32 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 32
  apply standard
  using step_exps_store_word32_elI by blast

lemmas step_exps_store_word32_el32I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word32_el64I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word32_beI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leadsto>* (ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_exps_succ32I, simp)+
  unfolding xtract32_24_0[symmetric] by solve_exps_succ32I

lemma step_exps_store_word32_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (storage_be32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))\<close>
  using assms apply -
  apply (solve_exps_succ32I, simp)+
  by solve_exps_succ32I

interpretation step_exps_store_word32_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be32 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 32
  apply standard
  using step_exps_store_word32_beI by blast

\<comment> \<open>The 64 bit solver scaffold\<close>
method solve_exps_mem32I_scaffold methods recurs solve_exp solve_type uses add = ((*
  (rule step_exps_load_word32_el64I.word.word) | 
  (rule step_exps_load_word32_el64I.succ.word) |
  (rule step_exps_load_word32_el64I.plus.word) |

  (rule step_exps_load_word32_elI.word.word, linarith) |
  (rule step_exps_load_word32_elI.succ.word, linarith) |
  (rule step_exps_load_word32_elI.plus.word, linarith) |

  (rule step_exps_load_word32_el64_num_ltI.word, linarith) | 
  (rule step_exps_load_word32_el64_num_ltI.succ, linarith) | 
  (rule step_exps_load_word32_el64_num_ltI.plus, linarith) | 

  (rule step_exps_load_word32_el_num_ltI.word, linarith, linarith) | 
  (rule step_exps_load_word32_el_num_ltI.succ, linarith, linarith) | 
  (rule step_exps_load_word32_el_num_ltI.plus, linarith, linarith) | 

  (rule step_exps_load_word32_next_el64_num_ltI.plus.plus, linarith, linarith) |

  (rule step_exps_load_word32_be64I) | (rule step_exps_load_word32_beI, linarith) |*)

    (rule step_exps_store_word32_elI.val.plus.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_elI.val.plus.word, solve_type) |
    (rule step_exps_store_word32_elI.val.word.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_elI, solve_type) |
    (rule step_exps_store_word32_beI.val.plus.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_beI.val.plus.word, solve_type) |
    (rule step_exps_store_word32_beI, solve_type) |
                    
  (solve_exps_succ32I_scaffold recurs solve_exp solve_type add: add)
)

method solve_exps_mem32I uses add = (
  solve_exps_mem32I_scaffold \<open>solve_exps_mem32I add: add\<close> \<open>solve_exp_succ32I add: add\<close>
      solve_type_succ32I add: add
)

method solve_bil_mem32I uses add = (
  solve_bilI_scaffold \<open>solve_bil_mem32I add: add\<close> \<open>solve_exps_mem32I add: add\<close>
)


context bil_syntax
begin

method solve_prog_mem32I uses add decoder = (
  solve_progI_scaffold \<open>solve_bil_mem32I add: add\<close> decoder: decoder
)

end

end
