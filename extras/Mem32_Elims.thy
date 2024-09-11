theory Mem32_Elims
  imports Mem32
          Mem16_Elims
begin

\<comment> \<open>Little Endian\<close>

lemma step_exps_concat_word32_elE: 
  assumes major: \<open>\<Delta> \<turnstile> ((((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) \<copyright> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<copyright>
                   ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8) \<copyright> ext num \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0) 
              \<leadsto>* (Val v)\<close>
      and minor: \<open>v = ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0 \<Longrightarrow> P\<close>
    shows P
  using major apply (intro minor)
  by (solve_expsE, unfold xtract32)+

lemma step_exps_cast64_concat32_elE:
  assumes major: \<open>\<Delta> \<turnstile> extend:64[
   (((ext num \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24)  \<copyright> ext num \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<copyright>
      ext num \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8)  \<copyright> ext num \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0] \<leadsto>* (Val v)\<close>
      and caveat: \<open>num < 2 ^ 32\<close>
      and minor: \<open>v = (num \<Colon> 64) \<Longrightarrow> P\<close>
    shows P
  using major apply (intro minor)
  apply (solve_expsE, unfold xtract32)+
  apply solve_expsE
  apply simp
  unfolding xtract_31_0_63_0[OF caveat] by solve_expsE

method solve_exp_succ32E_scaffold methods recurs solve_type uses add = (
(*  (rule step_load_byteI.word.succ2    step_load_byteI.word.succ3    step_load_byteI.succ.succ2
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
*)
  (solve_expE_scaffold recurs solve_type add: add)
)

method solve_exp_succ32E uses add = (
  solve_exp_succ32E_scaffold \<open>solve_exp_succ32E add: add\<close> solve_typeI add: add
)

method solve_exps_succ32E_scaffold methods recurs solve_exp solve_type uses add = (
  (erule step_exps_concat_word32_elE) |(*
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
*)
  (*(rule step_exps_cast64_concat32_elE, (rule add | linarith)) |*)

  (solve_expsE_scaffold recurs solve_exp (*solve_type*) add: add)
)

method solve_exps_succ32E uses add = (
  solve_exps_succ32E_scaffold \<open>solve_exps_succ32E add: add\<close> \<open>solve_exp_succ32E add: add\<close> solve_typeI 
    add: add
)

lemma step_exps_load_word32_elE: 
  assumes major: \<open>\<Delta> \<turnstile> (storage_el32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leadsto>* (Val v')\<close>
      and caveat: \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and minor: \<open>v' = (ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0) \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (intro minor)
  by solve_exps_succ32E


lemmas step_exps_load_word32_el32I = step_exps_load_word32_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word32_el64I = step_exps_load_word32_elE[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_store_word32_elE:
  assumes major: \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u32 \<leftarrow> (num\<^sub>v \<Colon> 32) \<leadsto>* (Val v)\<close>
      and caveat: \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
      and minor: \<open>v = storage_el32 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32) \<Longrightarrow> P\<close>
    shows P
  using major caveat apply (intro minor)
  by (solve_exps_succ32E; simp)+

interpretation step_exps_store_word32_elE: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta> v P. \<lbrakk>\<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u32 \<leftarrow> e\<^sub>3 \<leadsto>* (Val v);
          v = storage_el32 v\<^sub>1 w\<^sub>2 v\<^sub>3 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P)\<close> 32
  apply standard
  using step_exps_store_word32_elE by blast
(*
lemmas step_exps_store_word32_el32I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_store_word32_el64I = step_exps_load_word32_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]
*)(*
\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word32_beI: 
  assumes \<open>1 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be32 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 32))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u32 \<leadsto>* (ext num\<^sub>v \<Colon> 32 \<sim> hi : 31 \<sim> lo : 0)\<close>
  using assms apply - 
  apply (solve_exps_succ32E, simp)+
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
*)
\<comment> \<open>The 64 bit solver scaffold\<close>
method solve_exps_mem32E_scaffold methods recurs solve_exp solve_type uses add = ((*
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

  (rule step_exps_load_word32_be64I) | (rule step_exps_load_word32_beI, linarith) |

    (rule step_exps_store_word32_elI.val.plus.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_elI.val.plus.word, solve_type) |
    (rule step_exps_store_word32_elI.val.word.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_elI, solve_type) |
    (rule step_exps_store_word32_beI.val.plus.xtract_sz, linarith, solve_type) |
    (rule step_exps_store_word32_beI.val.plus.word, solve_type) |
    (rule step_exps_store_word32_beI, solve_type) |*)
                    
  (solve_exps_succ32E_scaffold recurs solve_exp solve_type add: add)
)

method solve_exps_mem32E uses add = (
  solve_exps_mem32E_scaffold \<open>solve_exps_mem32E add: add\<close> \<open>solve_exp_succ32E add: add\<close>
      solve_type_succ32I add: add
)

method solve_bil_mem32E uses add = (
  solve_bilE_scaffold \<open>solve_bil_mem32E add: add\<close> \<open>solve_exps_mem32E add: add\<close>
)


context bil_syntax
begin

method solve_prog_mem32E uses add decoder = (
  solve_progE_scaffold \<open>solve_bil_mem32E add: add\<close> decoder: decoder
)

end

end
