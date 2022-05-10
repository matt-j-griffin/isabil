theory BIR_Program_Memory
  imports BIR_Syntax
begin

type_synonym program_memory = \<open>word \<rightharpoonup> birinsn\<close>

definition
  find_label_set :: \<open>program_memory \<Rightarrow> Id \<Rightarrow> word set\<close> 
where 
  \<open>find_label_set \<Pi> name = {Addr\<^sub>\<Pi>. \<Pi> Addr\<^sub>\<Pi> = Some (Sub name)}\<close>

definition
  find_label :: \<open>program_memory \<Rightarrow> Id \<Rightarrow> nat \<Rightarrow> word\<close> 
where 
  \<open>find_label \<Pi> name addr_size = Word (Min (raw_val ` find_label_set \<Pi> name)) addr_size\<close>

fun
  stack_decode_bir :: \<open>var \<Rightarrow> nat \<Rightarrow> program_memory \<Rightarrow> program \<Rightarrow> insn\<close>
where
  \<open>stack_decode_bir RSP addr_size \<Pi> (_, w, _) = (
    case \<Pi> w of
      Some i \<Rightarrow> \<lparr> addr = w, size = (1 \<Colon> addr_size), code = stack_bir_to_bil RSP i \<rparr>
      | _ \<Rightarrow> no_insn
  )\<close>

locale bir_program_memory = bir +
  fixes \<Pi> :: program_memory

  assumes program_addrs_wf: \<open>\<forall>x \<in> dom \<Pi>. wf_program_addr x\<close> 
      and find_label: \<open>(@label) = Val (Immediate (find_label \<Pi> label addr_size))\<close>
      and \<open>decode = stack_decode_bir RSP addr_size \<Pi>\<close>
begin

lemma inj_on_raw_prog_addrs: \<open>inj_on raw_val (dom \<Pi>)\<close>
  by (simp add: inj_onI program_addrs_wf wf_program_addr_inj_on)

lemma raw_prog_addr_lt_addr_size: \<open>(\<forall>x \<in> dom \<Pi>. raw_val x < (2 ^ addr_size))\<close>
  by (simp add: program_addrs_wf wf_program_addr_simps)

lemma finite_raw_prog_addrs: \<open>finite (raw_val ` dom \<Pi>)\<close>
  using raw_prog_addr_lt_addr_size finite_nat_set_iff_bounded by auto

lemma finite_prog_addrs:  \<open>finite (dom \<Pi>)\<close>
  using finite_raw_prog_addrs finite_image_iff inj_on_raw_prog_addrs by auto



end
