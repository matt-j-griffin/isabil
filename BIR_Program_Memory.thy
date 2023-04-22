theory BIR_Program_Memory
  imports BIR_Syntax
begin

type_synonym prog = \<open>word \<rightharpoonup> bil\<close>

(* TODO this may be faster if I first map to all available values then filter Sub name. 
ie (dom \<Pi>) ` \<lambda>p . the \<Pi> p = Sub name *)
definition
  find_labels :: \<open>prog \<Rightarrow> string \<Rightarrow> word set\<close> 
where 
  \<open>find_labels \<Pi> label = {Addr\<^sub>\<Pi>. \<Pi> Addr\<^sub>\<Pi> = Some (sub label)}\<close> 

definition
  find_label :: \<open>prog \<Rightarrow> string \<Rightarrow> word\<close> 
where 
  \<open>find_label \<Pi> label = ((Min (raw_val ` (find_labels \<Pi> label))) \<Colon> addr_size)\<close>
(*
fun
  stack_decode_bir :: \<open>program_memory \<Rightarrow> program \<Rightarrow> insn\<close>
where
  \<open>stack_decode_bir \<Pi> (_, w, _) = (
    case \<Pi> w of
      Some i \<Rightarrow> \<lparr> addr = w, size = (1 \<Colon> addr_size), code = stack_bir_to_bil RSP i \<rparr>
      | _ \<Rightarrow> no_insn
  )\<close>
*)(*
definition
  wf_program_addr_size :: \<open>nat \<Rightarrow> word \<Rightarrow> bool\<close>
where
  \<open>wf_program_addr_size addr_size w \<equiv> (wf_word w \<and> bits w = addr_size)\<close>


lemma wf_program_addr_simps: 
  assumes \<open>wf_program_addr_size addr_size w\<close>
    shows \<open>raw_val w < (2 ^ addr_size)\<close>
  using assms apply (cases w, auto)
  by (auto simp add: wf_program_addr_size_def)

lemma wf_program_addr_inj_on:
  assumes \<open>wf_program_addr_size addr_size w\<^sub>1\<close> and \<open>wf_program_addr_size addr_size w\<^sub>2\<close>
      and \<open>raw_val w\<^sub>1 = raw_val w\<^sub>2\<close>
    shows \<open>w\<^sub>1 = w\<^sub>2\<close>
  using assms by (auto simp add: wf_program_addr_size_def word.expand)
*)

(* TODO: With locale interpretations (interpretations within a locale) we could tidy up a lot more
  of the syntax. Primarily raw words/values and Vars*)
locale program_memory_syntax =
    fixes \<Pi> :: prog
      and \<Gamma> :: TypingContext

  assumes \<Pi>\<^sub>\<rho>_is_imm: \<open>\<And>w. w \<in> dom \<Pi> \<Longrightarrow> (\<Gamma> \<turnstile> w :: imm\<langle>addr_size\<rangle>)\<close>
      and \<Pi>\<^sub>\<iota>_is_ok: \<open>\<And>\<iota>. \<iota> \<in> ran \<Pi> \<Longrightarrow> (\<Gamma> \<turnstile> \<iota> is ok)\<close>
      and \<Pi>\<^sub>\<iota>_is_birinsn: \<open>\<And>\<iota>. \<iota> \<in> ran \<Pi> \<Longrightarrow> is_birinsn \<iota>\<close>

      and addr_size_gt_0: \<open>addr_size > 0\<close>

begin

lemma \<Pi>\<^sub>\<rho>_is_ok: 
  assumes \<open>w \<in> dom \<Pi>\<close>
    shows \<open>w is ok\<close>
  using assms \<Pi>\<^sub>\<rho>_is_imm typed_ok_word.elims(2) by blast 

text \<open>The set of program addresses in the program memory\<close>

abbreviation
  \<Pi>\<^sub>\<rho> :: \<open>word set\<close> 
where
  \<open>\<Pi>\<^sub>\<rho> \<equiv> dom \<Pi>\<close>

text \<open>The set of instructions in the program memory\<close>

abbreviation
  \<Pi>\<^sub>\<iota> :: \<open>bil set\<close> 
where
  \<open>\<Pi>\<^sub>\<iota> \<equiv> ran \<Pi>\<close>


fun
  decode :: \<open>program \<Rightarrow> insn \<Rightarrow> bool\<close> (infixr \<open>\<mapsto>\<^sub>b\<^sub>i\<^sub>l\<close> 91)
where
  \<open>(\<Delta>, w\<^sub>1, mem') \<mapsto>\<^sub>b\<^sub>i\<^sub>l insn = (w\<^sub>1 \<in> \<Pi>\<^sub>\<rho> \<and> insn = \<lparr> addr = w\<^sub>1, size = (1 \<Colon> addr_size), code = the (\<Pi> w\<^sub>1) \<rparr>)\<close>

fun 
  label_exp :: \<open>string \<Rightarrow> exp\<close> (\<open>@_\<close>)
where
  \<open>(@label) = (Val (Immediate (find_label \<Pi> label)))\<close>

(* TODO figure out how to fix vars in isar proofs *)
                 
sublocale bir_syntax
  where decode_pred = decode
    and label_exp = label_exp
  apply standard 
     apply auto
  subgoal
    apply (rule \<Pi>\<^sub>\<iota>_is_birinsn)
    by (rule ranI)
  by (rule addr_size_gt_0)


abbreviation
  step_pred_abbrev :: \<open>program \<Rightarrow> program \<Rightarrow> bool\<close> (infixr \<open>\<leadsto>\<^sub>b\<^sub>i\<^sub>l\<close> 90)
where
  \<open>step_pred_abbrev p p' \<equiv> step_pred p p'\<close>


lemma insn_always_bil': \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> \<Longrightarrow> is_birinsn bil\<close>
  using insn_always_bil select_convs(3) by metis

lemma insn_always_sz1: \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = w\<^sub>2, code = bil \<rparr> \<Longrightarrow> w\<^sub>2 = (1 \<Colon> addr_size)\<close>
  by simp

lemma \<Pi>_decode: 
  assumes \<open>w\<^sub>1 \<in> \<Pi>\<^sub>\<rho>\<close>
    shows \<open>(\<Delta>, w\<^sub>1, mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w\<^sub>1, size = (1 \<Colon> addr_size), code = the (\<Pi> w\<^sub>1) \<rparr>\<close>
  using assms by simp

(*
lemma inj_on_raw_prog_addrs: \<open>inj_on raw_val (dom \<Pi>)\<close>
  by (meson inj_onI program_addrs_wf wf_program_addr_inj_on)

lemma raw_prog_addr_lt_addr_size: \<open>(\<forall>x \<in> dom \<Pi>. raw_val x < (2 ^ addr_size))\<close>
  by (simp add: program_addrs_wf wf_program_addr_simps)

lemma finite_raw_prog_addrs: \<open>finite (raw_val ` dom \<Pi>)\<close>
  using raw_prog_addr_lt_addr_size finite_nat_set_iff_bounded by auto

lemma finite_prog_addrs:  \<open>finite (dom \<Pi>)\<close>
  using finite_raw_prog_addrs finite_image_iff inj_on_raw_prog_addrs by auto
*)

end

end
