theory Expression_Semantics
  imports Instruction_Syntax "Typing/Typing"
begin

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)
no_notation (ASCII) HOL.Not (\<open>~ _\<close> [40] 40)


function
  type :: \<open>val \<Rightarrow> Type\<close>
where
  \<open>type (_[(_ \<Colon> nat') \<leftarrow> _, sz]) = mem\<langle>nat',sz\<rangle>\<close> | 
  \<open>type (_ \<Colon> nat') = imm\<langle>nat'\<rangle>\<close> | 
  \<open>type (unknown[_]: t) = t\<close>
  subgoal for P x
    apply (rule val_exhaust[of x])
    apply simp_all
    using word_exhaust by blast
  by auto

termination by (standard, auto)

lemma type_mem_not_imm[simp]: \<open>type (mem[w \<leftarrow> v', sz]) \<noteq> imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
  by (metis Type.distinct(1) is_ok_word.cases type.simps(1))

lemma type_unknown_diff: 
  assumes \<open>type (unknown[str]: t') = t\<close>
    shows \<open>t = t'\<close>
  using assms unfolding type.simps by clarify

lemma type_unknown_mem_diff: 
  assumes \<open>type (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r', sz\<^sub>m\<^sub>e\<^sub>m'\<rangle>) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r' \<and> sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>m\<^sub>e\<^sub>m'\<close>
  using assms by (drule_tac type_unknown_diff, clarify) 


lemma typed_ok_type:
  assumes \<open>\<Gamma> \<turnstile> v :: t\<close>
    shows \<open>type v = t\<close>
  using assms by (rule typed_ok_val.elims, auto)
(*
lemma type_typed_ok:
  assumes \<open>type v = t\<close>
      and \<open>\<Gamma> is ok\<close> and \<open>t is ok\<close>
      and \<open>\<forall>w. v = Immediate w \<longrightarrow> w is ok\<close>
      and \<open>\<forall>mem sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r w v'. v = (mem[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])
              \<longrightarrow> (\<Gamma> \<turnstile> v' :: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (w is ok)\<close>
    shows \<open>\<Gamma> \<turnstile> v :: t\<close>
  using assms apply (drule_tac P=\<open>\<Gamma> \<turnstile> v :: t\<close> in type.elims, auto)
  subgoal for val nat
    apply (erule allE[of _ \<open>val \<Colon> nat\<close>])
    by (simp add: word'_is_ok word_constructor_val_def)
  .
*)
context word_constructor
begin

function
  succ :: \<open>'a \<Rightarrow> 'a\<close>
where
  \<open>succ (num \<Colon> sz) = (num \<Colon> sz) +\<^sub>b\<^sub>v (1 \<Colon> sz)\<close> |
  \<open>\<lbrakk>\<forall>num sz. w \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> succ w = undefined\<close>
  subgoal for P x
    apply (rule word_syntax_exhaust[of x])
    by blast+    
  by auto
termination
  by (standard, auto)

lemmas SUCC = local.succ.simps(1)
  
end

text \<open>Confirmation Report lemmas\<close>

function
  concat_en :: \<open>val \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>concat_en (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) be = ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |
  \<open>concat_en (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) el = ((num\<^sub>2 \<Colon> sz\<^sub>2) \<cdot> (num\<^sub>1 \<Colon> sz\<^sub>1))\<close> |
  \<open>concat_en (_ \<Colon> sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) _ = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (_ \<Colon> sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t) _ = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) be
    = (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>)\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) el
    = (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>)\<close> |
  \<open>\<lbrakk>type v\<^sub>1 = mem\<langle>_, _\<rangle> \<or> type v\<^sub>2 = mem\<langle>_, _\<rangle>\<rbrakk> \<Longrightarrow> concat_en v\<^sub>1 v\<^sub>2 _ = undefined\<close>
  subgoal for P x 
    apply (cases x)
    apply simp
    subgoal for v\<^sub>1 v\<^sub>2 en
      apply (cases en)
      apply simp_all
      subgoal
        apply (rule val_exhaust[of v\<^sub>1])
        apply simp_all
        subgoal
          apply (rule val_exhaust[of v\<^sub>2])
          apply simp_all
          subgoal for str t
            apply (cases t)
            apply simp_all
            by blast
          subgoal
            by (metis type.simps(1) word_exhaust)
          .
        subgoal for str t
          apply (cases t)
          subgoal
            apply (rule val_exhaust[of v\<^sub>2])
            apply simp_all
            subgoal for str' t'
              apply (cases t')
              apply simp_all
              by blast
            by (metis type.elims unknown_storage_neq word_storage_neq)
          using type.simps(3) by blast
        by (metis type.elims unknown_storage_neq word_storage_neq)
      subgoal
        apply (rule val_exhaust[of v\<^sub>1])
        apply simp_all
        subgoal
          apply (rule val_exhaust[of v\<^sub>2])
          apply simp_all
          subgoal for str t
            apply (cases t)
            apply simp_all
            by blast
          subgoal
            by (metis type.simps(1) word_exhaust)
          .
        subgoal for str t
          apply (cases t)
          subgoal
            apply (rule val_exhaust[of v\<^sub>2])
            apply simp_all
            subgoal for str' t'
              apply (cases t')
              apply simp_all
              by blast
            by (metis type.elims unknown_storage_neq word_storage_neq)
          using type.simps(3) by blast
        by (metis type.elims unknown_storage_neq word_storage_neq)
      .
    .
  by auto

termination by (standard, auto)


lemma concat_en_induct_is_ok[consumes 3, case_names BeWord ElWord WorkUnk UnkWord Unknown]:
  assumes \<open>v = concat_en v\<^sub>1 v\<^sub>2 en\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
      and be_word: \<open>\<And>num\<^sub>1 num\<^sub>2. \<lbrakk>v = ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2));
           \<Gamma> \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1)::val :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> (num\<^sub>2 \<Colon> sz\<^sub>2)::val :: imm\<langle>sz\<^sub>2\<rangle>\<rbrakk>
          \<Longrightarrow> P (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) be\<close>
      and el_word: \<open>\<And>num\<^sub>1 num\<^sub>2. \<lbrakk>v = ((num\<^sub>2 \<Colon> sz\<^sub>2) \<cdot> (num\<^sub>1 \<Colon> sz\<^sub>1));
           \<Gamma> \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1)::val :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> (num\<^sub>2 \<Colon> sz\<^sub>2)::val :: imm\<langle>sz\<^sub>2\<rangle>\<rbrakk>
          \<Longrightarrow> P (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) el\<close>
      and word_unk: \<open>\<And>str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t num\<^sub>l\<^sub>e\<^sub>f\<^sub>t. \<lbrakk>v = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            \<Gamma> \<turnstile> (num\<^sub>l\<^sub>e\<^sub>f\<^sub>t \<Colon> sz\<^sub>1)::val :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>)::val :: imm\<langle>sz\<^sub>2\<rangle>\<rbrakk>
          \<Longrightarrow> P (num\<^sub>l\<^sub>e\<^sub>f\<^sub>t \<Colon> sz\<^sub>1) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>) en\<close>
      and unk_word: \<open>\<And>str\<^sub>l\<^sub>e\<^sub>f\<^sub>t num\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t. \<lbrakk>v = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            v\<^sub>1 = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>; v\<^sub>2 = (num\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t \<Colon> sz\<^sub>2); \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<rbrakk>
          \<Longrightarrow> P (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>) (num\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t \<Colon> sz\<^sub>2) en\<close>
      and be_unknown: \<open>\<And>str\<^sub>l\<^sub>e\<^sub>f\<^sub>t str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t. \<lbrakk>v = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            v\<^sub>1 = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>; v\<^sub>2 = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<rbrakk>
          \<Longrightarrow> P (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>) en\<close>
      and el_unknown: \<open>\<And>str\<^sub>l\<^sub>e\<^sub>f\<^sub>t str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t. \<lbrakk>v = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            v\<^sub>1 = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>; v\<^sub>2 = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<rbrakk>
          \<Longrightarrow> P (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>1\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>2\<rangle>) en\<close>
    shows \<open>P v\<^sub>1 v\<^sub>2 en\<close>
using assms proof (induct v\<^sub>1 v\<^sub>2 en rule: concat_en.induct)
  case (1 num\<^sub>1 sz\<^sub>1' num\<^sub>2 sz\<^sub>2')
  then show ?case 
    apply (frule_tac word_typed_diff)
    apply (frule word_typed_diff[of _ _ _ sz\<^sub>2])
    apply clarify
    unfolding concat_en.simps by blast+
next
  case (2 num\<^sub>1 sz\<^sub>1' num\<^sub>2 sz\<^sub>2')
  then show ?case 
    apply (frule_tac word_typed_diff)
    apply (frule word_typed_diff[of _ _ _ sz\<^sub>2])
    apply clarify
    unfolding concat_en.simps by blast+
next
  case (3 num\<^sub>l\<^sub>e\<^sub>f\<^sub>t sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t en')
  then show ?case 
    apply (frule_tac word_typed_diff)
    apply (frule unknown_imm_typed_diff)
    apply clarify
    unfolding concat_en.simps by blast+
next
  case (4 str\<^sub>l\<^sub>e\<^sub>f\<^sub>t sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t uw sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t ux)
  then show ?case 
    apply (frule_tac word_typed_diff)
    apply (frule unknown_imm_typed_diff)
    apply clarify
    unfolding concat_en.simps by blast+
next
  case (5 str\<^sub>l\<^sub>e\<^sub>f\<^sub>t sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t)
  then show ?case 
    apply (frule_tac unknown_imm_typed_diff)
    apply (frule unknown_imm_typed_diff[of _ _ _ sz\<^sub>2])
    apply clarify
    unfolding concat_en.simps by blast+    
next
  case (6 str\<^sub>l\<^sub>e\<^sub>f\<^sub>t sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t)
  then show ?case 
    apply (frule_tac unknown_imm_typed_diff)
    apply (frule unknown_imm_typed_diff[of _ _ _ sz\<^sub>2])
    apply clarify
    unfolding concat_en.simps by blast+
next
  case (7 v\<^sub>1 uy uz v\<^sub>2 va vb vc)
  then show ?case by (simp add: typed_ok_type)
qed

lemma concat_en_is_ok:
  assumes \<open>v = concat_en v\<^sub>1 v\<^sub>2 en\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> v :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
using assms proof (induct rule: concat_en_induct_is_ok)
  case (BeWord num\<^sub>1 num\<^sub>2)
  then show ?case
    unfolding bv_concat.simps Immediate_simp apply clarify
    using T_INT TWF_WORD by simp
next
  case (ElWord num\<^sub>1 num\<^sub>2)
  then show ?case 
    unfolding bv_concat.simps Immediate_simp apply clarify
    apply (simp only: add.commute)
    unfolding T_INT TWF_WORD by simp   
qed simp_all

function
  load_byte :: \<open>val \<Rightarrow> word \<Rightarrow> val\<close>
where
  \<open>\<lbrakk>w\<^sub>m\<^sub>e\<^sub>m = w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, _]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = v\<^sub>m\<^sub>e\<^sub>m\<close> |
  \<open>\<lbrakk>w\<^sub>m\<^sub>e\<^sub>m \<noteq> w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> _, _]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = load_byte mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> |
  \<open>load_byte (unknown[str]: mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) _ = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<close> |
  \<open>type v = imm\<langle>_\<rangle> \<Longrightarrow> load_byte v _ = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for v w
      apply (rule val_exhaust[of v])
      apply auto
      using type.simps(2) apply blast
      subgoal for str t
        apply (cases t, auto)
        by (metis type.simps(3))
      by fastforce
    .
  apply simp_all
  apply (metis Type.distinct(1) type.cases type.simps(1) unknown_storage_neq word_storage_neq)
  by auto

termination 
  apply (relation "(\<lambda>p. size_class.size (fst p)) <*mlex*> {}")
  apply (rule wf_mlex, blast)
  unfolding storage_constructor_val_def
  by (rule mlex_less, simp)

lemma load_byte_is_ok:
  assumes \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (load_byte mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) :: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
using assms proof (induct mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r rule: load_byte.induct)
  case (1 w\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r mem v\<^sub>m\<^sub>e\<^sub>m uu)
  then show ?case 
    unfolding load_byte.simps apply simp
    apply (rule word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], simp)
    by (frule storage_typed_diff, simp)
next
  case (2 w\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r mem uv uw)
  then show ?case 
    unfolding load_byte.simps apply simp
    apply (erule typed_ok_val.elims(2))
    by auto
next
  case (3 str ux sz\<^sub>m\<^sub>e\<^sub>m uy)
  then show ?case 
    unfolding load_byte.simps 
    apply (frule_tac unknown_mem_typed_diff)
    by simp
next
  case (4 v uz va)
  then show ?case
    by (simp add: typed_ok_type)
qed


function
  load :: \<open>val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>v\<^sub>a\<^sub>l]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l _ = (
      load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>v\<^sub>a\<^sub>l]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    undefined     
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    undefined     
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
      let 
        v\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en;
        v\<^sub>l\<^sub>e\<^sub>f\<^sub>t = load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r
      in concat_en v\<^sub>l\<^sub>e\<^sub>f\<^sub>t v\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t en
  )\<close> |
  \<open>load (unknown[str]: _) _ sz\<^sub>v\<^sub>a\<^sub>l _ = unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle> \<close> |
  \<open>load (_ \<Colon> _) _ _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, simp)
    subgoal for v
      apply (rule val_exhaust[of v])
      apply auto
      by (metis gr0I linorder_less_linear)
    .
  by auto

termination
  apply (relation "(\<lambda>p. size_class.size (fst (snd (snd p)))) <*mlex*> (\<lambda>p. size_class.size (fst p)) <*mlex*> {}")
  by (simp_all add: wf_mlex mlex_less)


lemma load_is_ok:
  assumes \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>0 < sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>v = load mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en\<close>
    shows \<open>\<Gamma> \<turnstile> v :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
using assms proof (induct mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en arbitrary: v rule: load.induct)
  case (1 mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l w\<^sub>a\<^sub>d\<^sub>d\<^sub>r en)
  then show ?case
    unfolding load.simps apply clarify
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    apply (frule storage_typed_diff)
    by (rule load_byte_is_ok[of _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
next
  case (2 sz\<^sub>v\<^sub>a\<^sub>l sz\<^sub>m\<^sub>e\<^sub>m mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r en)
  then show ?case 
    unfolding load.simps apply clarify
    by auto
next
  case (3 sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r en)
  then show ?case 
    unfolding load.simps apply clarify
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    apply (frule storage_typed_diff)
    by (metis nat_dvd_not_less)
next
  case (4 sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r en)
  then show ?case     
    unfolding load.simps apply clarify
    apply simp (* takes a long time *)
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    apply (frule storage_typed_diff, clarify)
    apply (frule_tac v=v and v\<^sub>1=\<open>load_byte (mem[a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> and sz\<^sub>1=sz\<^sub>m\<^sub>e\<^sub>m
                 and v\<^sub>2=\<open>load (mem[a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en\<close> 
                 and sz\<^sub>2=\<open>sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m\<close> and en=en and \<Gamma>=\<Gamma> in concat_en_is_ok)
    apply (rule load_byte_is_ok[of _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r], blast)
    using dvd_minus_self apply blast
    by (metis le_add_diff_inverse nat_less_le)
next
  case (5 str uu uv sz\<^sub>v\<^sub>a\<^sub>l uw)
  then show ?case 
    unfolding load.simps apply clarify
    apply (rule T_UNKNOWN)
    apply (rule TWF_IMM, blast) 
    using typed_ok_val.simps(2) unknown_typed_diff by blast
next
  case (6 ux uy uz va)
  then show ?case by simp
qed

subsubsection \<open>Store\<close>

function
  store :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<comment> \<open>Big endian store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) be = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - 1) \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l'), sz\<^sub>m\<^sub>e\<^sub>m]
        in
          store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l' - 1) \<sim> lo : 0) be
  )\<close> |
  \<comment> \<open>Little endian store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) el = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>m\<^sub>e\<^sub>m - 1) \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m]
        in
          store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - 1) \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) el
  )\<close> |
  \<comment> \<open>Unknown store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>) en = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>), sz\<^sub>m\<^sub>e\<^sub>m] in
            store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l'\<rangle>) en
  )\<close> |
  \<comment> \<open>Byte store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; type v\<^sub>v\<^sub>a\<^sub>l = imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l _ = (
    case type v\<^sub>v\<^sub>a\<^sub>l of imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow> (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  (* Illegal cases *)
  \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; type v\<^sub>v\<^sub>a\<^sub>l = imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem _ v\<^sub>v\<^sub>a\<^sub>l _ = undefined\<close> |
  \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk> \<Longrightarrow> store mem _ _ _ = undefined\<close> |
  \<open>\<lbrakk>type val = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> store _ _ val _ = undefined\<close>|
  \<open>\<lbrakk>type mem = imm\<langle>_\<rangle>\<rbrakk> \<Longrightarrow> store mem _ _ _ = undefined\<close>
  subgoal
    for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en
      apply (cases \<open>type v\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
      apply (cases \<open>type v\<^sub>v\<^sub>a\<^sub>l\<close>, simp_all)
      subgoal for sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l
        apply (cases \<open>sz\<^sub>m\<^sub>e\<^sub>m = 0\<close>, simp_all)
        apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
        apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
        apply (rule linorder_neqE_nat, auto)
        apply (rule val_exhaust[of v\<^sub>m\<^sub>e\<^sub>m], auto)
        subgoal
          apply (rule val_exhaust[of v\<^sub>v\<^sub>a\<^sub>l], auto)
          subgoal by (cases en)
          .
        subgoal
          apply (rule val_exhaust[of v\<^sub>v\<^sub>a\<^sub>l], auto)
          subgoal by (cases en)
          .
        .
      .
    .
  by auto
termination
  apply (relation \<open>(\<lambda>(_,_,v\<^sub>v\<^sub>a\<^sub>l,_). case (type v\<^sub>v\<^sub>a\<^sub>l) of imm\<langle>sz\<rangle> \<Rightarrow> size_class.size sz) <*mlex*> {}\<close>)
  subgoal
    apply (rule wf_mlex)
    by blast
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv
    by simp
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv
    by simp
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv
    by simp
  .


(* this is not very good *)
lemma succ_is_judgement:
  assumes \<open>\<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> Immediate (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
  apply (rule word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r _])
  using assms apply auto
  unfolding Immediate_simp
  apply (frule word_typed_diff, clarify)
  unfolding T_INT by simp

lemma extract_word_is_ok: 
  assumes \<open>\<Gamma> \<turnstile> Immediate w\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
      and \<open>sz < sz\<^sub>v\<^sub>a\<^sub>l\<close> and \<open>sz > 0\<close>
    shows \<open>\<Gamma> \<turnstile> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - 1) \<sim> lo : sz :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l - sz\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz - 1) \<sim> lo : 0 :: imm\<langle>sz\<rangle>\<close>
  using assms sorry

(*
lemma store_is_ok_induct[consumes 6, case_names BigEndian LittleEndian Unknown Single]:
  assumes \<open>v = store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
      and \<open>0 < sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and big_endian: \<open>(\<And>sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r num. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l; type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
            P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - 1 \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) - 1 \<sim> lo : 0)) be;
            \<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> (Immediate w\<^sub>v\<^sub>a\<^sub>l) :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>
          \<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) be)\<close>
      and little_endian:\<open>(\<And>sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l; type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
            P (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m - 1 \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - 1 \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m)) el;
            \<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> (Immediate w\<^sub>v\<^sub>a\<^sub>l) :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>
          \<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) el)\<close>
      and unknown: \<open>(\<And>sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str t. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l; type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
            P (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>, sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m\<rangle> en;
            \<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> (unknown[str]: t)::val :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>
          \<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r unknown[str]: t en)\<close>
      and single: \<open>(\<And>mem num v\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; v = mem[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m];
            \<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)::val :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>
          \<rbrakk> \<Longrightarrow> P mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) v\<^sub>v\<^sub>a\<^sub>l en)\<close>
  shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en\<close>
using assms proof (induct mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en rule: store.induct)
  case (1 mem uu sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l w\<^sub>a\<^sub>d\<^sub>d\<^sub>r num)
  show ?case 
    apply (rule big_endian)
    sledgehammer
  using "1.prems"
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    subgoal for num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r'
      using "1.prems"(2) apply clarify
      apply (frule storage_typed_diff, clarify)
      apply (rule_tac big_endian)
      using "1.hyps"(1) apply blast
      using "1.hyps"(2) apply blast
      apply (rule typed_ok_type[of \<Gamma>], blast)
      apply (rule "1.hyps"(3))
      apply blast+
      subgoal by (metis "1.hyps"(1) "1.hyps"(2) "1.prems"(1) store.simps(1))
      subgoal
        using "1.prems"(3)
        apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
        unfolding Immediate_simp
        apply (drule word_typed_diff, clarify)
        apply (rule T_MEM_val)
        subgoal 
          unfolding TWF_WORD
          by (meson is_ok_word.simps typed_ok_val.simps(1))
        subgoal 
          using "1.hyps"(1) by blast
        apply blast
        subgoal 
          by (metis "1.hyps"(1) "1.hyps"(2) "1.prems"(4) diff_diff_cancel extract_word_is_ok(1) less_Suc0 nless_le not_less_eq zero_less_diff)
        .
      subgoal
        apply (rule succ_is_judgement)
        by (rule "1.prems"(3))
      subgoal 
        apply (rule extract_word_is_ok(2))
        apply (rule "1.prems"(4))
        using "1.hyps"(1) "1.prems"(5) diff_less apply blast
        using "1.hyps"(2) zero_less_diff by blast
      subgoal 
        using "1.hyps"(2) by linarith
      subgoal
        using "1.prems"(6) dvd_minus_self by blast
      using big_endian apply blast
      using little_endian apply blast
      using "1.prems"(9) apply blast
      using "1.prems"(10) apply blast
      apply blast
      using "1.prems"(3) apply blast
      using "1.prems"(4) by blast
      .    
    sorry
next
  case (2 mem uv sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l w\<^sub>a\<^sub>d\<^sub>d\<^sub>r num)
  then show ?case sorry
next
  case (3 mem uw sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str en)
  then show ?case sorry
next
  case (4 mem ux sz\<^sub>m\<^sub>e\<^sub>m v\<^sub>v\<^sub>a\<^sub>l w\<^sub>a\<^sub>d\<^sub>d\<^sub>r uy)
  then show ?case sorry
next
  case (5 mem uz v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l va vb sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case sorry
next
  case (6 mem vc vd ve vf sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case sorry
next
  case (7 val vg vh vi vj vk)
  then show ?case 
next
  case (8 mem vl vm vn vo)
  then show ?case 
    by (metis Type.distinct(1) typed_ok_type)
qed

next
  case (8 mem ux sz\<^sub>v\<^sub>a\<^sub>l uy uz va vb vc vd sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.distinct(1) is_ok_word.cases type.simps(1) typed_ok_type)
next
  case (9 mem ve sz\<^sub>v\<^sub>a\<^sub>l vf vg vh sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.inject(2) typed_ok_type nat_dvd_not_less)
next
  case (10 mem vi vj vk vl vm sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.inject(2) dvd_pos_nat less_numeral_extra(3) typed_ok_type)
next
  case (11 mem vn vo vp vq vr)
  then show ?case 
    by (metis Type.distinct(1) typed_ok_type)
qed

  case (1 sz\<^sub>m\<^sub>e\<^sub>m' sz\<^sub>v\<^sub>a\<^sub>l' mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l)
  show ?case

next
  case (2 sz\<^sub>m\<^sub>e\<^sub>m' sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l)
  show ?case 
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    subgoal for num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r'
      using "2.prems"(2) apply clarify
      apply (frule storage_typed_diff, clarify)
      apply (rule little_endian[of _ _ _ _])
      using "2.hyps"(1) apply blast
      using "2.hyps"(2) apply blast
      unfolding type.simps apply blast
      apply (rule "2.hyps"(3))
      apply blast+
      subgoal
        using "2.hyps"(1) "2.hyps"(2) "2.prems"(1) store.simps(2) by presburger
      subgoal
        using "2.prems"(3)
        apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
        unfolding Immediate_simp
        apply (drule word_typed_diff, clarify)
        apply (rule T_MEM_val)
        subgoal 
          unfolding TWF_WORD
          by (meson is_ok_word.simps typed_ok_val.simps(1))
        subgoal 
          using "2.hyps"(1) by blast
        apply blast
        subgoal 
          apply (rule extract_word_is_ok(2))
          using "2.hyps"(1) "2.hyps"(2) "2.prems"(4) by blast+
        .
      subgoal
        apply (rule succ_is_judgement)
        by (rule "2.prems"(3))
      subgoal 
        apply (rule extract_word_is_ok(1))
        apply (rule "2.prems"(4)) 
        using "2.hyps"(2) apply blast
        using "2.hyps"(1) by blast
      subgoal 
        using "2.hyps"(2) by linarith
      subgoal
        using "2.prems"(6) dvd_minus_self by blast
      using big_endian apply blast
      using little_endian apply blast
      using "2.prems"(9) apply blast
      using "2.prems"(10) apply blast
      apply blast
      using "2.prems"(3) apply blast
      using "2.prems"(4) by blast
    .
next
  case (3 sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l)
  show ?case 
    using "3.prems"(2) apply (drule_tac unknown_mem_typed_diff', clarify)
    apply (rule_tac big_endian)
    apply simp
    using "3.hyps"(2) apply auto[1]
    apply simp
    subgoal
      apply (rule "3.hyps"(3))
      apply simp
      apply auto[1]
      apply simp
      apply simp
      subgoal by (metis "3.hyps"(1) "3.hyps"(2) "3.prems"(1) store.simps(3))
      subgoal
        using "3.prems"(3)
        apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
        unfolding Immediate_simp
        apply (drule word_typed_diff, clarify)
        apply (rule T_MEM_val)
        subgoal 
          unfolding TWF_WORD
          by (meson is_ok_word.simps typed_ok_val.simps(1))
        subgoal 
          using "3.hyps"(1) by blast
        apply blast
        subgoal 
          by (metis "3.hyps"(1) "3.hyps"(2) "3.prems"(4) diff_diff_cancel extract_word_is_ok(1) less_Suc0 nat_less_le not_less_eq zero_less_diff)
        .
      subgoal
        apply (rule succ_is_judgement)
        using "3.prems"(3) by blast
      subgoal
        apply (rule extract_word_is_ok(2))
        apply (rule "3.prems"(4))
        using "3.hyps"(1) "3.prems"(5) diff_less apply blast
        using "3.hyps"(2) zero_less_diff by blast
      subgoal 
        using "3.hyps"(2) by linarith
      subgoal
        using "3.prems"(6) dvd_minus_self by blast
      using big_endian apply blast
      using little_endian apply blast
      using "3.prems"(9) apply blast
      using "3.prems"(10) by blast
    apply blast
    using "3.prems"(3) apply blast
    using "3.prems"(4) by blast
next
  case (4 sz\<^sub>m\<^sub>e\<^sub>m' sz\<^sub>v\<^sub>a\<^sub>l str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l)
  show ?case 
    using "4.prems"(2) apply (drule_tac unknown_mem_typed_diff', clarify)
    apply (rule little_endian[of _ _ _ _])
    using "4.hyps"(1) apply auto[1]
    using "4.hyps"(2) apply auto[1]
    apply simp
    subgoal
      apply clarify
      apply (rule "4.hyps"(3))
      apply simp
      apply auto[1]
      apply simp
      subgoal 
        using "4.hyps"(1) "4.hyps"(2) "4.prems"(1) store.simps(4) by presburger
      subgoal
        using "4.prems"(3)
        apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
        unfolding Immediate_simp
        apply (drule word_typed_diff, clarify)
        apply (rule T_MEM_val)
        subgoal 
          unfolding TWF_WORD
          by (meson is_ok_word.simps typed_ok_val.simps(1))
        subgoal 
          using "4.hyps"(1) by blast
        using "4.prems"(1) apply auto[1]
        subgoal 
          apply (rule extract_word_is_ok(2))
          using "4.hyps"(1) "4.hyps"(2) "4.prems"(4) by blast+
        .
      subgoal
        apply (rule succ_is_judgement)
        using "4.prems"(3) by blast
      subgoal
        apply (rule extract_word_is_ok(1))
        apply (rule "4.prems"(4))
        using "4.hyps"(2) apply auto[1]
        using "4.hyps"(1) "4.prems"(4) diff_less by blast
      subgoal 
        using "4.hyps"(2) by linarith
      subgoal
        using "4.prems"(6) dvd_minus_self by blast
      using big_endian apply blast
      using little_endian apply blast
      using "4.prems"(9) apply blast
      using "4.prems"(10) by blast
    apply blast
    using "4.prems"(3) apply blast
    using "4.prems"(4) by blast
next
  case (5 sz\<^sub>m\<^sub>e\<^sub>m' sz\<^sub>v\<^sub>a\<^sub>l mem w\<^sub>m\<^sub>e\<^sub>m v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str t en)
  show ?case
    apply (rule word_exhaust[of w\<^sub>m\<^sub>e\<^sub>m], clarify)
    subgoal for num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r'
      using "5.prems"(2) apply clarify
      apply (frule storage_typed_diff, clarify)
      apply (rule "5.prems"(9))
      using "5.hyps"(1) apply blast
      using "5.hyps"(2) apply blast
      subgoal
        apply (rule typed_ok_type[of \<Gamma>])
        by blast
      subgoal
        apply (rule "5.hyps"(3))
        apply blast+
        subgoal by (metis "5.hyps"(1) "5.hyps"(2) "5.prems"(1) store.simps(5))        
        subgoal
          using "5.prems"(3) apply clarify
          apply (rule word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
          unfolding Immediate_simp 
          apply (drule word_typed_diff, clarify)
          apply (rule storage_add_is_ok)
          apply blast
          unfolding TWF_WORD apply (metis "5.prems"(3) TWF_WORD T_INT word_constructor_val_def)
          by (metis "5.prems"(4) TWF_IMM typed_ok_val.simps(2) typed_ok_val.simps(3) unknown_typed_diff)
        subgoal
          apply (rule succ_is_judgement)
          using "5.prems"(3) by blast
        subgoal
          by (metis "5.hyps"(2) "5.prems"(4) "5.prems"(6) TWF_IMM add_cancel_right_right diff_0_eq_0 linordered_semidom_class.add_diff_inverse nat_dvd_not_less type.simps(3) typed_ok_type typed_ok_val.simps(2))
        subgoal
          using "5.hyps"(2) zero_less_diff by blast
        subgoal
          using "5.prems"(6) dvd_minus_self by blast
      using big_endian apply blast
      using little_endian apply blast
      using "5.prems"(9) apply blast
      using "5.prems"(10) by blast
    apply blast
    using "5.prems"(3) apply blast
    using "5.prems"(4) by blast
  .
next
  case (6 mem uu sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str' t en)
  show ?case
    using "6.hyps"(1-3)
    using "6.prems"(2)
    apply (drule_tac unknown_mem_typed_diff, clarify)
    apply (rule_tac "6.prems"(9))
    apply blast+
    subgoal
      apply (rule typed_ok_type[of \<Gamma>])
      by blast
    subgoal
      apply (rule "6.hyps"(4))
      apply blast+
      subgoal by (metis "6.hyps"(2) "6.prems"(1) store.simps(6))
      subgoal
        using "6.prems"(3)
        apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
        unfolding Immediate_simp 
        apply (drule word_typed_diff, clarify)
        apply (rule storage_add_is_ok)
        apply blast
        unfolding TWF_WORD apply (metis TWF_WORD T_INT word_constructor_val_def) 
        by simp
      subgoal
        apply (rule succ_is_judgement)
        using "6.prems"(3) by blast
      subgoal by auto
      subgoal
        using zero_less_diff by blast
      subgoal
        by (simp add: "6.prems"(6))
      using big_endian apply blast
      using little_endian apply blast
      using "6.prems"(9) apply blast
      using "6.prems"(10) by blast
    apply blast
    using "6.prems"(3) apply blast
    using "6.prems"(4) by blast
next
  case (7 mem uv sz\<^sub>m\<^sub>e\<^sub>m' w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en)
  show ?case 
    using "7.prems"(1-6) "7.hyps"
    apply clarify
    apply (rule word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], clarify)
    unfolding Immediate_simp 
    apply (frule word_typed_diff, clarify)
    apply (frule typed_ok_type)
    apply (subgoal_tac \<open>sz\<^sub>m\<^sub>e\<^sub>m' = sz\<^sub>m\<^sub>e\<^sub>m\<close>, clarify)
    apply (rule "7.prems"(10))
    apply blast+
    using store.simps(7) apply blast
    apply blast
    unfolding T_INT apply blast+
    using Type.inject(2) by metis 
next
  case (8 mem ux sz\<^sub>v\<^sub>a\<^sub>l uy uz va vb vc vd sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.distinct(1) is_ok_word.cases type.simps(1) typed_ok_type)
next
  case (9 mem ve sz\<^sub>v\<^sub>a\<^sub>l vf vg vh sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.inject(2) typed_ok_type nat_dvd_not_less)
next
  case (10 mem vi vj vk vl vm sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (metis Type.inject(2) dvd_pos_nat less_numeral_extra(3) typed_ok_type)
next
  case (11 mem vn vo vp vq vr)
  then show ?case 
    by (metis Type.distinct(1) typed_ok_type)
qed


lemma store_is_ok:
  assumes \<open>v = store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
      and \<open>0 < sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
    shows \<open>\<Gamma> \<turnstile> v :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
using assms proof (induct rule: store_is_ok_induct)
  case (Single mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l)
  then show ?case
    apply clarify
    apply (rule storage_add_is_ok)
    apply blast+
    unfolding TWF_WORD apply simp
    by blast
qed
*)

subsubsection \<open>Expression evaluation\<close>

context word_constructor
begin

primrec 
  operator_unop :: \<open>UnOp \<Rightarrow> ('a \<Rightarrow> 'a)\<close>
where
  \<open>operator_unop Not = bv_negation\<close> |
  \<open>operator_unop Neg = bv_uminus\<close>

primrec
  operator_lop :: \<open>LOp \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)\<close>
where
  \<open>operator_lop Eq = (=\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Neq = (\<noteq>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Lt = (<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Le = (\<le>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Slt = (<\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Sle = (\<le>\<^sub>s\<^sub>b\<^sub>v)\<close>

primrec
  operator_aop :: \<open>AOp \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)\<close>
where
  \<open>operator_aop Plus = (+\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Minus = (-\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Times = (*\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Divide = (div\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SDivide = (div\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Mod = (%\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SMod = (%\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop And = (&\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Or = (|\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Xor = (xor\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop LShift = (<<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop RShift = (>>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop ARShift = (>>>\<^sub>b\<^sub>v)\<close>
end

context val_syntax
begin

function 
  eval_unop :: \<open>UnOp \<Rightarrow> 'a \<Rightarrow> 'a\<close>
where
  \<open>eval_unop _ (unknown[str]: t) = unknown[str]: t\<close> |
  \<open>eval_unop uop (num \<Colon> sz) = (operator_unop uop) ((num \<Colon> sz))\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_unop _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for uop v
      apply (rule val_syntax_exhaust[of v])
      by force+
    .
  by auto
termination by (standard, auto)

function 
  eval_binop :: \<open>BinOp \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
where
  \<open>eval_binop (AOp _) (unknown[str]: t) _ = unknown[str]: t\<close> |
  \<open>eval_binop (LOp _) (unknown[str]: _) _ = unknown[str]: imm\<langle>1\<rangle>\<close> |
  \<open>\<lbrakk>\<forall>str t. v \<noteq> unknown[str]: t\<rbrakk> \<Longrightarrow> eval_binop (AOp _) v (unknown[str]: t) = unknown[str]: t\<close> |
  \<open>\<lbrakk>\<forall>str t. v \<noteq> unknown[str]: t\<rbrakk> \<Longrightarrow> eval_binop (LOp _) v (unknown[str]: _) = unknown[str]: imm\<langle>1\<rangle>\<close> |
  \<open>eval_binop (AOp aop) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)
      = (operator_aop aop (num\<^sub>1 \<Colon> sz\<^sub>1) ((num\<^sub>2 \<Colon> sz\<^sub>2)))\<close> |
  \<open>eval_binop (LOp lop) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)
      = (operator_lop lop (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |
  \<open>\<lbrakk>(\<forall>str t. v\<^sub>1 \<noteq> unknown[str]: t); (\<forall>str t. v\<^sub>2 \<noteq> unknown[str]: t);
    (\<forall>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. v\<^sub>1 \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) \<or> v\<^sub>2 \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2))
   \<rbrakk> \<Longrightarrow> eval_binop _ v\<^sub>1 v\<^sub>2 = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for binop v\<^sub>1 v\<^sub>2
      apply (cases binop)
      subgoal for aop
        apply (rule val_syntax_exhaust[of v\<^sub>1])
        apply (rule val_syntax_exhaust[of v\<^sub>2])
        by force+
      subgoal for lop
        apply (rule val_syntax_exhaust[of v\<^sub>1])
        apply (rule val_syntax_exhaust[of v\<^sub>2])
        by force+
      .
    .
  by auto

termination by (standard, auto)

end


(* these are not generic *)

lemma operator_unop_typed_ok:
  assumes \<open>\<Gamma> \<turnstile> (num \<Colon> sz)::val :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (operator_unop uop (num \<Colon> sz))::val :: imm\<langle>sz\<rangle>\<close>
  using assms by (cases uop, auto)

lemma eval_unop_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v::val :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_unop uop v :: imm\<langle>sz\<rangle>\<close>
  using assms 
  apply (rule_tac val_exhaust[of v], auto)
  subgoal for num sz'
    apply (frule word_typed_diff, clarify)
    by (rule operator_unop_typed_ok, clarify)
  .

lemma operator_aop_typed_ok: \<open>\<Gamma> \<turnstile> operator_aop aop (num\<^sub>1 \<Colon> sz) (num\<^sub>2 \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  apply (cases aop)
  sorry

lemma eval_aop_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1::val :: imm\<langle>sz\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2::val :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_binop (AOp aop) v\<^sub>1 v\<^sub>2 :: imm\<langle>sz\<rangle>\<close>
  using assms 
  apply (rule_tac val_exhaust[of v\<^sub>1], auto)
  subgoal for num\<^sub>1 sz\<^sub>1
    apply (frule word_typed_diff, clarify)
    apply (rule_tac val_exhaust[of v\<^sub>2], safe)
    subgoal for num\<^sub>2 sz\<^sub>2
      apply (frule word_typed_diff[of _ _ sz\<^sub>2 _], clarify)
      unfolding eval_binop.simps by (rule operator_aop_typed_ok)
    by auto
  .

lemma eval_lop_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1::val :: imm\<langle>sz\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2::val :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_binop (LOp lop) v\<^sub>1 v\<^sub>2 :: imm\<langle>1\<rangle>\<close>
  sorry


function 
  eval_cast :: \<open>Cast \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> val\<close>
where 
  \<open>eval_cast _ sz (unknown[str]: _) = unknown[str]: imm\<langle>sz\<rangle>\<close> |
  \<open>eval_cast low sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>eval_cast high sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz - 1) \<sim> lo : (sz - sz')\<close> |
  \<open>eval_cast extend sz' (num \<Colon> sz) = exts (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>eval_cast pad sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_cast _ _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for cast sz' v
      apply (rule val_exhaust[of v])
      subgoal for num sz
        apply (cases cast)
        by force+
      apply force
      by fastforce
    .
  by auto

termination by (standard, auto)

lemma eval_cast_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v::val :: imm\<langle>sz'\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_cast cast sz v :: imm\<langle>sz\<rangle>\<close>
  using assms sorry

function 
  eval_if :: \<open>val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val\<close>
where 
  \<open>eval_if (unknown[str]: _) v _ = unknown[str]: (type v)\<close> |
  \<open>eval_if true v _ = v\<close> |
  \<open>eval_if false _ v = v\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); v \<noteq> true; v \<noteq> false\<rbrakk> \<Longrightarrow> eval_if v _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>1 v\<^sub>2 v\<^sub>3
      apply (rule val_exhaust[of v\<^sub>1])
      by blast+
    .
  by auto

termination by (standard, auto)

lemma eval_if_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1::val :: imm\<langle>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2::val :: t\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>3::val :: t\<close>
    shows \<open>\<Gamma> \<turnstile> eval_if v\<^sub>1 v\<^sub>2 v\<^sub>3 :: t\<close>
  using assms sorry


function 
  eval_extract :: \<open>nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_extract sz\<^sub>1 sz\<^sub>2 (unknown[str]: t) = unknown[str]:imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>\<close> |
  \<open>eval_extract sz\<^sub>1 sz\<^sub>2 (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_extract _ _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for sz\<^sub>1 sz\<^sub>2 v
      apply (rule val_exhaust[of v])
      by force+
    .
  by auto
termination by (standard, auto)

lemma eval_extract_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v::val :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_extract sz\<^sub>1 sz\<^sub>2 v :: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>\<close>
  using assms sorry

function 
  eval_concat :: \<open>val \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_concat (unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) (_ \<Colon> sz\<^sub>2) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) (unknown[_]: imm\<langle>sz\<^sub>2\<rangle>) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (_ \<Colon> sz\<^sub>1) (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> |
  \<open>\<lbrakk>type v\<^sub>1 = mem\<langle>_,_\<rangle> \<or> type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_concat v\<^sub>1 v\<^sub>2 = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>1 v\<^sub>2
      apply (rule val_exhaust[of v\<^sub>1])
      subgoal
        apply (rule val_exhaust[of v\<^sub>2])
        apply force
        subgoal for _ t
          apply (cases t)
          apply blast
          by (metis type.simps(3))
        subgoal for _ w
          apply (rule word_exhaust[of w])
          by (metis type.simps(1))
        .
      subgoal for _ t
        apply (cases t)
        subgoal
          apply (rule val_exhaust[of v\<^sub>2])
          apply blast
          subgoal for _ t'
            apply (cases t')
            apply blast
            by (metis type_unknown_diff)
          by (metis type.simps(1) word_exhaust)        
        by (metis type.simps(3))
      by (metis type.simps(1) word_exhaust)
    .
  by auto
termination by (standard, auto)

lemma concat_en_eq_be: \<open>concat_en v1 v2 be = eval_concat v1 v2\<close>
  by (induct v1 v2 rule: eval_concat.induct, auto)

lemma concat_en_eq_el: \<open>concat_en v2 v1 el = eval_concat v1 v2\<close>
  apply (induct v1 v2 rule: eval_concat.induct, auto)
  using concat_en.simps(7) by blast+

lemma typed_imm_exhaust:
    fixes v :: val  
  assumes \<open>\<Gamma> \<turnstile> v :: imm\<langle>sz\<rangle>\<close>
      and \<open>\<And>num. v = (num \<Colon> sz) \<Longrightarrow> Q\<close>
      and \<open>\<And>str. v = unknown[str]: imm\<langle>sz\<rangle> \<Longrightarrow> Q\<close>
    shows Q
  apply (rule val_exhaust[of v])
  subgoal for num sz
    apply (rule assms(2)[of num])
    using assms(1) apply clarify
    using word_typed_diff by blast
  subgoal for str t
    apply (rule assms(3)[of str])
    using assms(1) apply clarify
    using unknown_typed_diff by blast
  subgoal
    using assms(1) by auto
  .

lemma eval_concat_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1::val :: imm\<langle>sz\<^sub>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2::val :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_concat v\<^sub>1 v\<^sub>2 :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms apply (rule_tac typed_imm_exhaust[of _ v\<^sub>1], blast)
  subgoal for num\<^sub>1
    apply (rule typed_imm_exhaust[of _ v\<^sub>2], blast)
    subgoal for num\<^sub>2
      apply clarify
      unfolding eval_concat.simps by fastforce
    subgoal for str
      apply clarify
      unfolding eval_concat.simps by fastforce
    .
  subgoal for str
    apply (rule typed_imm_exhaust[of _ v\<^sub>2], blast)
    subgoal for num\<^sub>2
      apply clarify
      unfolding eval_concat.simps by fastforce
    subgoal for str
      apply clarify
      unfolding eval_concat.simps by fastforce
    .
  .

function 
  eval_load :: \<open>val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>eval_load _ (unknown[str]: imm\<langle>_\<rangle>) sz\<^sub>v\<^sub>a\<^sub>l _ = unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close> |
  \<open>eval_load v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) sz\<^sub>v\<^sub>a\<^sub>l en = load v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) sz\<^sub>v\<^sub>a\<^sub>l en\<close> |
  \<open>\<lbrakk>type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_load _ v\<^sub>2 _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for _ v\<^sub>2
      apply (rule val_exhaust[of v\<^sub>2])
      apply blast
      subgoal for _ t
        apply (cases t)
        apply blast
        using type.simps(3) by blast
      by (metis storage_constructor_val_def type.elims unknown_constructor_val_def val.distinct(5))
    .
  by auto
termination by (standard, auto)

lemma eval_load_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1::val :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2::val :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_load v\<^sub>1 v\<^sub>2 sz en :: imm\<langle>sz\<rangle>\<close>
  using assms sorry

function 
  eval_store :: \<open>val \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_store v\<^sub>1 (unknown[str]: imm\<langle>_\<rangle>) _ _ = unknown[str]: (type v\<^sub>1)\<close> |
  \<open>eval_store v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) en v\<^sub>3 = store v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) v\<^sub>3 en\<close> |
  \<open>\<lbrakk>type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_store _ v\<^sub>2 _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for _ v\<^sub>2
      apply (rule val_exhaust[of v\<^sub>2])
      apply blast
      subgoal for _ t
        apply (cases t)
        apply blast
        by (metis type.simps(3))
      apply simp
      by (metis Type.exhaust type_mem_not_imm)
    .
  by auto
termination by (standard, auto)

lemma eval_store_typed_ok: 
  assumes \<open>\<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>\<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> eval_store v\<^sub>1 v\<^sub>2 en v\<^sub>3 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms(2) apply (rule_tac val_exhaust[of v\<^sub>2])
  apply safe
  subgoal
    unfolding eval_store.simps
    sorry
  subgoal for str t
    unfolding eval_store.simps apply (cases t)
    using assms(1) apply simp
    apply (metis t_is_ok typed_ok_type typed_ok_val.simps(2) unknown_typed_diff)
    using unknown_typed_diff by blast
  subgoal 
    using storage_not_imm by blast
  .

function
  eval_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val\<close>
where
  \<open>eval_exp _ (Val v) = v\<close> |
  \<open>eval_exp \<Delta> (name' :\<^sub>t t) = (if (name' :\<^sub>t t) \<in> dom \<Delta> then (the (\<Delta> (name' :\<^sub>t t))) else (unknown[[]]: t))\<close> | (* TODO a string method to describe ids*)
  \<open>eval_exp \<Delta> (UnOp uop e) = eval_unop uop (eval_exp \<Delta> e)\<close> |
  \<open>eval_exp \<Delta> (BinOp e\<^sub>1 binop e\<^sub>2) = eval_binop binop (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Cast cast sz e) = eval_cast cast sz (eval_exp \<Delta> e)\<close> |
  \<open>eval_exp \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (eval_exp (\<Delta> (var \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = eval_if (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) (eval_exp \<Delta> e\<^sub>3)\<close> |
  \<open>eval_exp \<Delta> (extract:sz\<^sub>1:sz\<^sub>2[e]) = (eval_extract sz\<^sub>1 sz\<^sub>2 (eval_exp \<Delta> e))\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1 @ e\<^sub>2) = eval_concat (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1[e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l) = eval_load (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz\<^sub>v\<^sub>a\<^sub>l en\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l \<leftarrow>  e\<^sub>3) = eval_store (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) en (eval_exp \<Delta> e\<^sub>3)\<close>
  subgoal for P x
    apply (cases x)
    subgoal for \<Delta> e
      apply (rule exp_exhaust[of e])
      apply auto
      apply (simp add: word_constructor_exp_def)
      apply (simp add: unknown_constructor_exp_def)
      by (simp add: storage_constructor_exp_def)
    .
  unfolding var_constructor_exp_def append_exp_def by auto
termination
  apply standard
  unfolding append_exp_def
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  apply (rule mlex_less, force)+
  done

lemma eval_exp_true[simp]: \<open>eval_exp \<Delta> true = true\<close>
  by (simp add: true_exp_def)

lemma eval_exp_false[simp]: \<open>eval_exp \<Delta> false = false\<close>
  by (simp add: false_exp_def)

lemma eval_exp_word[simp]: \<open>eval_exp \<Delta> (num \<Colon> sz) = (num \<Colon> sz)\<close>
  by (simp add: word_constructor_exp_def)

lemma eval_exp_unknown[simp]: \<open>eval_exp \<Delta> (unknown[str]: t) = (unknown[str]: t)\<close>
  by (simp add: unknown_constructor_exp_def)

lemma eval_exp_storage[simp]: \<open>eval_exp \<Delta> (v[w \<leftarrow> v', sz]) = (v[w \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def)

lemma eval_exp_val: \<open>v' = eval_exp \<Delta> (Val v) \<Longrightarrow> v = v'\<close>
  by simp

lemma cast_typed_diff: \<open>\<Gamma> \<turnstile> cast:sz[e] :: imm\<langle>sz'\<rangle> \<Longrightarrow> sz' = sz\<close>
  using typed_ok_exp.simps(18) by metis

lemma load_typed_diff: \<open>\<Gamma> \<turnstile> e\<^sub>1[e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<rangle> \<Longrightarrow> sz = sz\<^sub>v\<^sub>a\<^sub>l\<close>
  by (metis typed_ok_exp.simps(4))

lemma store_typed_diff: \<open>\<Gamma> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l \<leftarrow> e\<^sub>3 :: mem\<langle>sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
  oops

definition 
  wfnew :: \<open>BIL_Syntax.var list \<Rightarrow> (BIL_Syntax.var \<Rightarrow> val option) \<Rightarrow> bool\<close>
where
  \<open>wfnew \<Gamma> \<Delta> = (\<forall>var \<in> dom \<Delta>. \<Gamma> \<turnstile> (the (\<Delta> var)) :: (var_type var))\<close>

lemma var_type_t[simp]: \<open>var_type (id' :\<^sub>t t) = t\<close>
  by (simp add: var_constructor_var_def)

lemma allInE:
  assumes major: "\<forall>x\<in> Q. P x" and minor: "P x \<Longrightarrow> R" and \<open>x \<in> Q\<close>
  shows R
  using assms by simp

lemma typed_ok_val_reduce: "((id' :\<^sub>t t') # \<Gamma>) \<turnstile> val::val :: t \<Longrightarrow> \<Gamma> \<turnstile> val :: t"
  by (induct rule: typed_ok_val.induct, auto)

lemma typed_ok_val_extend: "\<Gamma> \<turnstile> val :: t \<Longrightarrow> id' \<notin> dom\<^sub>\<Gamma> \<Gamma> \<Longrightarrow> t' is ok \<Longrightarrow> ((id' :\<^sub>t t') # \<Gamma>) \<turnstile> val::val :: t"
  by (induct \<Gamma> val t rule: typed_ok_val.induct, auto)
  
lemma wfnew_extend:
  assumes \<open>wfnew \<Gamma> \<Delta>\<close>
      and \<open>\<Gamma> \<turnstile> val :: t\<close> and \<open>id' \<notin> dom\<^sub>\<Gamma> \<Gamma>\<close>
    shows \<open>wfnew ((id' :\<^sub>t t) # \<Gamma>) (\<Delta>((id' :\<^sub>t t) \<mapsto> val))\<close>
  using assms unfolding wfnew_def apply clarify
  subgoal for var val'
    apply (cases \<open>(id' :\<^sub>t t) = var\<close>, auto)
    subgoal 
      using t_is_ok typed_ok_val_extend by blast
    subgoal
      apply (erule allInE[of _ _ var])
      apply auto
      apply (rule typed_ok_val_extend, auto)
      using t_is_ok by blast
    .
  .


lemma typed_eval_exp_induct_internal[consumes 3, case_names Val VarIn VarNotIn Load Store AOp LOp UnOp 
                                            Cast Let ITE Extract Concat]: 
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>v = eval_exp \<Delta> e\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
      and val: \<open>\<And>\<Gamma> \<Delta> v t. \<lbrakk>\<Gamma> \<turnstile> v :: t; t = type v; wfnew \<Gamma> \<Delta>\<rbrakk> \<Longrightarrow> P (Val v) \<Gamma> t \<Delta> v\<close>
      and var_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<in> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; \<Gamma> \<turnstile> the (\<Delta> (name :\<^sub>t t)) :: t; 
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> (the (\<Delta> (name :\<^sub>t t)))\<close>
      and var_not_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<notin> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok;
            \<Gamma> \<turnstile> ((unknown[[]]: t)::val) :: t;
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> ((unknown[[]::string]: t)::val)\<close>
      and load: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2); wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_load (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz en)\<close>
      and store: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; sz > 0;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2); 
            P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>3); wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_store (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) en (eval_exp \<Delta> e\<^sub>3))\<close>
      and aop: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 aop sz. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_binop (AOp aop) (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
      and lop: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 lop sz. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> (eval_binop (LOp lop) (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
      and uop: \<open>\<And>\<Gamma> \<Delta> t e uop sz. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_unop uop (eval_exp \<Delta> e))\<close>
      and cast: \<open>\<And>\<Gamma> \<Delta> t e sz sz' cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>;
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (cast:sz[e]) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_cast cast sz (eval_exp \<Delta> e))\<close>
      and let1: \<open>\<And>\<Gamma> \<Delta> t name t' e\<^sub>1 e\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: t'; ((name :\<^sub>t t') # \<Gamma>) \<turnstile> e\<^sub>2 :: t;
            P e\<^sub>1 \<Gamma> t' \<Delta> (eval_exp \<Delta> e\<^sub>1);
            wfnew \<Gamma> \<Delta>; name \<notin> dom\<^sub>\<Gamma> \<Gamma>; 
            (\<Gamma> \<turnstile> eval_exp \<Delta> e\<^sub>1 :: t' \<Longrightarrow> wfnew ((name :\<^sub>t t') # \<Gamma>) (\<Delta>((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) \<and>
            P e\<^sub>2 ((name :\<^sub>t t') # \<Gamma>) t (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2))
           \<rbrakk> \<Longrightarrow> P (Let (name :\<^sub>t t') e\<^sub>1 e\<^sub>2) \<Gamma> t \<Delta> (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close>
      and ite: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> t \<Delta> (eval_exp \<Delta> e\<^sub>2); P e\<^sub>3 \<Gamma> t \<Delta> (eval_exp \<Delta> e\<^sub>3)
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> (eval_if (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) (eval_exp \<Delta> e\<^sub>3))\<close>
      and extract': \<open>\<And>\<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            wfnew \<Gamma> \<Delta>; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> \<Delta> (eval_extract sz\<^sub>1 sz\<^sub>2 (eval_exp \<Delta> e))\<close>
      and concat: \<open>\<And>\<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; 
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2);
            wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (e\<^sub>1 @ e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> (eval_concat (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
    shows \<open>P e \<Gamma> t \<Delta> v\<close>
using assms(1-3) proof (induct \<Delta> e arbitrary: \<Gamma> \<Delta> v t rule: eval_exp.induct)
  case (1 uu v')
  then show ?case 
    apply (drule_tac eval_exp_val, clarify)
    apply (rule val)
    unfolding typed_ok_exp.simps apply blast+
    using typed_ok_type apply blast
    by blast
next
  case (2 \<Delta> name' t')
  then show ?case 
    apply (drule_tac var_typed_diff, clarify)
    apply (cases \<open>(name' :\<^sub>t t) \<in> dom \<Delta>\<close>)
    subgoal
      unfolding eval_exp.simps apply simp_all
      apply (rule var_in)
      apply blast+
      apply (metis var_type_t wfnew_def)
      by (simp_all add: var_constructor_exp_def var_constructor_var_def) (*bad*)

    subgoal
      unfolding eval_exp.simps apply simp_all
      apply (rule var_not_in)
      by (simp_all add: var_constructor_exp_def var_constructor_var_def) (*bad*)
    .
next
  case (3 \<Delta> uop e)
  show ?case 
    using 3(2-) unfolding eval_exp.simps apply clarify
    apply (cases t, clarify)
    subgoal for sz
      unfolding typed_ok_exp.simps apply (rule uop)
      apply blast+
      apply (rule 3(1))
      by blast+
    subgoal
      by simp
    .
next
  case (4 \<Delta> e\<^sub>1 binop e\<^sub>2)
  show ?case 
    using 4(3-) unfolding eval_exp.simps apply clarify
    apply (cases t)
    subgoal for sz
      apply (cases binop)
      subgoal for aop
        apply clarify
        unfolding typed_ok_exp.simps
        apply (rule aop)
        apply blast+
        subgoal 
          apply (rule 4(1))
          by blast+
        subgoal 
          apply (rule 4(2))
          by blast+
        .
      subgoal for lop
        apply (cases \<open>sz = 1\<close>)
        subgoal
          apply clarify
          unfolding typed_ok_exp.simps
          apply clarify
          apply (rule lop)
          apply blast+
          subgoal
            apply (rule 4(1))
            by blast+
          subgoal 
            apply (rule 4(2))
            by blast+
          .
        subgoal 
          using typed_ok_exp.simps(10) by blast
        .
      .
    subgoal by simp
    .    
next
  case (5 \<Delta> cast sz e)
  show ?case 
    using 5(2-) apply (cases t)
    subgoal for sz'
      unfolding eval_exp.simps apply clarify
      apply (frule cast_typed_diff, clarify)
      apply (cases cast, safe) 
      unfolding typed_ok_exp.simps apply safe
      subgoal
        apply (rule cast)
        apply blast+
        apply (rule 5(1))
        by blast+
      subgoal
        apply (rule cast)
        apply blast+
        apply (rule 5(1))
        by blast+
      subgoal
        apply (rule cast)
        apply blast+
        apply (rule 5(1))
        by blast+
      subgoal
        apply (rule cast)
        apply blast+
        apply (rule 5(1))
        by blast+
      .
    subgoal by simp
    .
next
  case (6 \<Delta> var e\<^sub>1 e\<^sub>2)
  show ?case 
    using 6(3-) unfolding eval_exp.simps apply clarify
    apply (rule var_exhaust[of var], clarify)
    unfolding typed_ok_exp.simps 
    subgoal for id t
      apply (rule let1, blast+)
      subgoal by (rule 6(1), blast+)
      apply blast+
      subgoal 
        apply (subgoal_tac \<open>wfnew ((id :\<^sub>t t) # \<Gamma>) (\<Delta>((id :\<^sub>t t) \<mapsto> eval_exp \<Delta> e\<^sub>1))\<close>)
        subgoal
          apply safe
          by (rule 6(2), blast+)
        subgoal
          by (rule wfnew_extend, blast+)
        .
      .
    .
next
  case (7 \<Delta> e\<^sub>1 e\<^sub>2 e\<^sub>3)
  show ?case 
    using 7(4-) unfolding typed_ok_exp.simps eval_exp.simps apply clarify
    apply (rule ite)
    apply blast+
    subgoal
      apply (rule 7(1))
      by blast+
    subgoal
      apply (rule 7(2))
      by blast+
    subgoal
      apply (rule 7(3))
      by blast+
    .
next
  case (8 \<Delta> sz\<^sub>1 sz\<^sub>2 e)
  show ?case 
    using 8(2-) unfolding eval_exp.simps apply (cases t)
    subgoal for sz
      apply (cases \<open>sz = sz\<^sub>1 - sz\<^sub>2 + 1\<close>)
      subgoal
        apply clarify
        unfolding typed_ok_exp.simps apply clarify
        apply (rule extract')
        apply blast+
        by (rule "8.hyps", blast+) 
      subgoal 
        using typed_ok_exp.simps(23) by blast
      .
    subgoal by simp
  .
next
  case (9 \<Delta> e\<^sub>1 e\<^sub>2)
  show ?case 
    using 9(3-) unfolding eval_exp.simps apply (cases t)
    subgoal for sz
      apply clarify
      unfolding typed_ok_exp.simps apply clarify
      subgoal for sz\<^sub>1 sz\<^sub>2
        apply (cases \<open>sz = sz\<^sub>1 + sz\<^sub>2\<close>)
        subgoal 
          apply (rule concat, blast+)
          subgoal by (rule 9(1), blast+)
          subgoal by (rule 9(2), blast+)
          by blast
        subgoal by blast
        .
      .
    subgoal by simp
    .
next
  case (10 \<Delta> e\<^sub>1 e\<^sub>2 en sz\<^sub>v\<^sub>a\<^sub>l)
  show ?case 
    using 10(3-) unfolding eval_exp.simps apply (cases t)
    subgoal for sz
      apply clarify
      apply (frule load_typed_diff)
      apply clarify
      unfolding typed_ok_exp.simps apply clarify
      apply (rule load, blast+)
      subgoal by (rule 10(1), blast+)
      subgoal by (rule 10(2), blast+)
      by blast
    subgoal by simp
    .
next
  case (11 \<Delta> e\<^sub>1 e\<^sub>2 en sz\<^sub>v\<^sub>a\<^sub>l e\<^sub>3)
  show ?case 
    using 11(4-) unfolding eval_exp.simps apply (cases t)
    subgoal by simp
    subgoal for sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
      apply clarify
      unfolding typed_ok_exp.simps apply clarify
      apply (rule store, blast+)
      subgoal by (rule 11(1), blast+)
      subgoal by (rule 11(2), blast+)
      subgoal by (rule 11(3), blast+)
      by blast
    .
qed

lemma eval_exp_typed_ok':
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>v = eval_exp \<Delta> e\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>\<Gamma> \<turnstile> v :: t\<close>
using assms proof (induct e \<Gamma> t \<Delta> v rule: typed_eval_exp_induct_internal)
  case (Load \<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    by (rule_tac eval_load_typed_ok, blast+)
next
  case (Store \<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)
  then show ?case 
    by (rule_tac eval_store_typed_ok, blast+)
next
  case (AOp \<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 aop sz)
  then show ?case 
    by (rule_tac eval_aop_typed_ok, blast+)
next
  case (LOp \<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 lop sz)
  then show ?case 
    by (rule_tac eval_lop_typed_ok, blast+)
next
  case (UnOp \<Gamma> \<Delta> t e uop sz)
  then show ?case 
    by (rule_tac eval_unop_typed_ok, blast)
next
  case (Cast \<Gamma> \<Delta> t e sz sz' cast)
  then show ?case 
    by (rule_tac eval_cast_typed_ok, blast+)
next
  case (Let \<Gamma> \<Delta> t name t' e\<^sub>1 e\<^sub>2)
  show ?case 
    using Let(1-5)
    apply (frule_tac Let(6))
    apply auto
    using typed_ok_val_reduce by blast
next
  case (ITE \<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3)
  then show ?case 
    by (rule_tac eval_if_typed_ok, blast+)
next
  case (Extract \<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 sz e)
  then show ?case 
    by (rule_tac eval_extract_typed_ok, blast+)
next
  case (Concat \<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2)
  then show ?case 
    by (rule_tac eval_concat_typed_ok, blast+)
qed simp_all


lemma eval_exp_typed_ok:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>\<Gamma> \<turnstile> (eval_exp \<Delta> e) :: t\<close>
  apply (rule eval_exp_typed_ok'[of _ _ _ \<open>eval_exp \<Delta> e\<close>])
  using assms by auto

(*
lemma typed_eval_exp_induct[consumes 3, case_names Val VarIn VarNotIn LoadUnkMem LoadUnkAddr Load
                                                   Store StoreUnkAddr AOpUnkLeft AOp AOpUnkRight
                                                   LOpUnkLeft LOp LOpUnkRight UnOpUnk UnOp
                                                   UnkWideningCast UnkNarrowingcast UnsignedCast
                                                   SignedCast HighCast LowCast Let
                                                   IteUnk IteTrue IteFalse ExtractUnk Extract
                                                   ConcatUnkLeft Concat ConcatUnkRight]:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>v = eval_exp \<Delta> e\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
      and val: \<open>\<And>\<Gamma> \<Delta> v t. \<lbrakk>\<Gamma> \<turnstile> v :: t; t = type v; wfnew \<Gamma> \<Delta>\<rbrakk> \<Longrightarrow> P (Val v) \<Gamma> t \<Delta> v\<close>
      and var_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<in> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; \<Gamma> \<turnstile> the (\<Delta> (name :\<^sub>t t)) :: t; 
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> (the (\<Delta> (name :\<^sub>t t)))\<close>
      and var_not_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<notin> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok;
            \<Gamma> \<turnstile> ((unknown[[]]: t)::val) :: t;
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> ((unknown[[]::string]: t)::val)\<close>
      and load: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2); wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_load (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz en)\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v'. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>2 = Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>;
            v = load v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz en                
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m str mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v'. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz w\<^sub>a\<^sub>d\<^sub>d\<^sub>r. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz mod sz\<^sub>m\<^sub>e\<^sub>m = 0; sz > 0;
            v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            \<Gamma> \<turnstile> v\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; v\<^sub>2 = Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>3; wfnew \<Gamma> \<Delta>;
            v = store v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>3 sz en
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz str. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz mod sz\<^sub>m\<^sub>e\<^sub>m = 0; sz > 0;
            v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            \<Gamma> \<turnstile> v\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>3; wfnew \<Gamma> \<Delta>;
            v = unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>  
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz w\<^sub>1 w\<^sub>2. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = Immediate w\<^sub>2;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = Immediate (operator_aop aop w\<^sub>1 w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz w\<^sub>1 str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 lop sz str. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>1\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 w\<^sub>2 lop sz. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = Immediate w\<^sub>2;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = Immediate (operator_lop lop w\<^sub>1 w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 lop sz str. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>1\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v v' t e uop sz str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            v' = eval_exp \<Delta> e; v' = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: imm\<langle>sz\<rangle>;
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v v' t e uop sz w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            v' = eval_exp \<Delta> e; v' = Immediate w; v = Immediate ((operator_unop uop) w);
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' str cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz'; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = unknown[str]: imm\<langle>sz'\<rangle>;
            v = unknown[str]: imm\<langle>sz\<rangle>; cast = Unsigned \<or> cast = Signed
           \<rbrakk> \<Longrightarrow> P (Cast cast sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' str cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = unknown[str]: imm\<langle>sz'\<rangle>; sz > 0;
            v = unknown[str]: imm\<langle>sz\<rangle>; cast = Low \<or> cast = High
           \<rbrakk> \<Longrightarrow> P (Cast cast sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz';
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (unsigned:sz[e]) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz'; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (Cast Signed sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; sz > 0; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (bits w - 1) \<sim> lo : (bits w - sz))
           \<rbrakk> \<Longrightarrow> P (Cast High sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; sz > 0; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (Cast Low sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t name t' e\<^sub>1 e\<^sub>2 v\<^sub>1. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: t'; \<Gamma> \<turnstile> v\<^sub>1 :: t'; ((name :\<^sub>t t') # \<Gamma>) \<turnstile> v :: t;
            P e\<^sub>1 \<Gamma> t' \<Delta> v\<^sub>1; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v = (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> v\<^sub>1)) e\<^sub>2);
            wfnew \<Gamma> \<Delta>; name \<notin> dom\<^sub>\<Gamma> \<Gamma>; wfnew ((name :\<^sub>t t') # \<Gamma>) (\<Delta>((name :\<^sub>t t') \<mapsto> v\<^sub>1));
            P e\<^sub>2 ((name :\<^sub>t t') # \<Gamma>) t (\<Delta> ((name :\<^sub>t t') \<mapsto> v\<^sub>1)) v
           \<rbrakk> \<Longrightarrow> P (Let (name :\<^sub>t t') e\<^sub>1 e\<^sub>2) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = unknown[str]: imm\<langle>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = unknown[str]: t;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = Immediate true;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = v\<^sub>2;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = Immediate false;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = v\<^sub>3;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> str v v' t sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            t = imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>; wfnew \<Gamma> \<Delta>; v' = eval_exp \<Delta> e; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v';
            v' = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> w v v' t sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            t = imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>; wfnew \<Gamma> \<Delta>; v' = eval_exp \<Delta> e; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'; 
            v' = Immediate w; v = Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 w\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = Immediate w\<^sub>1;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v\<^sub>2 = Immediate w\<^sub>2; v = Immediate (w\<^sub>1 \<cdot> w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = Immediate w\<^sub>1;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; v = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
    shows \<open>P e \<Gamma> t \<Delta> v\<close>
using assms(1-3) proof (induct e \<Gamma> t \<Delta> v rule: typed_eval_exp_induct_internal)
  case (Val \<Gamma> \<Delta> v t)
  then show ?case 
    using assms(4) by auto
next
  case (VarIn \<Gamma> \<Delta> v t name)
  then show ?case 
    using assms(5) by auto
next
  case (VarNotIn \<Gamma> \<Delta> v t name)
  then show ?case 
    using assms(6) by auto    
next
  case (Load \<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)
  then show ?case 
    using assms(7) apply (auto simp add: Let_def)
    apply (frule typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>, auto)
    using assms(8) by (metis typing_expression_exp_implies_eval_exp)
next
  case (Store \<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)
  then show ?case 
    apply (frule_tac e=e\<^sub>1 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>3 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>)
    apply (simp_all del: store.simps add: Let_def)
    using assms(9) typed_ok_type apply (metis Store.hyps(8) Type.simps(6) )
    apply (frule typed_ok_type)
    using assms(10) by simp
next
  case (AOp \<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 aop sz)
  then show ?case 
    apply (frule_tac e=e\<^sub>1 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, simp_all)
    using assms(11, 12) apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>, simp_all)
    using assms(13) by (simp add: AOp.hyps(6))
next
  case (LOp \<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 lop sz)
  then show ?case 
    apply (frule_tac e=e\<^sub>1 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, simp_all)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>, simp_all)
    using LOp.hyps(1) LOp.hyps(3) assms(15) apply auto[1]
    apply (metis LOp.hyps(1) LOp.hyps(3) assms(16) typing_expression_exp_implies_eval_exp)
    using assms(14) by auto
next
  case (UnOp \<Gamma> \<Delta> v t e uop sz)
  then show ?case 
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>, simp_all)
    defer
    apply (meson UnOp.hyps(3) assms(17) typing_expression_exp_implies_eval_exp)
    using assms(18) by simp
next
  case (UnsignedCast \<Gamma> \<Delta> v t e sz sz')
  then show ?case 
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    apply (simp_all del: s_extract_word.simps extract_word.simps)
    defer
    using assms(19) apply auto[1]
    using assms(21) One_nat_def by presburger
next
  case (SignedCast \<Gamma> \<Delta> v t e sz sz')
  then show ?case
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    apply (simp_all del: s_extract_word.simps extract_word.simps)
    defer
    using assms(19) apply auto[1]
    using assms(22) One_nat_def by presburger
next
  case (HighCast \<Gamma> \<Delta> v t e sz sz')
  then show ?case 
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    apply (simp_all del: s_extract_word.simps extract_word.simps)
    defer
    using assms(20) apply auto[1]
    using assms(23) One_nat_def by presburger
next
  case (LowCast \<Gamma> \<Delta> v t e sz sz')
  then show ?case 
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    apply (simp_all del: s_extract_word.simps extract_word.simps)
    defer
    using assms(20) apply auto[1]
    by (simp add: assms(24))
next
  case (Let \<Gamma> \<Delta> v t name t' e\<^sub>1 e\<^sub>2)
  then show ?case 
    by (meson assms(25) typing_expression_exp_implies_eval_exp_short wf\<Delta>_extend)
next
  case (ITE \<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3)
  then show ?case 
    apply (simp add: Let_def)
    apply (frule_tac e=e\<^sub>1 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>3 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>, auto)
    apply (simp add: assms(27))
    defer
    apply (frule typing_expression_exp_implies_eval_exp, blast+)
    apply (simp add: typed_ok_type assms(26))
    apply (frule_tac typing_immediate_value_not_true_false, blast)
    using assms(28) by auto
next
  case (Extract \<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 sz e)
  then show ?case 
    apply (frule_tac e=e in typing_expression_exp_implies_eval_exp_short, blast)
    apply (cases \<open>eval_exp \<Delta> e\<close>)
    using assms(30) apply (simp add: Extract.hyps(6))
    using assms(29) apply auto[1]
    using \<Gamma>_val_imm_not_storage by blast
next
  case (Concat \<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2)
  then show ?case 
    apply (frule_tac e=e\<^sub>1 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (frule_tac e=e\<^sub>2 in typing_expression_exp_implies_eval_exp_short, blast)
    apply (simp add: Let_def)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>1\<close>)
    apply (simp_all del: concat.simps)
    defer
    using assms(31) apply (frule_tac typed_ok_type, simp)
    apply (cases \<open>eval_exp \<Delta> e\<^sub>2\<close>)   
    apply (simp_all del: concat.simps)
    apply (simp add: assms(32))
    using assms(33) typing_val_immediate by auto
qed

lemma \<Gamma>_exp_type_implies_type_t:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
    shows \<open>type (eval_exp \<Delta> e) = t\<close>
  using assms apply (drule_tac \<Delta>=\<Delta> in typing_expression_exp_implies_eval_exp, auto)
  by (simp add: typed_ok_type)

(*
lemma let_substitute_Let_size_less: 
    \<open>size_class.size (Let var e\<^sub>1 e\<^sub>2) > size_class.size ([(eval_exp \<Delta> e\<^sub>1)\<sslash>var] e\<^sub>2)\<close>
  apply auto
  apply (induct e\<^sub>1, auto)
  apply (induct e\<^sub>2, auto)
  apply (metis add.commute add_less_mono add_mono_thms_linordered_field(1) less_Suc_eq)
  using less_Suc_eq let_substitute_val_size_eq by presburger+

termination eval_exp
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (auto simp add: wf_mlex mlex_prod_def)
  using let_substitute_Let_size_less by simp
*)
*)
function
  step_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto> _\<close> 401)
where
  \<open>(_ \<turnstile> (Val v) \<leadsto> _) = False\<close> |
  \<open>\<lbrakk>\<forall>v. e \<noteq> (Val v)\<rbrakk> \<Longrightarrow> (\<Delta> \<turnstile> e \<leadsto> e') = (
    e \<noteq> e' \<and>
    eval_exp \<Delta> e = eval_exp \<Delta> e'
  )\<close>
  subgoal for P x
    apply (cases x)
    subgoal for \<Delta> e\<^sub>1 e\<^sub>2
      apply (cases \<open>\<exists>v. e\<^sub>1 = (Val v)\<close>)
      by blast+
    .
  by auto
termination by (standard, auto)

lemma STEP_NOT_EQ: \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e)\<close>
  by (induct e, auto)

lemma STEP_NOT_REDUCTION: 
  assumes \<open>eval_exp \<Delta> e \<noteq> eval_exp \<Delta> e'\<close>
    shows \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e')\<close>
  using assms by (induct e, auto)

lemma STEP_NOT_VAL: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<leadsto> e')\<close>
  by simp

lemma STEP_IMPLIES_NOT_VAL: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>e \<noteq> Val v\<close>
  using assms by auto

lemma STEP_NEXT: 
  assumes \<open>eval_exp \<Delta> e = eval_exp \<Delta> e'\<close>
      and \<open>e \<noteq> e'\<close> and \<open>\<forall>v. e \<noteq> Val v\<close>
    shows \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
  using assms by (induct e, auto)

lemma VAR_IN:
  assumes \<open>((id' :\<^sub>t t), v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (Val v)\<close>
  using assms by auto

lemma VAR_IN_WORD:
  assumes \<open>((id' :\<^sub>t t), (num \<Colon> sz)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (num \<Colon> sz)\<close>
  using assms by auto

lemma VAR_IN_TRUE:
  assumes \<open>(id' :\<^sub>t t, true) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>\<Delta> \<turnstile> id' :\<^sub>t t \<leadsto> true\<close>
  unfolding true_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_FALSE:
  assumes \<open>(id' :\<^sub>t t, false) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>\<Delta> \<turnstile> id' :\<^sub>t t \<leadsto> false\<close>
  unfolding false_exp_def using assms by (rule VAR_IN)

lemma VAR_IN_STORAGE:
  assumes \<open>((id' :\<^sub>t t), v[w \<leftarrow> v', sz]) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> (v[w \<leftarrow> v', sz])\<close>
  using assms by auto

lemma VAR_IN_UNKNOWN:
  assumes \<open>((id' :\<^sub>t t), (unknown[str]: t)) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> unknown[str]: t\<close>
  using assms by auto

lemma VAR_UNKNOWN:
  assumes \<open>(id' :\<^sub>t t) \<notin> dom \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (id' :\<^sub>t t) \<leadsto> unknown['''']: t\<close>
  using assms by auto

lemma LOAD_STEP_ADDR:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1[e\<^sub>2', ed]:usz)\<close>  
  using assms by (cases e\<^sub>2, auto)

lemma LOAD_STEP_MEM:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma LOAD_STEP_MEM_word:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (e\<^sub>1'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma LOAD_BYTE:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (Val v')\<close>
  by auto

lemma LOAD_BYTE_word:  \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> (num\<^sub>v \<Colon> sz), sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> (num\<^sub>v \<Colon> sz)\<close>
  by auto

lemma LOAD_BYTE_FROM_NEXT:
  assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<rangle>\<close>
  shows \<open>\<Delta> \<turnstile> (v[(num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz])[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz)\<close>
  using assms apply auto
  subgoal 
    unfolding storage_constructor_exp_def storage_constructor_val_def by auto
  subgoal
    apply (rule val_exhaust[of v])
    apply simp_all
    by (metis Type.inject(2) load.simps(1) type.simps(1) word_exhaust)
  .

lemma LOAD_UN_ADDR: \<open>\<Delta> \<turnstile> e\<^sub>1[unknown[str]: imm\<langle>sz'\<rangle>, ed]:usz \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by auto

lemma LOAD_UN_MEM: \<open>\<Delta> \<turnstile> ((unknown[str]: t)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz) \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by auto

lemma LOAD_WORD_BE:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> 
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> 
  using assms apply (rule_tac val_exhaust[of v])
  subgoal by auto
  subgoal by auto
  subgoal for mem w v'
    apply (rule word_exhaust[of w], auto)
    using concat_en_eq_be by blast
  .

lemma LOAD_WORD_EL:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> 
    shows \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms apply (rule_tac val_exhaust[of v])
  subgoal by auto
  subgoal by auto
  subgoal for mem w v'
    apply (rule word_exhaust[of w], auto)
    using concat_en_eq_el by blast
  .

lemma STORE_STEP_VAL:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> 
  using assms by (cases e\<^sub>3, auto)

lemma STORE_STEP_ADDR:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>2, auto) 

lemma STORE_STEP_ADDR_word:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz')) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (v\<^sub>3 \<Colon> sz'))\<close> 
  using assms STORE_STEP_ADDR word_constructor_exp_def by presburger

lemma STORE_STEP_MEM:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>1, auto) 

lemma STORE_WORD_BE:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms apply auto
  apply (rule_tac val_exhaust[of val])
  by auto
  
lemma STORE_WORD_EL:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type val = imm\<langle>sz\<rangle>\<close>
      and \<open>e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<leadsto> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  using assms apply auto
  apply (rule_tac val_exhaust[of val])
  by auto

lemma STORE_VAL:
  assumes \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>type v' = imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms by (cases ed, auto)
  
lemma STORE_UN_ADDR:
  assumes \<open>type v = t\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>, ed]:usz' \<leftarrow> (Val v')) \<leadsto> (unknown[str]: t)\<close>
  using assms by (cases t, auto)

lemma LET_STEP:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> (Let var e\<^sub>1' e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)
(*
fun 
  capture_avoiding :: \<open>(Id \<times> Type) set \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>capture_avoiding \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (var \<notin> \<Delta> \<and> capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding (\<Delta> \<union> {var}) e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (UnOp _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (BinOp e\<^sub>1 _ e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Cast _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding \<Delta> (Extract _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Load e\<^sub>1 e\<^sub>2 _ _) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Store e\<^sub>1 e\<^sub>2 _ _ e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding _ _ = True\<close>

lemma let_substitute_v_Let_size_less: 
    \<open>size_class.size (Let var (Val v\<^sub>1) e\<^sub>2) > size_class.size ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  by (induct e\<^sub>2, auto)

lemma capture_avoiding_substitution_eval_eq:
  assumes \<open>capture_avoiding (dom (\<Delta>(var \<mapsto> v))) e\<close> 
    shows \<open>eval_exp (\<Delta>(var \<mapsto> v)) e = eval_exp \<Delta> ([v\<sslash>var]e)\<close> 
  using assms apply (induct e arbitrary: \<Delta>)
  apply auto
  apply (simp_all only: let_substitute_val.simps capture_avoiding.simps)
  by (metis dom_fun_upd fun_upd_twist option.distinct(1))

lemma LET: 
  assumes \<open>capture_avoiding (dom \<Delta>) (Let var (Val v\<^sub>1) e\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (Let var (Val v\<^sub>1) e\<^sub>2) \<leadsto> ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  using assms apply auto
  apply (metis less_not_refl let_substitute_v_Let_size_less)
  using let_substitute_val_size_eq apply auto[1]
  using capture_avoiding_substitution_eval_eq by simp
*)
lemma ITE_STEP_COND:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>1, auto)

lemma ITE_STEP_THEN:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>2, auto)

lemma ITE_STEP_ELSE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3')\<close>
  using assms by (cases e\<^sub>3, auto)

lemma ITE_TRUE: \<open>\<Delta> \<turnstile> (Ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>2)\<close>
  by auto

lemma ITE_FALSE: \<open>\<Delta> \<turnstile> (Ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>3)\<close>
  by auto

lemma ITE_UNK:
  assumes \<open>type v\<^sub>2 = t'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite (unknown[str]: t) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (unknown[str]: t')\<close>
  using assms by (simp add: unknown_constructor_exp_def)

lemma BOP_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val v\<^sub>1) bop e\<^sub>2) \<leadsto> (BinOp (Val v\<^sub>1) bop e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto)

lemma PLUS_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> ((Val v\<^sub>1) + e\<^sub>2) \<leadsto> ((Val v\<^sub>1) + e\<^sub>2')\<close>
  using assms unfolding plus_exp.simps by (rule BOP_RHS)

lemma BOP_RHS_WORD:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) bop e\<^sub>2) \<leadsto> (BinOp (num \<Colon> sz) bop e\<^sub>2')\<close>
  unfolding word_constructor_exp_def using assms by (rule BOP_RHS)

lemma BOP_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp e\<^sub>1 bop e\<^sub>2) \<leadsto> (BinOp e\<^sub>1' bop e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma AOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (unknown[str]: t) (AOp aop) (Val v)) \<leadsto> (unknown[str]: t)\<close>
  by auto

lemma AOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (AOp aop) (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  by auto

lemma LOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (unknown[str]: t) (LOp lop) (Val v)) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  by auto

lemma LOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp lop) (unknown[str]: t)) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  by auto

lemma PLUS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma MINUS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by (cases \<open>num\<^sub>2 \<le> num\<^sub>1\<close>, auto)
  
lemma TIMES: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma DIV: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma SDIV: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma MOD: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma SMOD: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma LSL: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma LSR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma ASR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma LAND: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma LOR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma XOR: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma EQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> true\<close>
  by (simp add: bv_eq_def)

lemma EQ_DIFF: 
  assumes \<open>(num\<^sub>1 \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz)) \<leadsto> false\<close>
  using assms apply auto
  unfolding bv_eq_def by auto

lemma NEQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> false\<close>
  by (simp add: bv_eq_def)

lemma NEQ_DIFF: 
  assumes \<open>(num\<^sub>1 \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz)) (LOp Neq) (num\<^sub>2 \<Colon> sz) \<leadsto> true\<close>
  using assms apply auto
  apply (simp add: bv_eq_def)
  by (cases \<open>num\<^sub>1 = num\<^sub>2\<close>, auto)

lemma LESS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma LESS_EQ: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) lteq (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  apply auto
  by (simp_all add: bv_eq_def)

lemma SIGNED_LESS: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma SIGNED_LESS_EQ: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) slteq (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
  apply auto
  by (simp_all add: bv_eq_def)

lemma UOP: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (UnOp uop e) \<leadsto> (UnOp uop e')\<close>
  using assms by (cases e, auto)

lemma UOP_UNK: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  by auto

lemma NOT: \<open>\<Delta> \<turnstile> ~(num \<Colon> sz) \<leadsto> (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
  unfolding BIL_Syntax.not_exp.simps by auto

lemma NOT_FALSE: \<open>\<Delta> \<turnstile> ~false \<leadsto> true\<close>
  using bv_negation_false_true NOT by (metis false_word)

lemma NOT_TRUE: \<open>\<Delta> \<turnstile> ~true \<leadsto> false\<close>
  using bv_negation_true_false NOT by (metis true_word)


lemma NEG: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<leadsto> (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
  by auto

lemma CONCAT_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<leadsto> (e\<^sub>1 @ e\<^sub>2')\<close>
  using assms unfolding step_pred_exp.simps
  apply auto
  apply (simp add: STEP_NOT_EQ)
  by (metis STEP_NOT_REDUCTION)


lemma CONCAT_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<leadsto> (e\<^sub>1' @ (Val v\<^sub>2))\<close>
  using assms unfolding step_pred_exp.simps
  apply auto
  apply (simp add: STEP_NOT_EQ)
  by (metis STEP_NOT_REDUCTION)

lemma CONCAT_LHS_UN:
  assumes \<open>type v\<^sub>2 = imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v\<^sub>2)) \<leadsto> unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms apply (rule_tac val_exhaust[of v\<^sub>2]) 
  by auto

lemma CONCAT_RHS_UN:
    \<open>\<Delta> \<turnstile> (num \<Colon> sz\<^sub>1) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close>
  by (simp_all add: unknown_constructor_exp_def)

lemma CONCAT: \<open>\<Delta> \<turnstile> (num\<^sub>1 \<Colon> sz) @ (num\<^sub>2 \<Colon> sz) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<cdot> (num\<^sub>2 \<Colon> sz))\<close>
  by auto

lemma EXTRACT: 
  assumes \<open>sz\<^sub>2 \<le> sz\<^sub>1\<close>
    shows \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<leadsto> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)\<close>
  using assms by auto

lemma CAST_REDUCE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto> (Cast cast sz e')\<close>
  using assms by (cases e, auto)

lemma CAST_UNK: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by auto

lemma CAST_LOW: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by auto

lemma CAST_HIGH: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))\<close>
  by auto

lemma CAST_SIGNED: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<leadsto> (exts (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by auto

lemma CAST_UNSIGNED: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>
  by auto


fun
  eval_exps_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close>)
where
  \<open>(\<Delta> \<turnstile> e \<leadsto>* v) = (v = eval_exp \<Delta> e)\<close>


lemma REDUCE: \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2) \<Longrightarrow> (\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* v) \<Longrightarrow> (\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* v)\<close>
  apply auto
  by (metis STEP_NOT_REDUCTION)

lemma REFL:  \<open>\<Delta> \<turnstile> (Val v) \<leadsto>* v\<close>
  by auto

lemma REFL_UNKNOWN[simp]:  \<open>\<Delta> \<turnstile> unknown[str]: t \<leadsto>* unknown[str]: t\<close>
  by auto

lemma REFL_WORD[simp]:  \<open>\<Delta> \<turnstile> (num \<Colon> sz) \<leadsto>* (num \<Colon> sz)\<close>
  by auto

lemma REFL_STORAGE[simp]:  \<open>\<Delta> \<turnstile> (v[w \<leftarrow> v',sz]) \<leadsto>* (v[w \<leftarrow> v',sz])\<close>
  by auto


lemma REFL_TRUE[simp]: \<open>\<Delta>a \<turnstile> true \<leadsto>* true\<close>
  by auto

lemma REFL_FALSE[simp]: \<open>\<Delta>a \<turnstile> false \<leadsto>* false\<close>
  by auto


lemma reflI:
  assumes \<open>e = (Val v)\<close> shows \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
  using assms by auto


lemma reduce_true_false_unknown:
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
    shows \<open>v = true \<or> v = false \<or> (\<exists>str. v = unknown[str]: imm\<langle>1\<rangle>)\<close>
  using assms apply (drule_tac eval_exp_typed_ok, blast)
  unfolding eval_exps_pred_exp.simps apply simp 
  apply (rule val_exhaust[of v])
  subgoal for num sz
    by (metis One_nat_def bool_word_is_ok_exhaust)
  subgoal for str t
    apply (cases t, auto)
    apply (metis unknown_imm_typed_diff)
    by (metis unknown_typed_diff)
  subgoal 
    by force
  .


(*
lemma typed_reduce_exp_induct[consumes 3, case_names Val VarIn VarNotIn LoadUnkMem LoadUnkAddr Load
                                                   Store StoreUnkAddr AOpUnkLeft AOp AOpUnkRight
                                                   LOpUnkLeft LOp LOpUnkRight UnOpUnk UnOp
                                                   UnkWideningCast UnkNarrowingcast UnsignedCast
                                                   SignedCast HighCast LowCast Let
                                                   IteUnk IteTrue IteFalse ExtractUnk Extract
                                                   ConcatUnkLeft Concat ConcatUnkRight]:
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t. \<lbrakk>\<Gamma> \<turnstile> v :: t; t = type v; wfnew \<Gamma> \<Delta>\<rbrakk> \<Longrightarrow> P (Val v) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t name. \<lbrakk>(name :\<^sub>t t) \<in> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; v = the (\<Delta> (name :\<^sub>t t)); 
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Var (name :\<^sub>t t)) \<Gamma> t \<Delta> (the (\<Delta> (name :\<^sub>t t)))\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t name. \<lbrakk>(name :\<^sub>t t) \<notin> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; v = unknown[[]]: t; 
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Var (name :\<^sub>t t)) \<Gamma> t \<Delta> (unknown[[]]: t)\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v'. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = Storage mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v' sz\<^sub>m\<^sub>e\<^sub>m; v\<^sub>2 = Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>;
            v = load v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz en                
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m str. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>;
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m str mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v'. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = Storage mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' v' sz\<^sub>m\<^sub>e\<^sub>m; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz w\<^sub>a\<^sub>d\<^sub>d\<^sub>r. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz mod sz\<^sub>m\<^sub>e\<^sub>m = 0; sz > 0;
            v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            \<Gamma> \<turnstile> v\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; v\<^sub>2 = Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>3; wfnew \<Gamma> \<Delta>;
            v = store v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>3 sz en
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz str. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz mod sz\<^sub>m\<^sub>e\<^sub>m = 0; sz > 0;
            v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            \<Gamma> \<turnstile> v\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> v\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>3; wfnew \<Gamma> \<Delta>;
            v = unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>  
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz w\<^sub>1 w\<^sub>2. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = Immediate w\<^sub>2;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = Immediate (operator_aop aop w\<^sub>1 w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 aop sz w\<^sub>1 str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 lop sz str. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>1\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 w\<^sub>2 lop sz. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = Immediate w\<^sub>2;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = Immediate (operator_lop lop w\<^sub>1 w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 lop sz str. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<rangle>; v\<^sub>1 = Immediate w\<^sub>1; v\<^sub>2 = unknown[str]: imm\<langle>sz\<rangle>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<^sub>2;
            v = unknown[str]: imm\<langle>1\<rangle>
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v v' t e uop sz str. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            v' = eval_exp \<Delta> e; v' = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: imm\<langle>sz\<rangle>;
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v v' t e uop sz w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            v' = eval_exp \<Delta> e; v' = Immediate w; v = Immediate ((operator_unop uop) w);
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' str cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz'; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = unknown[str]: imm\<langle>sz'\<rangle>;
            v = unknown[str]: imm\<langle>sz\<rangle>; cast = Unsigned \<or> cast = Signed
           \<rbrakk> \<Longrightarrow> P (Cast cast sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' str cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = unknown[str]: imm\<langle>sz'\<rangle>; sz > 0;
            v = unknown[str]: imm\<langle>sz\<rangle>; cast = Low \<or> cast = High
           \<rbrakk> \<Longrightarrow> P (Cast cast sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz';
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (unsigned:sz[e]) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz \<ge> sz'; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = (eval_exp \<Delta> e); wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (Cast Signed sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; sz > 0; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (bits w - 1) \<sim> lo : (bits w - sz))
           \<rbrakk> \<Longrightarrow> P (Cast High sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e v' sz sz' w. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz'\<rangle>; sz' \<ge> sz; 
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> v'; v' = eval_exp \<Delta> e; sz > 0; wfnew \<Gamma> \<Delta>; v' = Immediate w;
            v = Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)
           \<rbrakk> \<Longrightarrow> P (Cast Low sz e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t name t' e\<^sub>1 e\<^sub>2 v\<^sub>1. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: t'; \<Gamma> \<turnstile> v\<^sub>1 :: t'; ((name :\<^sub>t t') # \<Gamma>) \<turnstile> v :: t;
            P e\<^sub>1 \<Gamma> t' \<Delta> v\<^sub>1; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v = (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> v\<^sub>1)) e\<^sub>2);
            wfnew \<Gamma> \<Delta>; name \<notin> dom\<^sub>\<Gamma> \<Gamma>; wfnew ((name :\<^sub>t t') # \<Gamma>) (\<Delta>((name :\<^sub>t t') \<mapsto> v\<^sub>1));
            P e\<^sub>2 ((name :\<^sub>t t') # \<Gamma>) t (\<Delta> ((name :\<^sub>t t') \<mapsto> v\<^sub>1)) v
           \<rbrakk> \<Longrightarrow> P (Let (name :\<^sub>t t') e\<^sub>1 e\<^sub>2) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = unknown[str]: imm\<langle>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = unknown[str]: t;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = Immediate true;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = v\<^sub>2;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t e\<^sub>1 e\<^sub>2 e\<^sub>3 v\<^sub>1 v\<^sub>2 v\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2; v\<^sub>3 = eval_exp \<Delta> e\<^sub>3; v\<^sub>1 = Immediate false;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: t; \<Gamma> \<turnstile> v\<^sub>3 :: t; v = v\<^sub>3;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> t \<Delta> v\<^sub>2; P e\<^sub>3 \<Gamma> t \<Delta> v\<^sub>3
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> str v v' t sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            t = imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>; wfnew \<Gamma> \<Delta>; v' = eval_exp \<Delta> e; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v';
            v' = unknown[str]: imm\<langle>sz\<rangle>; v = unknown[str]: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> w v v' t sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            t = imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>; wfnew \<Gamma> \<Delta>; v' = eval_exp \<Delta> e; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> v'; 
            v' = Immediate w; v = Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = unknown[str]: imm\<langle>sz\<^sub>1\<rangle>;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 w\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = Immediate w\<^sub>1;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v\<^sub>2 = Immediate w\<^sub>2; v = Immediate (w\<^sub>1 \<cdot> w\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
      and \<open>\<And>\<Gamma> \<Delta> v t sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 w\<^sub>1 str. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> v\<^sub>1; P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> v\<^sub>2; wfnew \<Gamma> \<Delta>; v\<^sub>1 = Immediate w\<^sub>1;
            \<Gamma> \<turnstile> v\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> v\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; v\<^sub>1 = eval_exp \<Delta> e\<^sub>1; v\<^sub>2 = eval_exp \<Delta> e\<^sub>2;
            v\<^sub>2 = unknown[str]: imm\<langle>sz\<^sub>2\<rangle>; v = unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>
           \<rbrakk> \<Longrightarrow> P (Concat e\<^sub>1 e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> v\<close>
    shows \<open>P e \<Gamma> t \<Delta> v\<close>
  using assms(1-5) apply (drule_tac P=P in typed_eval_exp_induct)
  apply blast
  apply blast
  apply blast
  apply blast
  using assms(6) apply simp
  using assms(7) apply simp
  using assms(8) apply simp
  using assms(9) apply simp
  using assms(10) apply simp
  using assms(11) apply simp
  using assms(12) apply simp
  using assms(13) apply simp
  using assms(14) apply simp
  using assms(15) apply simp
  using assms(16) apply simp
  using assms(17) apply simp
  using assms(18) apply simp
  using assms(19) apply simp
  using assms(20) apply simp
  using assms(21) apply simp
  using assms(22) apply simp
  using assms(23) apply simp
  using assms(24) apply simp
  using assms(25) apply simp
  using assms(26) apply simp
  using assms(27) apply simp
  using assms(28) apply simp
  using assms(29) apply simp
  using assms(30-34) by simp_all
*)

(*
lemma typed_eval_exp_induct[consumes 3, case_names Val VarIn VarNotIn Load Store AOp LOp UnOp 
                                            Cast Let ITE Extract Concat]: 
  assumes \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>\<Delta> \<turnstile> e \<leadsto>* v\<close>
      and \<open>wfnew \<Gamma> \<Delta>\<close>
      and val: \<open>\<And>\<Gamma> \<Delta> v t. \<lbrakk>\<Gamma> \<turnstile> v :: t; t = type v; wfnew \<Gamma> \<Delta>\<rbrakk> \<Longrightarrow> P (Val v) \<Gamma> t \<Delta> v\<close>
      and var_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<in> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok; \<Gamma> \<turnstile> the (\<Delta> (name :\<^sub>t t)) :: t; 
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> (the (\<Delta> (name :\<^sub>t t)))\<close>
      and var_not_in: \<open>\<And>\<Gamma> \<Delta> t name. \<lbrakk>(name :\<^sub>t t) \<notin> dom \<Delta>; (name :\<^sub>t t) \<in> set \<Gamma>; \<Gamma> is ok;
            \<Gamma> \<turnstile> ((unknown[[]]: t)::val) :: t;
            t is ok; wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (name :\<^sub>t t) \<Gamma> t \<Delta> ((unknown[[]::string]: t)::val)\<close>
      and load: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 en sz sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>t = imm\<langle>sz\<rangle>; sz > 0; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; 
            \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>;
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2); wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Load e\<^sub>1 e\<^sub>2 en sz) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_load (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz en)\<close>
      and store: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz. \<lbrakk>t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m dvd sz; sz > 0;
            \<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; 
            P e\<^sub>1 \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2); 
            P e\<^sub>3 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>3); wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (Store e\<^sub>1 e\<^sub>2 en sz e\<^sub>3) \<Gamma> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Delta> (eval_store (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz en (eval_exp \<Delta> e\<^sub>3))\<close>
      and aop: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 aop sz. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_binop (AOp aop) (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
      and lop: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 lop sz. \<lbrakk>t = imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2)
           \<rbrakk> \<Longrightarrow> P (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) \<Gamma> imm\<langle>1\<rangle> \<Delta> (eval_binop (LOp lop) (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
      and uop: \<open>\<And>\<Gamma> \<Delta> t e uop sz. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; wfnew \<Gamma> \<Delta>;
            P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (UnOp uop e) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_unop uop (eval_exp \<Delta> e))\<close>
      and cast: \<open>\<And>\<Gamma> \<Delta> t e sz sz' cast. \<lbrakk>t = imm\<langle>sz\<rangle>; \<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>;
            P e \<Gamma> imm\<langle>sz'\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (cast:sz[e]) \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_cast cast sz (eval_exp \<Delta> e))\<close>
      and let1: \<open>\<And>\<Gamma> \<Delta> t name t' e\<^sub>1 e\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: t'; ((name :\<^sub>t t') # \<Gamma>) \<turnstile> e\<^sub>2 :: t;
            P e\<^sub>1 \<Gamma> t' \<Delta> (eval_exp \<Delta> e\<^sub>1);
            wfnew \<Gamma> \<Delta>; name \<notin> dom\<^sub>\<Gamma> \<Gamma>; 
            (\<Gamma> \<turnstile> eval_exp \<Delta> e\<^sub>1 :: t' \<Longrightarrow> wfnew ((name :\<^sub>t t') # \<Gamma>) (\<Delta>((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) \<and>
            P e\<^sub>2 ((name :\<^sub>t t') # \<Gamma>) t (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2))
           \<rbrakk> \<Longrightarrow> P (Let (name :\<^sub>t t') e\<^sub>1 e\<^sub>2) \<Gamma> t \<Delta> (eval_exp (\<Delta> ((name :\<^sub>t t') \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close>
      and ite: \<open>\<And>\<Gamma> \<Delta> t e\<^sub>1 e\<^sub>2 e\<^sub>3. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: t; \<Gamma> \<turnstile> e\<^sub>3 :: t; wfnew \<Gamma> \<Delta>;
            P e\<^sub>1 \<Gamma> imm\<langle>1\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> t \<Delta> (eval_exp \<Delta> e\<^sub>2); P e\<^sub>3 \<Gamma> t \<Delta> (eval_exp \<Delta> e\<^sub>3)
           \<rbrakk> \<Longrightarrow> P (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Gamma> t \<Delta> (eval_if (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) (eval_exp \<Delta> e\<^sub>3))\<close>
      and extract': \<open>\<And>\<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 sz e. \<lbrakk>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>; sz\<^sub>2 \<le> sz\<^sub>1; 
            wfnew \<Gamma> \<Delta>; P e \<Gamma> imm\<langle>sz\<rangle> \<Delta> (eval_exp \<Delta> e)
           \<rbrakk> \<Longrightarrow> P (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Gamma> imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> \<Delta> (eval_extract sz\<^sub>1 sz\<^sub>2 (eval_exp \<Delta> e))\<close>
      and concat: \<open>\<And>\<Gamma> \<Delta> sz\<^sub>1 sz\<^sub>2 e\<^sub>1 e\<^sub>2. \<lbrakk>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>; \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>; 
            P e\<^sub>1 \<Gamma> imm\<langle>sz\<^sub>1\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>1); P e\<^sub>2 \<Gamma> imm\<langle>sz\<^sub>2\<rangle> \<Delta> (eval_exp \<Delta> e\<^sub>2);
            wfnew \<Gamma> \<Delta>
           \<rbrakk> \<Longrightarrow> P (e\<^sub>1 @ e\<^sub>2) \<Gamma> imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<Delta> (eval_concat (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2))\<close>
    shows \<open>P e \<Gamma> t \<Delta> v\<close>
  using assms typed_eval_exp_induct_internal
*)

end
