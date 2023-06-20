theory Typing_Value_Typed_Ok
  imports Typing_Storage_Typed_Ok 
          Typing_Word_Typed_Ok 
          Typing_Unknown_Typed_Ok
          "../Val_Instance" 
begin

class value_typed_ok = storage_typed_ok + unknown_typed_ok + word_typed_ok + val_syntax
begin

lemma bool_val_syntax_exhaust:
  assumes \<open>\<Gamma> \<turnstile> v :: imm\<langle>1\<rangle>\<close>
  obtains
    (True) \<open>v = true\<close>
  | (False) \<open>v = false\<close>
  | (Unknown) str where \<open>v = (unknown[str]: imm\<langle>1\<rangle>)\<close>
  | (NotVal) \<open>\<forall>num sz. v \<noteq> (num \<Colon> sz)\<close> \<open>\<forall>mem w v' sz. v \<noteq> (mem[w \<leftarrow> v', sz])\<close>
              \<open>\<forall>str t. v \<noteq> (unknown[str]: t)\<close>
  using assms apply (rule_tac val_syntax_exhaust[of v])
  apply safe
  subgoal
    apply (rule local.bool_word_is_ok_exhaust[of \<Gamma> v])
    by blast+
  subgoal for str t
    apply (frule unknown_typed_diff, clarify)
    by blast
  using local.storage_not_imm apply auto[1]    
  by blast

end

instantiation val :: value_typed_ok
begin

function
  is_ok_val :: \<open>val \<Rightarrow> bool\<close>
where 
  \<open>is_ok_val (num \<Colon> sz) = ((num \<Colon> sz)::word) is ok\<close> |
  \<open>\<lbrakk>\<forall>num sz. x \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> is_ok_val x = False\<close>
  subgoal for P x
    apply (rule val_exhaust[of x], blast)
    by blast+
  by auto 

termination by (standard, auto)

function 
  typed_ok_val :: \<open>TypingContext \<Rightarrow> val \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typed_ok_val \<Gamma> (num \<Colon> sz) imm\<langle>sz\<rangle> = (((num \<Colon> sz)::word) is ok \<and> \<Gamma> is ok)\<close> |
  \<open>typed_ok_val \<Gamma> (unknown[str]: t) t = (t is ok \<and> \<Gamma> is ok)\<close> |
  \<open>typed_ok_val \<Gamma> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>v\<^sub>a\<^sub>l]) mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>v\<^sub>a\<^sub>l\<rangle> = (((num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)::word) is ok \<and> sz\<^sub>v\<^sub>a\<^sub>l > 0 \<and>
       (\<Gamma> \<turnstile> v' :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>) \<and> (\<Gamma> \<turnstile> v :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>v\<^sub>a\<^sub>l\<rangle>))\<close> |
  \<open>\<lbrakk>
    (\<forall>num sz. v = (num \<Colon> sz) \<longrightarrow> t \<noteq> imm\<langle>sz\<rangle>) \<and>
    (\<forall>str t'. v = (unknown[str]: t') \<longrightarrow> t \<noteq> t') \<and>
    (\<forall>mem num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz\<^sub>v\<^sub>a\<^sub>l. v = (mem[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>v\<^sub>a\<^sub>l]) \<longrightarrow> t \<noteq> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>v\<^sub>a\<^sub>l\<rangle>)
   \<rbrakk> \<Longrightarrow> typed_ok_val _ v t = False\<close>  
  subgoal for P x
    apply (rule prod_cases3[of x])
    apply auto
    subgoal for a b c
      apply (case_tac b, auto)
      by blast+
    .
  apply (simp_all del: is_ok_word.simps)  
  by blast+

termination
  apply standard
  apply (relation \<open>(\<lambda>p. size (fst (snd p))) <*mlex*> {}\<close>)
  apply (simp_all add: wf_mlex)
  unfolding storage_constructor_val_def
  by (rule mlex_less, auto)+



instance
  apply (standard, simp_all)
  subgoal by (drule typed_ok_val.elims(2), auto)
  subgoal using typed_ok_val.simps(4) by fastforce
  subgoal using typed_ok_val.simps(4) by fastforce
  subgoal using typed_ok_val.simps(4) by fastforce
  subgoal using typed_ok_val.simps(4) by fastforce
  .

end

end
