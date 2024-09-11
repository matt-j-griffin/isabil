theory Bitvector_Nat
  imports Bitvector_Syntax
begin

instantiation nat :: word
begin

definition
  word_constructor_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>(val \<Colon> sz) = val mod sz\<close>



function
  type_nat :: \<open>nat \<Rightarrow> Type\<close>
where
  \<open>type_nat (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close>
  subgoal for P x by (rule wordI)
  subgoal unfolding word_constructor_word_def by auto
  .
termination by (standard, auto)

instance
  apply standard
  unfolding word_constructor_nat_def
  sledgehammer

end

end
