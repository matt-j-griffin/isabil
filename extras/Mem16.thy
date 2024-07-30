theory Mem16
  imports "../ExpressionSemantics/Expression_Syntax_Locales"
begin

\<comment> \<open>Memory Extensions for 16bit words\<close>



context storage_constructor
begin

abbreviation 
  storage_el16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8])
\<close>

abbreviation 
  storage_be16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be16 mem w v \<equiv> (mem
    [     w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8])
\<close>

end

lemma type_storage_el16: \<open>type (storage_el16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_be16: \<open>type (storage_be16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

end
