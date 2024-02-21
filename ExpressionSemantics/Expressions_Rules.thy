theory Expressions_Rules
  imports Expression_Rules
begin

inductive
  step_exps :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close> [400, 400, 400] 401)
where
  Reduce: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> |
  Refl: \<open>\<Delta> \<turnstile> e \<leadsto>* e\<close>

inductive_cases ReduceE: \<open>\<Delta> \<turnstile> e \<leadsto>* e'\<close>

text \<open>Improved induction rule for step_exps\<close>

lemma step_exps_induct[consumes 1, case_names Reduce Refl]:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> 
      and \<open>(\<And>e\<^sub>1 e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3 \<Longrightarrow> P e\<^sub>2 \<Longrightarrow> P e\<^sub>1)\<close> 
      and \<open>P e\<^sub>3\<close>
    shows \<open>P e\<^sub>1\<close>
  using assms by (induct \<Delta> e\<^sub>1 e\<^sub>3 rule: step_exps.induct, blast+)

text \<open>Common storages\<close> (* TODO move *)

context storage_constructor
begin

abbreviation 
  storage16 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage16 mem w v \<equiv> (mem
    [w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8])
\<close>

abbreviation (* TODO addresses *)
  storage32 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage32 mem w v \<equiv> (mem
    [w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ w) \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ w)) \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8])
\<close>

abbreviation 
  storage_el64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_el64 mem w v \<equiv> (mem
    [w \<leftarrow> ext v \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ w) \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ w)) \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
    [succ (succ (succ (succ w))) \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ (succ (succ (succ (succ w)))) \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ (succ (succ (succ (succ (succ w))))) \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ (succ (succ (succ (succ (succ (succ w)))))) \<leftarrow> ext v \<sim> hi : 63 \<sim> lo : 56, 8])
\<close>

abbreviation 
  storage_be64 :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> 'a\<close>
where
  \<open>storage_be64 mem w v \<equiv> (mem
    [w \<leftarrow> ext v \<sim> hi : 63 \<sim> lo :  56, 8]
    [succ w \<leftarrow> ext v \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ (succ w) \<leftarrow> ext v \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ (succ (succ w)) \<leftarrow> ext v \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ (succ (succ (succ w))) \<leftarrow> ext v \<sim> hi : 31 \<sim> lo : 24, 8]
    [succ (succ (succ (succ (succ w)))) \<leftarrow> ext v \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ (succ (succ (succ w))))) \<leftarrow> ext v \<sim> hi : 15 \<sim> lo : 8, 8]
    [succ (succ (succ (succ (succ (succ (succ w)))))) \<leftarrow> ext v \<sim> hi : 7 \<sim> lo : 0, 8])
\<close>

end

lemma type_storage16: \<open>type (storage16 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage32: \<open>type (storage32 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_el64: \<open>type (storage_el64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage_be64: \<open>type (storage_be64 mem (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

method solve_type_storage = (
    rule type_storage_el64 | rule type_storage32 | rule type_storage16 | rule type_storageI |
    rule type_storage_be64 | rule type_storage32 | rule type_storage16 | rule type_storageI
)

end