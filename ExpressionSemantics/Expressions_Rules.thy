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
  storage16 :: \<open>val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close>
where
  \<open>storage16 mem num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>2 \<equiv> (mem
    [num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>2 \<Colon> 16 \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>2 \<Colon> 16 \<sim> hi : 15 \<sim> lo :  8, 8])
\<close>

abbreviation (* TODO addresses *)
  storage32 :: \<open>val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close>
where
  \<open>storage32 mem num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>2 \<equiv> (mem
    [num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>2 \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24, 8])
\<close>

abbreviation 
  storage64 :: \<open>val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close>
where
  \<open>storage64 mem num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num\<^sub>2 \<equiv> (mem
    [num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0, 8]
    [succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8, 8]
    [succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16, 8]
    [succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24, 8]
    [succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32, 8]
    [succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40, 8]
    [succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48, 8]
    [succ (succ (succ (succ (succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))))))) \<leftarrow> ext num\<^sub>2 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56, 8])
\<close>

end

lemma type_storage16: \<open>type (storage16 mem address sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage32: \<open>type (storage32 mem address sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

lemma type_storage64: \<open>type (storage64 mem address sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r val\<^sub>1) = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  unfolding succ.simps bv_plus.simps by (rule type_storageI)

method solve_type_storage = (
    rule type_storage64 | rule type_storage32 | rule type_storage16 | rule type_storageI
)

end