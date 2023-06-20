theory Bitvector_Syntax
  imports Syntax
begin

class word_constructor = bool_syntax +
    fixes word_constructor :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a\<close> (infixl \<open>\<Colon>\<close> 51)
  assumes word_eq[simp]: \<open>\<And>nat sz nat' sz'. (nat \<Colon> sz) = (nat' \<Colon> sz') \<longleftrightarrow> nat = nat' \<and> sz = sz'\<close>
      and true_word: \<open>true = (1 \<Colon> 1)\<close>
      and false_word: \<open>false = (0 \<Colon> 1)\<close>
begin

lemma word_not_sz_neqI:
  assumes \<open>num \<noteq> num'\<close>
    shows \<open>(num \<Colon> sz) \<noteq> (num' \<Colon> sz)\<close>
  using assms by simp

lemma word_synax_induct: 
  assumes \<open>\<And>nat sz. Q (nat \<Colon> sz)\<close>
      and \<open>\<And>nat sz. w \<noteq> (nat \<Colon> sz) \<Longrightarrow> Q w\<close>
    shows \<open>Q w\<close>
  using assms by force

lemma word_syntax_exhaust:
  obtains 
    (Word) nat sz where \<open>w = (nat \<Colon> sz)\<close>
  | (NotWord) \<open>\<forall>nat sz. w \<noteq> (nat \<Colon> sz)\<close>
   by force

lemma bv_pattern_complete:
  assumes \<open>(\<And>nat\<^sub>1 sz\<^sub>1. x = (nat\<^sub>1 \<Colon> sz\<^sub>1) \<Longrightarrow> P)\<close>
      and \<open>(\<And>w\<^sub>1. \<lbrakk>\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz); x = w\<^sub>1\<rbrakk> \<Longrightarrow> P)\<close>
    shows P
  using assms by blast

lemma bv2_pattern_complete:
  assumes \<open>(\<And>nat\<^sub>1 sz\<^sub>1 nat\<^sub>2 sz\<^sub>2. x = (nat\<^sub>1 \<Colon> sz\<^sub>1, nat\<^sub>2 \<Colon> sz\<^sub>2) \<Longrightarrow> P)\<close>
      and \<open>(\<And>w\<^sub>1 w\<^sub>2. (\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz)) \<Longrightarrow> x = (w\<^sub>1, w\<^sub>2) \<Longrightarrow> P)\<close>
    shows P
  using assms 
    apply (cases x, clarify)
    subgoal for w\<^sub>1 w\<^sub>2 
      apply (rule word_syntax_exhaust[of w\<^sub>1], simp_all)
      by (rule word_syntax_exhaust[of w\<^sub>2], simp_all)+
    .

lemma bv_eq_sz_pattern_complete:
  assumes \<open>(\<And>nat\<^sub>1 sz nat\<^sub>2. x = (nat\<^sub>1 \<Colon> sz, nat\<^sub>2 \<Colon> sz) \<Longrightarrow> P)\<close>
      and \<open>(\<And>sz\<^sub>1 sz\<^sub>2 nat\<^sub>1 nat\<^sub>2. \<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2; x = (nat\<^sub>1 \<Colon> sz\<^sub>1, nat\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> P)\<close>
      and \<open>(\<And>w\<^sub>1 w\<^sub>2. \<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz)); x = (w\<^sub>1, w\<^sub>2)\<rbrakk> \<Longrightarrow> P)\<close>
    shows P
  using assms 
  apply (rule_tac bv2_pattern_complete[of x P])
  subgoal for nat\<^sub>1 sz\<^sub>1 nat\<^sub>2 sz\<^sub>2
    by (cases \<open>sz\<^sub>1 = sz\<^sub>2\<close>, blast+)
  by blast 

function
  bv_plus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>+\<^sub>b\<^sub>v\<close> 56)    
where  
  \<open>(nat\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (((nat\<^sub>1 + nat\<^sub>2) mod 2 ^ sz) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) +\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_plus.simps[simp del]

function
  bv_inc :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>++\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>++\<^sub>b\<^sub>v (nat\<^sub>1 \<Colon> sz) = (nat\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (1 \<Colon> sz)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> ++\<^sub>b\<^sub>v w = undefined\<close>
  apply blast+
  by auto
termination by (standard, auto)

function 
  bv_minus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>-\<^sub>b\<^sub>v\<close> 56)
where 
  \<open>\<lbrakk>nat\<^sub>2 \<le> nat\<^sub>1\<rbrakk> \<Longrightarrow> (nat\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 - nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>nat\<^sub>1 < nat\<^sub>2\<rbrakk> \<Longrightarrow> (nat\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (((2 ^ sz + nat\<^sub>1) - nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) -\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  subgoal for P x 
    apply (rule bv_eq_sz_pattern_complete[of x P])
    subgoal for nat\<^sub>1 sz nat\<^sub>2 by (cases \<open>nat\<^sub>2 \<le> nat\<^sub>1\<close>, simp_all)
    by simp
  by auto

termination by (standard, auto)

function
  bv_times :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>*\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (((nat\<^sub>1 * nat\<^sub>2) mod 2 ^ sz) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) *\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function 
  bv_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>div\<^sub>b\<^sub>v\<close> 56) (* TODO *)
where
  \<open>(nat\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 div nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) div\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_sdivide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>div\<^sub>s\<^sub>b\<^sub>v\<close> 56) (* TODO *)
where
  \<open>(nat\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 div nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) div\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function 
  bv_land :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>&\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((and nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) &\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 &\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

lemma land_false[simp]: 
    \<open>true &\<^sub>b\<^sub>v false = false\<close> 
    \<open>false &\<^sub>b\<^sub>v true = false\<close> 
    \<open>false &\<^sub>b\<^sub>v false = false\<close>
  unfolding true_word false_word bv_land.simps and_zero_eq zero_and_eq by safe

lemma land_true[simp]:
    \<open>true &\<^sub>b\<^sub>v true = true\<close>
  unfolding true_word bv_land.simps and.idem by clarify

function
  bv_lor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>|\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((or nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) |\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 |\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>xor\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((Bit_Operations.xor nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) xor\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 xor\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_mod\<^sub>b\<^sub>v :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>%\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 % nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) %\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_smod :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>%\<^sub>s\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 % nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) %\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_lsl :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><<\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2) = (((nat\<^sub>1 * (2 ^ nat\<^sub>2)) mod 2 ^ sz\<^sub>1) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <<\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_lsr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>>>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2) = ((nat\<^sub>1 div (2 ^ nat\<^sub>2)) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 >>\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_asr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>>>>\<^sub>b\<^sub>v\<close> 56)  
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) >>>\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> _) = (((and nat\<^sub>1 ((2 ^ nat\<^sub>2) div 2)) + (nat\<^sub>1 div (2 ^ nat\<^sub>2))) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 >>>\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function 
  bv_concat :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<cdot>\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (nat\<^sub>2 \<Colon> sz\<^sub>2) = (nat (concat_bit sz\<^sub>2 (of_nat nat\<^sub>2) (of_nat nat\<^sub>1)) \<Colon> (sz\<^sub>1 + sz\<^sub>2))\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 \<cdot> w\<^sub>2 = undefined\<close>
  apply (rule bv2_pattern_complete, blast)
  by auto

termination by (standard, auto)

lemma bv_concat_0: \<open>(0 \<Colon> sz\<^sub>1) \<cdot> (0 \<Colon> sz\<^sub>2) = (0 \<Colon> sz\<^sub>1 + sz\<^sub>2)\<close>
  unfolding bv_concat.simps by auto

function
  bv_uminus :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>-\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>-\<^sub>b\<^sub>v (nat\<^sub>1 \<Colon> sz\<^sub>1) = (nat\<^sub>1 \<Colon> sz\<^sub>1)\<close> | (* TODO *)
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> -\<^sub>b\<^sub>v w\<^sub>1 = undefined\<close>
  apply (rule bv_pattern_complete, blast)
  by auto

termination by (standard, auto)

function
  bv_negation :: \<open>'a \<Rightarrow> 'a\<close> (\<open>~\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>~\<^sub>b\<^sub>v (nat\<^sub>1 \<Colon> sz\<^sub>1) = ((2 ^ sz\<^sub>1 - 1 - nat\<^sub>1) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> ~\<^sub>b\<^sub>v w\<^sub>1 = undefined\<close>
  apply (rule bv_pattern_complete, blast)
  by auto

termination by (standard, auto)

lemma bv_negation_true_false[simp]: \<open>~\<^sub>b\<^sub>v true = false\<close>
  unfolding true_word false_word bv_negation.simps by auto

lemma bv_negation_false_true[simp]: \<open>~\<^sub>b\<^sub>v false = true\<close>
  unfolding true_word false_word bv_negation.simps by auto

function
  bv_le :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (if nat\<^sub>1 < nat\<^sub>2 then true else false)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) <\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  bv_sle :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><\<^sub>s\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (if nat\<^sub>1 < nat\<^sub>2 then true else false)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) <\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

function
  xtract :: \<open>'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>ext _ \<sim> hi : _ \<sim> lo : _\<close>)
where
  \<open>(ext (nat\<^sub>1 \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = (take_bit (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w + 1) (drop_bit sz\<^sub>l\<^sub>o\<^sub>w nat\<^sub>1) \<Colon> (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w + 1))\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> (ext w \<sim> hi : _ \<sim> lo : _) = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for w sz\<^sub>h\<^sub>i sz\<^sub>l\<^sub>o\<^sub>w
      apply (rule word_syntax_exhaust[of w])
      subgoal for nat sz
        apply (cases \<open>sz\<^sub>l\<^sub>o\<^sub>w \<le> sz\<^sub>h\<^sub>i\<close>)
        by simp_all
      by force
    .
  by auto

termination by (standard, auto)

declare xtract.simps[simp del]

lemma extract_0: \<open>(ext 0 \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = 0 \<Colon> Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w)\<close>
  unfolding xtract.simps by auto

lemma extract_concat32:
  assumes \<open>x < 2 ^ 32\<close>
    shows \<open>((((ext x \<Colon> 32 \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext x \<Colon> 32 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
               ext x \<Colon> 32 \<sim> hi : 15 \<sim> lo :  8) \<cdot> ext x \<Colon> 32 \<sim> hi :  7 \<sim> lo :  0) = x \<Colon> 32\<close>
  unfolding xtract.simps bv_concat.simps apply simp
  unfolding of_nat_take_bit of_nat_drop_bit
  unfolding concat_bit_take_bit_eq
  apply (unfold concat_bit_drop_bit, simp)+
  by (metis add_One_commute assms concat_take_drop_bit_nat_eq_self numeral_plus_numeral semiring_norm(2) semiring_norm(4) semiring_norm(6))

lemma extract_concat64:
  assumes \<open>x < 2 ^ 64\<close>
    shows \<open>((((((((ext x \<Colon> 64 \<sim> hi : 63 \<sim> lo : 56) \<cdot> ext x \<Colon> 64 \<sim> hi : 55 \<sim> lo : 48) \<cdot>
                   ext x \<Colon> 64 \<sim> hi : 47 \<sim> lo : 40) \<cdot> ext x \<Colon> 64 \<sim> hi : 39 \<sim> lo : 32) \<cdot>
                   ext x \<Colon> 64 \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext x \<Colon> 64 \<sim> hi : 23 \<sim> lo : 16) \<cdot>
                   ext x \<Colon> 64 \<sim> hi : 15 \<sim> lo :  8) \<cdot> ext x \<Colon> 64 \<sim> hi :  7 \<sim> lo :  0) = (x \<Colon> 64)\<close>
  unfolding xtract.simps bv_concat.simps apply simp
  unfolding of_nat_take_bit of_nat_drop_bit
  unfolding concat_bit_take_bit_eq
  apply (unfold concat_bit_drop_bit, simp)+
  by (metis add_One_commute assms concat_take_drop_bit_nat_eq_self numeral_plus_numeral semiring_norm(2) semiring_norm(4) semiring_norm(6))

lemma extract_low: 
  assumes \<open>val < 2 ^ 32\<close>
    shows \<open>(ext val \<Colon> sz \<sim> hi : 32 - 1 \<sim> lo : 0) = (val \<Colon> 32)\<close>
  unfolding xtract.simps apply simp
  apply (rule take_bit_nat_eq_self)
  using assms by assumption

function (* TODO maintain sign*)
  sxtract :: \<open>'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>exts _ \<sim> hi : _ \<sim> lo : _\<close>)
where
  \<open>(exts (nat\<^sub>1 \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = (take_bit (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w + 1) (drop_bit sz\<^sub>l\<^sub>o\<^sub>w nat\<^sub>1) \<Colon> (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w + 1))\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> (exts w \<sim> hi : _ \<sim> lo : _) = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for w sz\<^sub>h\<^sub>i sz\<^sub>l\<^sub>o\<^sub>w
      apply (rule word_syntax_exhaust[of w])
      subgoal for nat sz
        apply (cases \<open>sz\<^sub>h\<^sub>i \<le> sz\<close>)
        apply (cases \<open>sz\<^sub>l\<^sub>o\<^sub>w \<le> sz\<^sub>h\<^sub>i\<close>)
        by simp_all
      by force
    .
  by auto

termination by (standard, auto)

declare sxtract.simps[simp del]

lemma extracts_0: \<open>(exts 0 \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = 0 \<Colon> Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w)\<close>
  unfolding sxtract.simps by auto

lemma sxtract_lt_extend: 
  assumes \<open>val < 2 ^ 32\<close>
    shows \<open>(exts val \<Colon> sz \<sim> hi : 63 \<sim> lo : 0) = (val \<Colon> 64)\<close>
  unfolding sxtract.simps apply (simp (no_asm))
  apply (rule take_bit_nat_eq_self)
  using assms by simp

definition 
  bv_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>=\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a =\<^sub>b\<^sub>v b \<equiv> if a = b then true else false\<close>  

lemma and_eq_true[simp]: \<open>((num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) &\<^sub>b\<^sub>v true = (num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using bv_land.simps  bv_eq_def local.false_word local.true_word by fastforce  

lemma and_eq_false[simp]: \<open>((num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) &\<^sub>b\<^sub>v false = false\<close>
using bv_land.simps bv_eq_def local.false_word local.true_word by fastforce    


abbreviation 
  bv_neq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<noteq>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<noteq>\<^sub>b\<^sub>v b \<equiv> ~\<^sub>b\<^sub>v (a =\<^sub>b\<^sub>v b)\<close>

abbreviation
  bv_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<le>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<le>\<^sub>b\<^sub>v b \<equiv> (a =\<^sub>b\<^sub>v b) &\<^sub>b\<^sub>v (a <\<^sub>b\<^sub>v b)\<close>

abbreviation
  bv_sleq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<le>\<^sub>s\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<le>\<^sub>s\<^sub>b\<^sub>v b \<equiv> (a =\<^sub>b\<^sub>v b) &\<^sub>b\<^sub>v (a <\<^sub>s\<^sub>b\<^sub>v b)\<close>


end

class word = word_constructor +
  assumes word_induct: \<open>\<And>w Q. \<lbrakk>\<And>a b. Q (a \<Colon> b)\<rbrakk> \<Longrightarrow> Q w\<close>
      and word_exhaust: \<open>\<And>w Q. \<lbrakk>\<And>a b. w = (a \<Colon> b) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>

datatype word = Word (raw_val: nat) (bits: nat)



end
