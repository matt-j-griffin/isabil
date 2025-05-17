theory Bitvector_Syntax
  imports Syntax
          "Typing/Typing_Typed_Ok"
begin        

class word_constructor = type_syntax + typed_ok + is_ok +
  fixes word_constructor :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a\<close> (infixl \<open>\<Colon>\<close> 51)
  assumes word_inject[simp]: \<open>\<And>nat sz nat' sz'. (nat \<Colon> sz) = (nat' \<Colon> sz') \<equiv> nat = nat' \<and> sz = sz'\<close>
      and type_wordI: \<open>\<And>num sz. type (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close>
      and word_is_ok: \<open>\<And>num sz. (num \<Colon> sz) is ok \<longleftrightarrow> sz > 0 \<and> num < 2 ^ sz\<close>
      and word_typed_ok: \<open>\<And>\<Gamma> num sz. (\<Gamma> \<turnstile> (num \<Colon> sz) :: t) \<longleftrightarrow> \<Gamma> is ok \<and> (num \<Colon> sz) is ok \<and> t = imm\<langle>sz\<rangle>\<close>
begin

lemma type_wordE: \<open>type (num \<Colon> sz) = t \<Longrightarrow> (t = imm\<langle>sz\<rangle> \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using type_wordI by blast


abbreviation
  true :: 'a
where 
  \<open>true \<equiv> (Suc 0 \<Colon> Suc 0)\<close>

abbreviation
  false :: 'a
where 
  \<open>false \<equiv> (0 \<Colon> Suc 0)\<close>

lemma true_neq_false[simp]: \<open>true \<noteq> false\<close> \<open>false \<noteq> true\<close>
  by auto

lemma word_bool_inject[simp]: 
    \<open>(num \<Colon> sz) = true  \<longleftrightarrow> num = 1 \<and> sz = 1\<close> \<open>true  = (num \<Colon> sz) \<longleftrightarrow> num = 1 \<and> sz = 1\<close>
    \<open>(num \<Colon> sz) = false \<longleftrightarrow> num = 0 \<and> sz = 1\<close> \<open>false = (num \<Colon> sz) \<longleftrightarrow> num = 0 \<and> sz = 1\<close>
  unfolding word_inject by auto

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

declare bv_inc.simps[simp del]

function 
  bv_minus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>-\<^sub>b\<^sub>v\<close> 56)
where 
  \<open>(nat\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((if (nat\<^sub>1 < nat\<^sub>2) then 2 ^ sz + nat\<^sub>1 - nat\<^sub>2 else (nat\<^sub>1 - nat\<^sub>2)) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) -\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  subgoal for P x 
    apply (rule bv_eq_sz_pattern_complete[of x P])
    subgoal for nat\<^sub>1 sz nat\<^sub>2 by (cases \<open>nat\<^sub>2 \<le> nat\<^sub>1\<close>, simp_all)
    by simp
  by auto
termination by (standard, auto)

declare bv_minus.simps[simp del]

lemma minus0[simp]: \<open>(num \<Colon> sz) -\<^sub>b\<^sub>v (0 \<Colon> sz) = (num \<Colon> sz)\<close>
  unfolding bv_minus.simps by simp

function
  bv_times :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>*\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (((nat\<^sub>1 * nat\<^sub>2) mod 2 ^ sz) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) *\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

declare bv_times.simps[simp del]

lemma times0[simp]: \<open>(0 \<Colon> sz) *\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (0 \<Colon> sz)\<close> \<open>(nat\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (0 \<Colon> sz) = (0 \<Colon> sz)\<close>
  unfolding bv_times.simps by simp_all

function 
  bv_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>div\<^sub>b\<^sub>v\<close> 56) (* TODO *)
where
  \<open>(nat\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 div nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) div\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_divide.simps[simp del]

lemma divide0[simp]: \<open>(0 \<Colon> sz) div\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (0 \<Colon> sz)\<close>
  unfolding bv_divide.simps by simp_all

function
  bv_sdivide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>div\<^sub>s\<^sub>b\<^sub>v\<close> 56) (* TODO *)
where
  \<open>(nat\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 div nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) div\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

declare bv_sdivide.simps[simp del]

function 
  bv_land :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>&\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((and nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) &\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 &\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

declare bv_land.simps[simp del]

lemma land0[simp]: \<open>(0 \<Colon> sz) &\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (0 \<Colon> sz)\<close> \<open>(nat\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (0 \<Colon> sz) = (0 \<Colon> sz)\<close>
  unfolding bv_land.simps by simp_all

lemma land_true[simp]:
    \<open>true &\<^sub>b\<^sub>v true = true\<close>
  unfolding  bv_land.simps and.idem by auto

function
  bv_lor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>|\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((or nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) |\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 |\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_lor.simps[simp del]

lemma lor0[simp]: \<open>(0 \<Colon> sz) |\<^sub>b\<^sub>v (num \<Colon> sz) = (num \<Colon> sz)\<close> \<open>(num \<Colon> sz) |\<^sub>b\<^sub>v (0 \<Colon> sz) = (num \<Colon> sz)\<close>
  unfolding bv_lor.simps by simp_all

lemma lor_true[simp]: 
    \<open>true |\<^sub>b\<^sub>v true = true\<close>
  unfolding   bv_lor.simps or_one_eq one_or_eq by simp_all

function
  bv_xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>xor\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((Bit_Operations.xor nat\<^sub>1 nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) xor\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 xor\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_xor.simps[simp del]

lemma xor0[simp]: \<open>(num \<Colon> sz) xor\<^sub>b\<^sub>v (0 \<Colon> sz) = (num \<Colon> sz)\<close> \<open>(0 \<Colon> sz) xor\<^sub>b\<^sub>v (num \<Colon> sz) = (num \<Colon> sz)\<close>
  unfolding bv_xor.simps by simp_all

lemma xor_eq[simp]: \<open>(num \<Colon> sz) xor\<^sub>b\<^sub>v (num \<Colon> sz) = (0 \<Colon> sz)\<close>
  unfolding bv_xor.simps by simp_all


function
  bv_mod\<^sub>b\<^sub>v :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>%\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 % nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) %\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_mod\<^sub>b\<^sub>v.simps[simp del]

lemma mod0[simp]: \<open>(0 \<Colon> sz) %\<^sub>b\<^sub>v (num \<Colon> sz) = (0 \<Colon> sz)\<close> \<open>(num \<Colon> sz) %\<^sub>b\<^sub>v (0 \<Colon> sz) = (num \<Colon> sz)\<close>
  unfolding bv_mod\<^sub>b\<^sub>v.simps by simp_all

function
  bv_smod :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>%\<^sub>s\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = ((nat\<^sub>1 % nat\<^sub>2) \<Colon> sz)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) %\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_smod.simps[simp del]

function
  bv_lsl :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><<\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2) = (((nat\<^sub>1 * (2 ^ nat\<^sub>2)) mod 2 ^ sz\<^sub>1) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <<\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_lsl.simps[simp del]

lemma lsl0[simp]:
    \<open>(0 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (num \<Colon> sz\<^sub>2) = (0 \<Colon> sz\<^sub>1)\<close>
  unfolding bv_lsl.simps by simp_all

function
  bv_lsr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>>>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2) = ((nat\<^sub>1 div (2 ^ nat\<^sub>2)) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 >>\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_lsr.simps[simp del]

lemma lsr0[simp]:
    \<open>(0 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (num \<Colon> sz\<^sub>2) = (0 \<Colon> sz\<^sub>1)\<close> \<open>(num \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (0 \<Colon> sz\<^sub>2) = (num \<Colon> sz\<^sub>1)\<close>
  unfolding bv_lsr.simps by simp_all

function
  bv_asr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>>>>\<^sub>b\<^sub>v\<close> 56)  
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) >>>\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> _) = (((and nat\<^sub>1 ((2 ^ nat\<^sub>2) div 2)) + (nat\<^sub>1 div (2 ^ nat\<^sub>2))) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 >>>\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

declare bv_asr.simps[simp del]

lemma asr0[simp]:
    \<open>(0 \<Colon> sz\<^sub>1) >>>\<^sub>b\<^sub>v (num \<Colon> sz\<^sub>2) = (0 \<Colon> sz\<^sub>1)\<close> \<open>(num \<Colon> sz\<^sub>1) >>>\<^sub>b\<^sub>v (0 \<Colon> sz\<^sub>2) = (num \<Colon> sz\<^sub>1)\<close>
  unfolding bv_asr.simps by simp_all

function 
  bv_concat :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<cdot>\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (nat\<^sub>2 \<Colon> sz\<^sub>2) = (nat (concat_bit sz\<^sub>2 (of_nat nat\<^sub>2) (of_nat nat\<^sub>1)) \<Colon> (sz\<^sub>1 + sz\<^sub>2))\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 \<cdot> w\<^sub>2 = undefined\<close>
  apply (rule bv2_pattern_complete, blast)
  by auto
termination by (standard, auto)

declare bv_concat.simps[simp del]

lemma concat0: \<open>(0 \<Colon> sz\<^sub>1) \<cdot> (0 \<Colon> sz\<^sub>2) = (0 \<Colon> sz\<^sub>1 + sz\<^sub>2)\<close>
  unfolding bv_concat.simps by auto

function
  bv_uminus :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>-\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>-\<^sub>b\<^sub>v (nat\<^sub>1 \<Colon> sz\<^sub>1) = (nat\<^sub>1 \<Colon> sz\<^sub>1)\<close> | (* TODO *)
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> -\<^sub>b\<^sub>v w\<^sub>1 = undefined\<close>
  apply (rule bv_pattern_complete, blast)
  by auto

termination by (standard, auto)

declare bv_uminus.simps[simp del]

function
  bv_negation :: \<open>'a \<Rightarrow> 'a\<close> (\<open>~\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>~\<^sub>b\<^sub>v (nat\<^sub>1 \<Colon> sz\<^sub>1) = ((2 ^ sz\<^sub>1 - 1 - nat\<^sub>1) \<Colon> sz\<^sub>1)\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> ~\<^sub>b\<^sub>v w\<^sub>1 = undefined\<close>
  apply (rule bv_pattern_complete, blast)
  by auto
termination by (standard, auto)

declare bv_negation.simps[simp del]

lemma bv_negation_true_false[simp]: \<open>~\<^sub>b\<^sub>v true = false\<close>
  unfolding   bv_negation.simps by auto

lemma bv_negation_false_true[simp]: \<open>~\<^sub>b\<^sub>v false = true\<close>
  unfolding   bv_negation.simps by auto

function
  bv_lt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (if nat\<^sub>1 < nat\<^sub>2 then true else false)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) <\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto
termination by (standard, auto)

lemma bv_lt_true: \<open>nat\<^sub>1 < nat\<^sub>2 \<Longrightarrow> (nat\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = true\<close>
  by auto

lemma bv_lt_false: \<open>nat\<^sub>1 \<ge> nat\<^sub>2 \<Longrightarrow> (nat\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = false\<close>
  by auto

lemma bv_lt_true_or_false: \<open>(num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = ((if num\<^sub>1 < num\<^sub>2 then Suc 0 else 0) \<Colon> Suc 0)\<close>
  unfolding bv_lt.simps apply (split if_splits)+
  by simp

lemma not_lt_false[simp]:
  \<open>(~\<^sub>b\<^sub>v ((a \<Colon> sz) <\<^sub>b\<^sub>v (b \<Colon> sz)) = false) \<longleftrightarrow> ((a \<Colon> sz) <\<^sub>b\<^sub>v (b \<Colon> sz)) = true\<close>
  by auto

declare bv_lt.simps[simp del]

lemma lt0[simp]: \<open>(num \<Colon> sz) <\<^sub>b\<^sub>v (0 \<Colon> sz) = false\<close>
  unfolding bv_lt.simps by simp_all

lemma lt_same[simp]: \<open>(num \<Colon> sz) <\<^sub>b\<^sub>v (num \<Colon> sz) = false\<close>
  unfolding bv_lt.simps by simp_all

function
  bv_slt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open><\<^sub>s\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(nat\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz) = (if nat\<^sub>1 < nat\<^sub>2 then true else false)\<close> |
  \<open>\<lbrakk>sz\<^sub>1 \<noteq> sz\<^sub>2\<rbrakk> \<Longrightarrow> (_ \<Colon> sz\<^sub>1) <\<^sub>s\<^sub>b\<^sub>v (_ \<Colon> sz\<^sub>2) = undefined\<close> |
  \<open>\<lbrakk>(\<forall>nat sz. w\<^sub>1 \<noteq> (nat \<Colon> sz)) \<or> (\<forall>nat sz. w\<^sub>2 \<noteq> (nat \<Colon> sz))\<rbrakk> \<Longrightarrow> w\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = undefined\<close>
  apply (rule bv_eq_sz_pattern_complete, blast+)
  by auto

termination by (standard, auto)

declare bv_slt.simps[simp del]

function
  xtract :: \<open>'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>ext _ \<sim> hi : _ \<sim> lo : _\<close>)
where
  \<open>(ext (nat\<^sub>1 \<Colon> _) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = (take_bit (Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w)) (drop_bit sz\<^sub>l\<^sub>o\<^sub>w nat\<^sub>1) \<Colon> (Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w)))\<close> |
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

lemma extract0[simp]: \<open>(ext 0 \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = 0 \<Colon> Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w)\<close>
  unfolding xtract.simps by auto

lemma extract_to_sz: 
  assumes \<open>sz > 0\<close> and \<open>y < 2 ^ sz\<close> 
    shows \<open>(ext y \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0) = y \<Colon> sz\<close>
  using assms 
  by (metis Suc_pred add.commute diff_Suc_eq_diff_pred drop_bit_0 id_apply plus_1_eq_Suc take_bit_nat_eq_self_iff xtract.simps(1))

lemma extract_full:
  assumes \<open>num < 2 ^ sz\<close> and \<open>sz > 0\<close> shows \<open>(ext num \<Colon> sz \<sim> hi : (sz - 1) \<sim> lo : 0) = (num \<Colon> sz)\<close>
  using assms extract_to_sz by blast
  
lemma extract_concat32:
  assumes \<open>x < 2 ^ 32\<close>
    shows \<open>((((ext x \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext x \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot>
               ext x \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<cdot> ext x \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) = x \<Colon> 32\<close>
  unfolding xtract.simps bv_concat.simps apply simp
  unfolding of_nat_take_bit of_nat_drop_bit
  unfolding concat_bit_take_bit_eq
  apply (unfold concat_bit_drop_bit, simp)+
  by (metis add_One_commute assms concat_take_drop_bit_nat_eq_self numeral_plus_numeral semiring_norm(2) semiring_norm(4) semiring_norm(6))

lemma extract_concat64:
  assumes \<open>x < 2 ^ 64\<close>
    shows \<open>((((((((ext x \<Colon> sz \<sim> hi : 63 \<sim> lo : 56) \<cdot> ext x \<Colon> sz \<sim> hi : 55 \<sim> lo : 48) \<cdot>
                   ext x \<Colon> sz \<sim> hi : 47 \<sim> lo : 40) \<cdot> ext x \<Colon> sz \<sim> hi : 39 \<sim> lo : 32) \<cdot>
                   ext x \<Colon> sz \<sim> hi : 31 \<sim> lo : 24) \<cdot> ext x \<Colon> sz \<sim> hi : 23 \<sim> lo : 16) \<cdot>
                   ext x \<Colon> sz \<sim> hi : 15 \<sim> lo :  8) \<cdot> ext x \<Colon> sz \<sim> hi :  7 \<sim> lo :  0) = (x \<Colon> 64)\<close>
  unfolding xtract.simps bv_concat.simps apply simp
  unfolding of_nat_take_bit of_nat_drop_bit
  unfolding concat_bit_take_bit_eq
  apply (unfold concat_bit_drop_bit, simp)+
  by (metis add_One_commute assms concat_take_drop_bit_nat_eq_self numeral_plus_numeral semiring_norm(2) semiring_norm(4) semiring_norm(6))


lemma xtract_concat_consecutive:
  assumes \<open>x2 > x3\<close> \<open>x3 > x4\<close>
    shows \<open>(ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x3) \<cdot> (ext num \<Colon> x1 \<sim> hi : x3 - 1 \<sim> lo : x4) = (ext num \<Colon> x1 \<sim> hi : x2 \<sim> lo : x4)\<close>
unfolding xtract.simps bv_concat.simps proof auto
  have sz_simp1: \<open>(Suc (x2 - x3) + Suc (x3 - Suc x4)) = (Suc (x2 - x4))\<close>
    using assms by fastforce
  have sz_simp2: \<open>Suc (x3 - Suc x4) + x4 = x3\<close>
    using assms by fastforce
  show \<open>nat (concat_bit (Suc (x3 - Suc x4)) (int (take_bit (Suc (x3 - Suc x4)) (drop_bit x4 num)))
          (int (take_bit (Suc (x2 - x3)) (drop_bit x3 num)))) = take_bit (Suc (x2 - x4)) (drop_bit x4 num)\<close>
    using nat_concat_bit_take_bit_drop_bit2[of \<open>Suc (x3 - Suc x4)\<close> x4 num \<open>Suc (x2 - x3)\<close>, unfolded sz_simp1 sz_simp2]    
    by blast
next
  show \<open>Suc (x2 - x3 + (x3 - Suc x4)) = x2 - x4\<close>
    using assms by fastforce
qed


lemma nested_extract_within': 
  assumes  \<open>sz\<^sub>l\<^sub>o' \<le> sz\<^sub>h\<^sub>i'\<close> and \<open>sz\<^sub>h\<^sub>i' + sz\<^sub>l\<^sub>o \<le> sz\<^sub>h\<^sub>i\<close>
    shows \<open>(ext (ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) \<sim> hi : sz\<^sub>h\<^sub>i' \<sim> lo : sz\<^sub>l\<^sub>o') = (ext num \<Colon> sz \<sim> hi : (sz\<^sub>h\<^sub>i' + sz\<^sub>l\<^sub>o) \<sim> lo : (sz\<^sub>l\<^sub>o' + sz\<^sub>l\<^sub>o))\<close>
  using assms unfolding xtract.simps take_bit_drop_bit by auto


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

lemma bv_eq[simp]: \<open>a =\<^sub>b\<^sub>v a = true\<close>
  unfolding bv_eq_def by simp

lemma bv_not_eq: \<open>a \<noteq> b \<Longrightarrow> a =\<^sub>b\<^sub>v b = false\<close>
  unfolding bv_eq_def by simp


lemma and_eq_true[simp]: \<open>((num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) &\<^sub>b\<^sub>v true = (num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  using bv_land.simps  bv_eq_def (*local. local.*) by fastforce  

lemma and_eq_false[simp]: \<open>((num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) &\<^sub>b\<^sub>v false = false\<close>
using bv_land.simps bv_eq_def (*local. local.*) by fastforce    


abbreviation 
  bv_neq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<noteq>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<noteq>\<^sub>b\<^sub>v b \<equiv> ~\<^sub>b\<^sub>v (a =\<^sub>b\<^sub>v b)\<close>

lemma bv_eq_neq[simp]: \<open>(num \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num \<Colon> sz) = false\<close>
  unfolding bv_eq bv_negation_true_false ..

lemma bv_neq_true: \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2) \<Longrightarrow> (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true\<close>
  using bv_negation_false_true bv_not_eq by presburger

lemma bv_neq_true_false[simp]: \<open>true \<noteq>\<^sub>b\<^sub>v false = true\<close>
  using bv_negation_false_true bv_not_eq  by simp

lemma bv_neq_false_true[simp]: \<open>false \<noteq>\<^sub>b\<^sub>v true  = true\<close>
  using bv_negation_false_true bv_not_eq by (simp add: bv_eq_def)

lemma bv_not_eq_same_sz_true: assumes \<open>num\<^sub>1 \<noteq> num\<^sub>2\<close> shows \<open>(num\<^sub>1 \<Colon> sz) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
  using assms bv_neq_true by simp

abbreviation
  bv_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<le>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<le>\<^sub>b\<^sub>v b \<equiv> (a =\<^sub>b\<^sub>v b) |\<^sub>b\<^sub>v (a <\<^sub>b\<^sub>v b)\<close>

lemmas bv_leq_defs = bv_eq_def bv_lor.simps bv_lt.simps

lemma bv_leq_true_or_false: \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = ((if num\<^sub>1 \<le> num\<^sub>2 then Suc 0 else 0) \<Colon> Suc 0)\<close>
  unfolding bv_leq_defs apply (split if_splits)+
  by simp

lemma bv_leq_same_szI: assumes \<open>num\<^sub>1 \<le> num\<^sub>2\<close> shows \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true\<close>
  using assms unfolding bv_leq_defs by auto

lemma bv_leq_same[simp]: \<open>(num \<Colon> sz) \<le>\<^sub>b\<^sub>v (num \<Colon> sz) = true\<close>
  apply (rule bv_leq_same_szI)
  ..

abbreviation
  bv_sleq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<le>\<^sub>s\<^sub>b\<^sub>v\<close> 56)
where
  \<open>a \<le>\<^sub>s\<^sub>b\<^sub>v b \<equiv> (a =\<^sub>b\<^sub>v b) |\<^sub>b\<^sub>v (a <\<^sub>s\<^sub>b\<^sub>v b)\<close>

function
  succ :: \<open>'a \<Rightarrow> 'a\<close>
where
  succI: \<open>succ (num \<Colon> sz) = (num \<Colon> sz) +\<^sub>b\<^sub>v (1 \<Colon> sz)\<close> |
  \<open>\<lbrakk>\<forall>num sz. w \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> succ w = undefined\<close>
  subgoal for P x
    apply (rule word_syntax_exhaust[of x])
    by blast+    
  by auto
termination
  by (standard, auto)

declare succ.simps[simp del]

lemma succ_plus: \<open>succ ((x \<Colon> sz) +\<^sub>b\<^sub>v (y \<Colon> sz)) = ((x \<Colon> sz) +\<^sub>b\<^sub>v (Suc y \<Colon> sz))\<close>
  unfolding succ.simps bv_plus.simps mod_simps by auto


(* TODO MOVE *)

lemma succ_plus_lhs: \<open>succ ((x \<Colon> sz) +\<^sub>b\<^sub>v (y \<Colon> sz)) = (x \<Colon> sz) +\<^sub>b\<^sub>v succ (y \<Colon> sz)\<close>
  unfolding succ.simps bv_plus.simps mod_simps by auto


lemma succ_plus_lhs_is_word:
  assumes \<open>\<exists>num. w\<^sub>1 = (num \<Colon> sz)\<close> \<open>\<exists>num. w\<^sub>2 = (num \<Colon> sz)\<close>
    shows \<open>succ (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) = w\<^sub>1 +\<^sub>b\<^sub>v succ w\<^sub>2\<close>
  using assms apply safe
  by (rule succ_plus_lhs)

lemma is_word[simp]: \<open>\<exists>num. num' \<Colon> sz = num \<Colon> sz\<close>
  by auto

lemma plus_is_word[intro]: 
  assumes \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close>
    shows \<open>\<exists>num. w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 = num \<Colon> sz\<close>
  using assms apply auto
  unfolding bv_plus.simps by auto

lemma minus_is_word[intro]: 
  assumes \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close>
    shows \<open>\<exists>num. w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2 = num \<Colon> sz\<close>
  using assms apply auto
  unfolding bv_minus.simps by auto

lemma succ_is_word[intro]:
  assumes \<open>\<exists>num. w = num \<Colon> sz\<close>
    shows \<open>\<exists>num. succ w = num \<Colon> sz\<close>
  using assms apply auto
  unfolding succ.simps by auto

lemma bv_plus_neq_lhsI:
  assumes \<open>(y \<Colon> sz) is ok\<close> \<open>(z \<Colon> sz) is ok\<close> \<open>y \<noteq> z\<close>
    shows \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v (y \<Colon> sz) \<noteq> (x \<Colon> sz) +\<^sub>b\<^sub>v (z \<Colon> sz)\<close>
  using assms   unfolding bv_plus.simps succ.simps mod_simps word_is_ok apply (elim conjE)
  apply (intro word_not_sz_neqI conjI plus_mod_neq_lhs)
  .

lemma bv_plus_neq_lhs_is_wordI:
  fixes w\<^sub>1 :: 'a
  assumes \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close>
      and \<open>w\<^sub>1 is ok\<close> \<open>w\<^sub>2 is ok\<close> \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    shows \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v w\<^sub>1 \<noteq> (x \<Colon> sz) +\<^sub>b\<^sub>v w\<^sub>2\<close>
  using assms apply (elim exE, simp only:)
  apply (rule bv_plus_neq_lhsI)
  by auto

(*
lemma plus_is_okI': (* TODO *)
  assumes ex: \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close>
      and w_is_ok: \<open>w\<^sub>1 is ok\<close> \<open>w\<^sub>2 is ok\<close>
    shows \<open>(w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) is ok\<close>
  using ex w_is_ok apply auto
  unfolding word_is_ok bv_plus.simps by auto

lemma succ_is_okI: (* TODO *)
  assumes ex: \<open>\<exists>num. w = num \<Colon> sz\<close> and sz: \<open>0 < sz\<close>
    shows \<open>succ w is ok\<close>
  using ex sz apply auto
  unfolding succ.simps word_is_ok apply (intro plus_is_okI word_is_okI)
  by auto
*)

lemmas bv_simps = bv_plus.simps bv_minus.simps bv_times.simps bv_divide.simps bv_sdivide.simps
                  bv_inc.simps bv_land.simps bv_lor.simps bv_xor.simps bv_mod\<^sub>b\<^sub>v.simps bv_smod.simps
                  bv_lsl.simps bv_lsr.simps bv_asr.simps bv_concat.simps bv_uminus.simps
                  bv_negation.simps bv_lt.simps bv_slt.simps xtract.simps sxtract.simps




text \<open>Type syntax for words\<close>

lemma type_plusI[simp]: \<open>type ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) = imm\<langle>sz\<rangle>\<close>
  unfolding bv_plus.simps by (rule type_wordI)

lemma type_succI[simp]: \<open>type (succ (num \<Colon> sz)) = imm\<langle>sz\<rangle>\<close>
  unfolding succ.simps by (rule type_plusI)

lemma word_is_okI[intro]: 
  assumes \<open>sz > 0\<close> and \<open>num < 2 ^ sz\<close>
    shows \<open>(num \<Colon> sz) is ok\<close>
  using assms unfolding word_is_ok by blast

lemma word_is_okE[elim]: 
  assumes \<open>(num \<Colon> sz) is ok\<close>
  obtains \<open>sz > 0\<close> \<open>num < 2 ^ sz\<close>
  using assms unfolding word_is_ok by blast

lemma plus_is_okI[intro]: 
  assumes sz: \<open>0 < sz\<close>
  shows \<open>((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
using assms proof -
  show "((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok"
    unfolding bv_plus.simps using sz apply (rule word_is_okI)
    by auto
qed

lemma plus_word_is_okI:
  assumes ex: \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close> 
      and sz: \<open>0 < sz\<close>
  shows \<open>(w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2) is ok\<close>
  using assms by auto

lemma minus_is_okI[intro]:
  assumes word1_is_ok: \<open>(num\<^sub>1 \<Colon> sz) is ok\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
using assms proof (elim word_is_okE)
  fix num\<^sub>1 num\<^sub>2 :: nat
  assume sz: "0 < sz" and num\<^sub>1_lt: "num\<^sub>1 < 2 ^ sz"
  show "((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok"
    unfolding bv_minus.simps using sz apply (rule word_is_okI)
    using num\<^sub>1_lt by fastforce
qed

lemma minus_word_is_okI:
  assumes ex: \<open>\<exists>num. w\<^sub>1 = num \<Colon> sz\<close> \<open>\<exists>num. w\<^sub>2 = num \<Colon> sz\<close> 
      and word1_is_ok: \<open>w\<^sub>1 is ok\<close>
    shows \<open>(w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2) is ok\<close>
  using assms by auto

lemma extract_is_okI[intro]:
    shows \<open>(ext num \<Colon> sz \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) is ok\<close>
  unfolding xtract.simps apply (rule word_is_okI)
  by (auto simp add: take_bit_eq_mod)

lemma extract_word_is_okI:
  assumes \<open>\<exists>num. w = num \<Colon> sz\<close>
    shows \<open>(ext w \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o) is ok\<close>
  using assms by auto


lemma bv_times_ok:
  assumes \<open>0 < sz\<close>                       
    shows \<open>((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  unfolding bv_times.simps using assms apply (rule word_is_okI) 
  by simp

lemma bv_divide_ok:
  assumes \<open>0 < sz\<close> and \<open>num\<^sub>1 < 2 ^ sz\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) is ok\<close>
  unfolding bv_divide.simps using assms(1) apply (rule word_is_okI)
  using assms(2) div_le_dividend le_trans verit_comp_simplify1(3)
  by (meson)

lemma concat_word_is_okI:
  assumes \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) is ok\<close> and \<open>(num\<^sub>2 \<Colon> sz\<^sub>2) is ok\<close>
    shows \<open>((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) is ok\<close>
  apply (insert assms) 
  apply (erule word_is_okE)+
  unfolding bv_concat.simps apply (rule word_is_okI)
  subgoal by blast
  subgoal
    unfolding concat_bit_def nat_less_numeral_power_cancel_iff apply (rule OR_upper)
    subgoal by (rule take_bit_nonnegative)
    subgoal
      using add.commute le_add1 nat_int nat_less_iff take_bit_int_less_self_iff take_bit_nat_eq_self take_bit_nonnegative take_bit_of_nat take_bit_tightened_less_eq_nat verit_comp_simplify1(3)
      by metis
    subgoal
      using add.commute push_bit_take_bit take_bit_int_eq_self_iff take_bit_of_nat take_bit_nat_eq_self
      by metis
    .
  .

lemma succ_is_okI:
  assumes ex: \<open>\<exists>num. w = num \<Colon> sz\<close> and sz: \<open>sz > 0\<close>
    shows \<open>succ w is ok\<close>
  using ex apply auto
  unfolding succ.simps word_is_ok apply (intro plus_is_okI word_is_okI)
  using sz by auto

lemma succ_is_okI':
  assumes ex: \<open>\<exists>num. w = num \<Colon> sz\<close> and w_is_ok: \<open>w is ok\<close>
    shows \<open>succ w is ok\<close>
  using ex w_is_ok apply auto
  unfolding succ.simps word_is_ok apply (intro plus_is_okI word_is_okI)
  using less_exp power_lt_min by blast+

\<comment> \<open>BIL formalisation lemma\<close>

lemmas TWF_WORD = word_is_okI

method is_word uses add = (
  rule add is_word succ_is_word plus_is_word minus_is_word; is_word add: add
)

method typec_word_is_ok uses add = ((
  rule add word_is_okI plus_is_okI; (rule add | solves \<open>simp\<close>)) |
  (rule plus_word_is_okI, is_word add: add, is_word add: add, linarith) |
  (rule minus_word_is_okI, is_word add: add, is_word add: add, typec_word_is_ok add: add) |
  (rule succ_is_okI, is_word add: add, linarith) |
  (rule succ_is_okI', is_word add: add, typec_word_is_ok add: add) |
  (rule extract_word_is_okI, is_word add: add)
)


lemma word_typed_diff: \<open>\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz'\<rangle> \<Longrightarrow> sz = sz'\<close>
  unfolding word_typed_ok by auto

lemma word_not_mem: \<open>\<not>(\<Gamma> \<turnstile> (num \<Colon> sz) :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>)\<close>
  unfolding word_typed_ok by auto



lemma word_typed_okI:
  assumes \<open>\<Gamma> is ok\<close> and \<open>(num \<Colon> sz) is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  using assms unfolding word_typed_ok by blast

lemma word_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> is ok \<and> (num \<Colon> sz) is ok\<close>
  using assms unfolding word_typed_ok by blast

lemma bv_uminus_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> num \<Colon> sz :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> -\<^sub>b\<^sub>v (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  using assms unfolding bv_uminus.simps by auto

lemma bv_negation_typed_okI:
  assumes \<open>\<Gamma> is ok\<close> and \<open>0 < sz\<close>
    shows \<open>\<Gamma> \<turnstile> ~\<^sub>b\<^sub>v (num \<Colon> sz) :: imm\<langle>sz\<rangle>\<close>
  unfolding bv_negation.simps using assms(1) apply (rule word_typed_okI) 
  using assms(2) apply (rule TWF_WORD)
  by simp
(*
lemma bool_word_is_ok_exhaust:
  assumes \<open>\<Gamma> \<turnstile> w :: imm\<langle>1\<rangle>\<close>
  obtains 
    (True) \<open>w = true\<close>
  | (False) \<open>w = false\<close>
  | (NotWord) \<open>\<forall>nat sz. w \<noteq> (nat \<Colon> sz)\<close>
  using assms apply (rule_tac word_syntax_exhaust[of w])
  subgoal for nat sz
    apply clarify
    apply (frule word_typed_diff, clarify)
    apply (frule word_typed_okE)
    apply (rule bool_is_ok_exhaust)
    by blast+
  by simp
*)
lemma concat_word_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> num\<^sub>1 \<Colon> sz\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> num\<^sub>2 \<Colon> sz\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  apply (insert assms) 
  apply (drule word_typed_okE)+
  apply (elim conjE)
  unfolding bv_concat.simps apply (rule word_typed_okI)
  subgoal by blast
  subgoal
    unfolding bv_concat.simps[symmetric] by (rule concat_word_is_okI)
  .

lemmas T_INT = word_typed_okI


end



class word = word_constructor + (* TODO TERMINATE! *)
  assumes word_induct: \<open>\<And>w Q. \<lbrakk>\<And>a b. Q (a \<Colon> b)\<rbrakk> \<Longrightarrow> Q w\<close>
      and word_exhaust[case_names Word]: \<open>\<And>w Q. \<lbrakk>\<And>a b. w = (a \<Colon> b) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>
begin

lemma type_succ_recI: 
  assumes \<open>type w = imm\<langle>sz\<rangle>\<close>
    shows \<open>type (succ w) = imm\<langle>sz\<rangle>\<close>
  using assms apply (cases w rule: word_exhaust, safe)
  by (simp add: type_wordI)

end

datatype word = Word nat nat

end
