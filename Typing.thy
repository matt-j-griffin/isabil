theory Typing
  imports Context_Syntax
begin

text \<open>\<Gamma> \<turnstile> bil is ok\<close>

text \<open>\<Gamma> is ok\<close>
text \<open>t is ok\<close>
           

consts is_ok :: \<open>'a \<Rightarrow> bool\<close> (\<open>_ is ok\<close>)

overloading
  is_ok_Type \<equiv> \<open>is_ok :: Type \<Rightarrow> bool\<close>
  is_ok_TypingContext \<equiv> \<open>is_ok :: TypingContext \<Rightarrow> bool\<close>
begin

primrec 
  is_ok_Type :: \<open>Type \<Rightarrow> bool\<close>
where 
  \<open>is_ok_Type (Imm sz) = (sz > 0)\<close> |
  \<open>is_ok_Type (Mem sz\<^sub>1 sz\<^sub>2) = (sz\<^sub>1 > 0 \<and> sz\<^sub>2 > 0)\<close>

primrec
  is_ok_TypingContext :: \<open>TypingContext \<Rightarrow> bool\<close>
where 
  \<open>is_ok_TypingContext [] = True\<close> |
  \<open>is_ok_TypingContext (a # \<Gamma>) = (let (name, t) = a in (name \<notin> dom\<^sub>\<Gamma> \<Gamma> \<and> (t is ok) \<and> (\<Gamma> is ok)))\<close>

end

lemma set_not_\<Gamma>_is_ok:
    fixes \<Gamma> :: TypingContext
  assumes \<open>(x, sz\<^sub>1) \<in> set \<Gamma>\<close>
      and \<open>(x, sz\<^sub>2) \<in> set \<Gamma>\<close>
      and \<open>sz\<^sub>1 \<noteq> sz\<^sub>2\<close>
    shows \<open>\<not>(\<Gamma> is ok)\<close>
  using assms apply (induct \<Gamma>)
  apply (auto simp add: dom\<^sub>\<Gamma>_def)
  apply (metis fst_eqD imageI)
  by (metis fst_eqD rev_image_eqI)


consts typing_expression :: \<open>TypingContext \<Rightarrow> 'a \<Rightarrow> Type \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ :: _\<close>)

overloading
  typing_expression_val \<equiv> \<open>typing_expression :: TypingContext \<Rightarrow> val \<Rightarrow> Type \<Rightarrow> bool\<close>
  typing_expression_exp \<equiv> \<open>typing_expression :: TypingContext \<Rightarrow> exp \<Rightarrow> Type \<Rightarrow> bool\<close>
begin

fun 
  typing_expression_val :: \<open>TypingContext \<Rightarrow> val \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typing_expression_val \<Gamma> (Immediate (num \<Colon> sz')) (Imm sz) = (sz = sz' \<and> sz > 0 \<and> (\<Gamma> is ok))\<close> |
  \<open>typing_expression_val \<Gamma> (Unknown str t) t' = (t = t' \<and> (t is ok) \<and> (\<Gamma> is ok))\<close> |
  \<open>typing_expression_val \<Gamma> (Storage v w v' sz) (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz') = (sz = sz' \<and> sz > 0 \<and> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r > 0 \<and> 
       (\<Gamma> \<turnstile> v' :: (Imm sz)) \<and> bits w = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<and> (\<Gamma> \<turnstile> v :: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz')))\<close> |
  \<open>typing_expression_val \<Gamma> v t = False\<close>
fun 
  typing_expression_exp :: \<open>TypingContext \<Rightarrow> exp \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typing_expression_exp \<Gamma> (Var (name, t')) t = (t = t' \<and> (name, t') \<in> set \<Gamma> \<and> (\<Gamma> is ok))\<close> |
  \<open>typing_expression_exp \<Gamma> (Load e\<^sub>1 e\<^sub>2 ed sz') (Imm sz'') = (sz'' = sz' \<and> sz' > 0 \<and> (\<exists>sz sz\<^sub>m\<^sub>e\<^sub>m. sz' mod sz = 0 \<and> 
                                             (\<Gamma> \<turnstile> e\<^sub>1 :: (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>m\<^sub>e\<^sub>m))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Store e\<^sub>1 e\<^sub>2 ed sz' e\<^sub>3) (Mem sz\<^sub>m\<^sub>e\<^sub>m sz) = (sz' mod sz = 0 \<and> sz' > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: (Imm sz'))
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>m\<^sub>e\<^sub>m)) 
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)))\<close> |
  \<open>typing_expression_exp \<Gamma> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) (Imm sz) = ((\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz)) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz)))\<close> |
  \<open>typing_expression_exp \<Gamma> (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) (Imm (Suc 0)) = (\<exists>sz. (\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz)) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz)))\<close> | 
  \<open>typing_expression_exp \<Gamma> (UnOp uop e) (Imm sz) = (\<Gamma> \<turnstile> e :: (Imm sz))\<close> |
  \<open>typing_expression_exp \<Gamma> (Cast Unsigned sz e) (Imm sz'') = (sz > 0 \<and> sz = sz'' \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: (Imm sz'))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Cast Signed sz e) (Imm sz'') = (sz > 0 \<and> sz = sz'' \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: (Imm sz'))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Cast High sz e) (Imm sz'') = (sz > 0 \<and> sz = sz'' \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: (Imm sz'))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Cast Low sz e) (Imm sz'') = (sz > 0 \<and> sz = sz'' \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: (Imm sz'))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Let (name, t) e\<^sub>1 e\<^sub>2) t' = ((\<Gamma> \<turnstile> e\<^sub>1 :: t) \<and> (((name, t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'))\<close> |
  \<open>typing_expression_exp \<Gamma> (Val v) t = (\<Gamma> \<turnstile> v :: t)\<close> |
  \<open>typing_expression_exp \<Gamma> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) t = ((\<Gamma> \<turnstile> e\<^sub>1 :: (Imm 1)) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: t) \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: t))\<close> |
  \<open>typing_expression_exp \<Gamma> (Extract sz\<^sub>1 sz\<^sub>2 e) (Imm sz\<^sub>e\<^sub>x\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>t) = (sz\<^sub>e\<^sub>x\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>t = sz\<^sub>1 - sz\<^sub>2 + 1 \<and> sz\<^sub>1 \<ge> sz\<^sub>2 \<and>
                                              (\<exists>sz. (\<Gamma> \<turnstile> e :: (Imm sz))))\<close> |
  \<open>typing_expression_exp \<Gamma> (Concat e\<^sub>1 e\<^sub>2) (Imm sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) = (\<exists>sz\<^sub>1 sz\<^sub>2. sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t = sz\<^sub>1 + sz\<^sub>2 \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz\<^sub>1)) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>2)))\<close> |
  \<open>typing_expression_exp \<Gamma> e t = False\<close>
end


consts judgement_is_ok :: \<open>TypingContext \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ is ok\<close>)

overloading 
  is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<equiv> \<open>judgement_is_ok :: TypingContext \<Rightarrow> stmt \<Rightarrow> bool\<close>
  is_ok\<^sub>b\<^sub>i\<^sub>l \<equiv> \<open>judgement_is_ok :: TypingContext \<Rightarrow> bil \<Rightarrow> bool\<close>
begin

fun 
  is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t :: \<open>TypingContext \<Rightarrow> stmt \<Rightarrow> bool\<close> and
  is_ok\<^sub>b\<^sub>i\<^sub>l :: \<open>TypingContext \<Rightarrow> bil \<Rightarrow> bool\<close>
where
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (Move (name, t) e) = ((\<Gamma> \<turnstile> (Var (name, t)) :: t) \<and> (\<Gamma> \<turnstile> e :: t))\<close> |
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (Jmp e) = (\<exists>sz. (\<Gamma> \<turnstile> e :: (Imm sz)))\<close> |
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (CpuExn _) = (\<Gamma> is ok)\<close> |
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (Special _) = (\<Gamma> is ok)\<close> |
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (While e seq) = ((\<Gamma> \<turnstile> seq is ok) \<and> (\<Gamma> \<turnstile> e :: (Imm 1)))\<close> |
  \<open>is_ok\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<Gamma> (If e seq\<^sub>1 seq\<^sub>2) = ((\<Gamma> \<turnstile> seq\<^sub>1 is ok) \<and> (\<Gamma> \<turnstile> seq\<^sub>2 is ok) \<and> (\<Gamma> \<turnstile> e :: (Imm 1)))\<close> |
  \<open>is_ok\<^sub>b\<^sub>i\<^sub>l \<Gamma> Empty = True\<close> |
  \<open>is_ok\<^sub>b\<^sub>i\<^sub>l \<Gamma> (Stmt stmt seq) = ((\<Gamma> \<turnstile> stmt is ok) \<and> (\<Gamma> \<turnstile> seq is ok))\<close>

end


section \<open>\<Gamma> \<turnstile> bil is ok\<close>


lemma T_SEQ_ONE:
    fixes stmt :: stmt
  assumes \<open>\<Gamma> \<turnstile> stmt is ok\<close>
    shows \<open>\<Gamma> \<turnstile> Stmt stmt Empty is ok\<close>
  using assms by auto

lemma T_SEQ_REC:
  assumes \<open>\<Gamma> \<turnstile> stmt is ok\<close>
      and \<open>\<Gamma> \<turnstile> seq is ok\<close>
    shows \<open>\<Gamma> \<turnstile> Stmt stmt seq is ok\<close>
  using assms is_ok\<^sub>b\<^sub>i\<^sub>l.elims(1) by blast


section \<open>\<Gamma> \<turnstile> stmt is ok\<close>


lemma T_MOVE:
  assumes \<open>\<Gamma> \<turnstile> (Var (name, t)) :: t\<close>
      and \<open>\<Gamma> \<turnstile> e :: t\<close>
    shows \<open>\<Gamma> \<turnstile> Move (name, t) e is ok\<close>
  using assms by auto

lemma T_JMP:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm sz)\<close>
    shows \<open>\<Gamma> \<turnstile> Jmp e is ok\<close>
  using assms by auto

lemma T_CPUEXN:
  assumes \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> CpuExn n is ok\<close>
  using assms by auto

lemma T_SPECIAL:
  assumes \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> Special str is ok\<close>
  using assms by auto

lemma T_WHILE:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm 1)\<close>
      and \<open>\<Gamma> \<turnstile> seq is ok\<close> 
    shows \<open>\<Gamma> \<turnstile> While e seq is ok\<close>
  using assms by auto

lemma T_IF:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm 1)\<close>
      and \<open>\<Gamma> \<turnstile> seq\<^sub>1 is ok\<close>
      and \<open>\<Gamma> \<turnstile> seq\<^sub>2 is ok\<close>
    shows \<open>\<Gamma> \<turnstile> If e seq\<^sub>1 seq\<^sub>2 is ok\<close>
  using assms by auto

lemma T_IFTHEN:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm 1)\<close>
      and \<open>\<Gamma> \<turnstile> seq is ok\<close> 
    shows \<open>\<Gamma> \<turnstile> IfThen e seq is ok\<close>
  using assms by auto

section \<open>\<Gamma> \<turnstile> exp :: type\<close>


lemma T_VAR:
  assumes \<open>(name, t) \<in> set \<Gamma>\<close> and \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (Var (name, t)) :: t\<close>
  using assms by auto

lemma T_INT:
  assumes \<open>sz > 0\<close> and \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> Immediate (num \<Colon> sz) :: (Imm sz)\<close>
  using assms by auto


lemma T_MEM:
  assumes \<open>sz\<^sub>1 > 0\<close> and \<open>sz\<^sub>2 > 0\<close> 
      and \<open>\<Gamma> \<turnstile> v  :: (Mem sz\<^sub>2 sz\<^sub>1)\<close>
      and \<open>\<Gamma> \<turnstile> v' :: (Imm sz\<^sub>1)\<close>
    shows \<open>\<Gamma> \<turnstile> Storage v (num\<^sub>1 \<Colon> sz\<^sub>2) v' sz\<^sub>1 :: (Mem sz\<^sub>2 sz\<^sub>1)\<close> (*TODO*) 
  using assms by auto

lemma T_LOAD:
  assumes \<open>sz' mod sz = 0\<close> and \<open>sz' > 0\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>m\<^sub>e\<^sub>m)\<close>
    shows \<open>\<Gamma> \<turnstile> (Load e\<^sub>1 e\<^sub>2 ed sz') :: (Imm sz')\<close>
  using assms apply auto
  by (meson assms(1))
  
lemma T_STORE:
  assumes \<open>sz' mod sz = 0\<close> and \<open>sz' > 0\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>m\<^sub>e\<^sub>m)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>3 :: (Imm sz')\<close>
    shows \<open>\<Gamma> \<turnstile> (Store e\<^sub>1 e\<^sub>2 ed sz' e\<^sub>3) :: (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)\<close>
  using assms by auto

lemma T_AOP:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz)\<close>
    shows \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) :: (Imm sz)\<close>
  using assms by auto

lemma T_LOP:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz)\<close>
    shows \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) :: (Imm 1)\<close>
  using assms by auto

lemma T_UOP:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm sz)\<close>
    shows \<open>\<Gamma> \<turnstile> (UnOp uop e) :: (Imm sz)\<close>
  using assms by auto

lemma T_CAST_WIDEN:
  assumes \<open>sz > 0\<close> and \<open>sz \<ge> sz'\<close>
      and \<open>\<Gamma> \<turnstile> e :: (Imm sz')\<close>
      and \<open>widen = Signed \<or> widen = Unsigned\<close>
    shows \<open>\<Gamma> \<turnstile> (Cast widen sz e) :: (Imm sz)\<close> (* TODO *)
  using assms by auto

lemma T_CAST_NARROW:
  assumes \<open>sz > 0\<close> and \<open>sz' \<ge> sz\<close>
      and \<open>\<Gamma> \<turnstile> e :: (Imm sz')\<close>
      and \<open>narrow = High \<or> narrow = Low\<close>
    shows \<open>\<Gamma> \<turnstile> (Cast narrow sz e) :: (Imm sz)\<close> (* TODO *)
  using assms by auto

lemma T_LET:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: t\<close>
      and \<open>((name, t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'\<close>
    shows \<open>\<Gamma> \<turnstile> (Let (name, t) e\<^sub>1 e\<^sub>2) :: t'\<close>
  using assms by auto

lemma T_UNKNOWN:
  assumes \<open>t is ok\<close>
      and \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (Unknown str t) :: t\<close>
  using assms by auto

lemma T_ITE:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Imm 1)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: t\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>3 :: t\<close> 
    shows \<open>\<Gamma> \<turnstile> Ite e\<^sub>1 e\<^sub>2 e\<^sub>3 :: t\<close>
  using assms by auto

lemma T_EXTRACT:
  assumes \<open>\<Gamma> \<turnstile> e :: (Imm sz)\<close>
      and \<open>sz\<^sub>1 \<ge> sz\<^sub>2\<close>
    shows \<open>\<Gamma> \<turnstile> Extract sz\<^sub>1 sz\<^sub>2 e :: (Imm (sz\<^sub>1 - sz\<^sub>2 + 1))\<close>
  using assms by auto

lemma T_CONCAT:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: (Imm sz\<^sub>1)\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: (Imm sz\<^sub>2)\<close>
    shows \<open>\<Gamma> \<turnstile> Concat e\<^sub>1 e\<^sub>2 :: (Imm (sz\<^sub>1 + sz\<^sub>2))\<close>
  using assms by auto



section \<open>t is ok\<close>


lemma TWF_IMM:
  assumes \<open>sz > 0\<close>
    shows \<open>(Imm sz) is ok\<close>
  using assms by auto

lemma TWF_MEM:
  assumes \<open>sz\<^sub>1 > 0\<close> and \<open>sz\<^sub>2 > 0\<close>
    shows \<open>(Mem sz\<^sub>1 sz\<^sub>2) is ok\<close> 
  using assms by auto


section \<open>\<Gamma> is ok\<close>


lemma TG_NIL: \<open>([]::TypingContext) is ok\<close>
  by auto

lemma TG_CONS:
  assumes \<open>name \<notin> dom\<^sub>\<Gamma> \<Gamma>\<close>
      and \<open>t is ok\<close>
      and \<open>\<Gamma> is ok\<close>
    shows \<open>((name, t) # \<Gamma>) is ok\<close>
  using assms by auto

text \<open>Check the example from the specification\<close>

lemma
  assumes "bil = Stmt (If foo (Stmt (Move (x, Imm 1) (Val (Immediate (0 \<Colon> 1)))) Empty) (Stmt (Move (x, Imm 32) (Val (Immediate (42 \<Colon> 32)))) Empty)) bar"
    shows "\<not>(\<Gamma> \<turnstile> bil is ok)"
  using assms by (auto simp add: set_not_\<Gamma>_is_ok)

end

