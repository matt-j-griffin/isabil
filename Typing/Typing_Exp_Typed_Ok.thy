theory Typing_Exp_Typed_Ok
  imports Typing_Value_Typed_Ok
          Typing_Var_Typed_Ok
          "../ExpressionSemantics/Expression_Syntax"
begin

no_notation List.append (infixr "@" 65)

class exp_typed_ok = value_typed_ok + var_typed_ok

instantiation exp :: exp_typed_ok 
begin

function
  is_ok_exp :: \<open>exp \<Rightarrow> bool\<close>
where 
  \<open>is_ok_exp (num \<Colon> sz) = ((num \<Colon> sz)::val) is ok\<close> |
  \<open>\<lbrakk>\<forall>num sz. x \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> is_ok_exp x = False\<close>
  subgoal for P x
    apply (rule exp.exhaust[of x], blast)
    by blast+
  by auto 
termination
  apply standard
  by auto

function
  typed_ok_exp :: \<open>TypingContext \<Rightarrow> exp \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  (* Var *)
  \<open>typed_ok_exp \<Gamma> (id' :\<^sub>t t) t = ((id' :\<^sub>t t) \<in> set \<Gamma> \<and> (\<Gamma> is ok) \<and> (t is ok))\<close> |
  \<open>\<lbrakk>t \<noteq> t'\<rbrakk> \<Longrightarrow> typed_ok_exp _ (_ :\<^sub>t t) t' = False\<close> |
  (* Load *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1[e\<^sub>2, ed]:usz) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and>
                                             (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz'\<rbrakk> \<Longrightarrow> typed_ok_exp _ (_[_, _]:usz) imm\<langle>sz'\<rangle> = False\<close> |
  \<open>typed_ok_exp _ (_[_, _]:u_) mem\<langle>_, _\<rangle> = False\<close> |
  (* Store *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 with [e\<^sub>2, ed]:usz \<leftarrow> e\<^sub>3) mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> = (sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and> sz > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>)
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>) 
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>))\<close> |
  \<open>typed_ok_exp _ (_ with [_, _]:u_ \<leftarrow> _) imm\<langle>_\<rangle> = False\<close> |
  (* BinOp *)
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) imm\<langle>sz\<rangle> = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>))\<close> |
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) imm\<langle>1\<rangle> = (\<exists>sz. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>))\<close> | 
  \<open>\<lbrakk>sz \<noteq> 1\<rbrakk> \<Longrightarrow> typed_ok_exp _ (BinOp _ (LOp _) _) imm\<langle>sz\<rangle> = False\<close> | 
  \<open>typed_ok_exp _ (BinOp _ _ _) mem\<langle>_, _\<rangle> = False\<close> |
  (* UnOp *)
  \<open>typed_ok_exp \<Gamma> (UnOp uop e) imm\<langle>sz\<rangle> = (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp _ (UnOp _ _) mem\<langle>_,_\<rangle> = False\<close> |
  (* Cast *)
  \<open>typed_ok_exp \<Gamma> (pad:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (extend:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (high:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (low:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz'\<rbrakk> \<Longrightarrow> typed_ok_exp _ ((_::Cast):sz[_]) imm\<langle>sz'\<rangle> = False\<close> |
  \<open>typed_ok_exp \<Gamma> ((_::Cast):_[_]) mem\<langle>_,_\<rangle> = False\<close> |
  (* Let *)
  \<open>typed_ok_exp \<Gamma> (Let (id' :\<^sub>t t) e\<^sub>1 e\<^sub>2) t' = (id' \<notin> dom\<^sub>\<Gamma> \<Gamma> \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: t) \<and> (((id' :\<^sub>t t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'))\<close> |
  (* Ite *)
  \<open>typed_ok_exp \<Gamma> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) t = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: t) \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: t))\<close> |
  (* extract *)
  \<open>typed_ok_exp \<Gamma> (extract:sz\<^sub>1:sz\<^sub>2[e]) imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> = (sz\<^sub>1 \<ge> sz\<^sub>2 \<and> (\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz\<^sub>1 - sz\<^sub>2 + 1\<rbrakk> \<Longrightarrow> typed_ok_exp _ (extract:sz\<^sub>1:sz\<^sub>2[_]) imm\<langle>sz\<rangle> = False\<close> |
  \<open>typed_ok_exp _ (extract:_:_[_]) mem\<langle>_,_\<rangle> = False\<close> |
  (* concat *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 @ e\<^sub>2) imm\<langle>sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t\<rangle> = (\<exists>sz\<^sub>1 sz\<^sub>2. sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t = sz\<^sub>1 + sz\<^sub>2 \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>))\<close> |
  \<open>typed_ok_exp _ (_ @ _) mem\<langle>_, _\<rangle> = False\<close> |
  (* val *)
  \<open>typed_ok_exp \<Gamma> (Val v) t = (\<Gamma> \<turnstile> v :: t)\<close>
  subgoal for P x
    apply (cases x, simp_all)
    subgoal for \<Gamma> e t
      apply (rule exp_exhaust[of e])
      apply clarify
      apply (metis Val_simp_word)
      apply (metis Val_simp_unknown)
      apply (metis Val_simp_storage)
      apply (metis (full_types))
      subgoal
        apply (cases t)
        by metis+
      subgoal
        apply (cases t)
        by metis+
      subgoal
        apply (cases t)
        by metis+
      subgoal for _ _ bop
        apply (cases t)
        subgoal for sz
          apply (cases bop)
          by metis+
        by metis
      subgoal
        apply (cases t)
        by metis+
      subgoal for cast
        apply (cases t)
        subgoal
          apply (cases cast)
          by metis+
        by metis
      apply (metis var_exhaust)
      apply metis
      by (metis (no_types, opaque_lifting) Type.exhaust)
    .
  by auto

termination 
  apply (standard)
  unfolding append_exp_def
  apply (relation \<open>(\<lambda>p. size (fst (snd p))) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  by (rule mlex_less, simp)+

instance 
  apply standard
  subgoal
    apply (induct rule: typed_ok_exp.induct)
    apply simp_all
    apply blast
    by (simp add: t_is_ok)
  subgoal by simp  
  subgoal
    apply (rule storage_typed_diff)
    unfolding storage_constructor_exp_def by simp
  subgoal unfolding storage_constructor_exp_def by simp  
  subgoal unfolding unknown_constructor_exp_def by simp
  subgoal
    apply (rule unknown_typed_diff)
    by (simp add: unknown_constructor_exp_def)
  subgoal for \<Gamma> num sz
    unfolding word_constructor_exp_def
    using is_ok_exp.simps(1) word_constructor_exp_def by auto
  subgoal for \<Gamma> num sz sz'
    apply (rule word_typed_diff[of \<Gamma> num sz sz'])
    unfolding word_constructor_exp_def by simp
  subgoal unfolding word_constructor_exp_def by simp
  subgoal
    unfolding typed_ok_exp.simps by clarify
  subgoal by simp
  subgoal
    using typed_ok_exp.simps(2) by blast
  .

end


(*


  \<open>typed_ok_exp \<Gamma> (id' :\<^sub>t t) t = ((id' :\<^sub>t t) \<in> set \<Gamma> \<and> (\<Gamma> is ok) \<and> (t is ok))\<close> |
  \<open>\<lbrakk>t \<noteq> t'\<rbrakk> \<Longrightarrow> typed_ok_exp _ (_ :\<^sub>t t) t' = False\<close> |
  (* Load *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1[e\<^sub>2, ed]:usz) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and>
                                             (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz'\<rbrakk> \<Longrightarrow> typed_ok_exp _ (_[_, _]:usz) imm\<langle>sz'\<rangle> = False\<close> |
  \<open>typed_ok_exp _ (_[_, _]:u_) mem\<langle>_, _\<rangle> = False\<close> |
  (* Store *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 with [e\<^sub>2, ed]:usz \<leftarrow> e\<^sub>3) mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> = (sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and> sz > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>)
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>) 
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>))\<close> |
  \<open>typed_ok_exp _ (_ with [_, _]:u_ \<leftarrow> _) imm\<langle>_\<rangle> = False\<close> |
  (* BinOp *)
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) imm\<langle>sz\<rangle> = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>))\<close> |
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) imm\<langle>1\<rangle> = (\<exists>sz. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>))\<close> | 
  \<open>\<lbrakk>sz \<noteq> 1\<rbrakk> \<Longrightarrow> typed_ok_exp _ (BinOp _ (LOp _) _) imm\<langle>sz\<rangle> = False\<close> | 
  \<open>typed_ok_exp _ (BinOp _ _ _) mem\<langle>_, _\<rangle> = False\<close> |
  (* UnOp *)
  \<open>typed_ok_exp \<Gamma> (UnOp uop e) imm\<langle>sz\<rangle> = (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp _ (UnOp _ _) mem\<langle>_,_\<rangle> = False\<close> |
  (* Cast *)
  \<open>typed_ok_exp \<Gamma> (pad:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (extend:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (high:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>typed_ok_exp \<Gamma> (low:sz[e]) imm\<langle>sz\<rangle> = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz'\<rbrakk> \<Longrightarrow> typed_ok_exp _ ((_::Cast):sz[_]) imm\<langle>sz'\<rangle> = False\<close> |
  \<open>typed_ok_exp \<Gamma> ((_::Cast):_[_]) mem\<langle>_,_\<rangle> = False\<close> |
  (* Let *)
  \<open>typed_ok_exp \<Gamma> (Let (id' :\<^sub>t t) e\<^sub>1 e\<^sub>2) t' = (id' \<notin> dom\<^sub>\<Gamma> \<Gamma> \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: t) \<and> (((id' :\<^sub>t t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'))\<close> |
  (* Ite *)
  \<open>typed_ok_exp \<Gamma> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) t = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: t) \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: t))\<close> |
  (* extract *)
  \<open>typed_ok_exp \<Gamma> (extract:sz\<^sub>1:sz\<^sub>2[e]) imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle> = (sz\<^sub>1 \<ge> sz\<^sub>2 \<and> (\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)))\<close> |
  \<open>\<lbrakk>sz \<noteq> sz\<^sub>1 - sz\<^sub>2 + 1\<rbrakk> \<Longrightarrow> typed_ok_exp _ (extract:sz\<^sub>1:sz\<^sub>2[_]) imm\<langle>sz\<rangle> = False\<close> |
  \<open>typed_ok_exp _ (extract:_:_[_]) mem\<langle>_,_\<rangle> = False\<close> |
  (* concat *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 @ e\<^sub>2) imm\<langle>sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t\<rangle> = (\<exists>sz\<^sub>1 sz\<^sub>2. sz\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t = sz\<^sub>1 + sz\<^sub>2 \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>))\<close> |
  \<open>typed_ok_exp _ (_ @ _) mem\<langle>_, _\<rangle> = False\<close> |
  (* val *)
  \<open>typed_ok_exp \<Gamma> (Val v) t = (\<Gamma> \<turnstile> v :: t)\<close>

*)

lemma load_exp_typed_okI:
  assumes \<open>sz dvd sz'\<close> and \<open>sz' > 0\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>nat', sz\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>nat'\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz' :: imm\<langle>sz'\<rangle>\<close>
  using assms by auto

lemma load_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<exists>sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and> sz > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>)\<close>
  using assms by auto

lemma store_exp_typed_okI:
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz'\<close> and \<open>sz' > 0\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz'\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> e\<^sub>1 with [e\<^sub>2, ed]:usz' \<leftarrow> e\<^sub>3 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms by auto

lemma store_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 with [e\<^sub>2, ed]:usz' \<leftarrow> e\<^sub>3 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<exists>sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. sz\<^sub>m\<^sub>e\<^sub>m dvd sz' \<and> sz' > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>)
            \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz'\<rangle>)\<close>
  using assms by auto

lemma aop_exp_typed_okI: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) :: imm\<langle>sz\<rangle>\<close>
  using assms by auto

lemma aop_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) :: imm\<langle>sz\<rangle>\<close>
    shows \<open>(\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>)\<close>
  using assms by auto

lemma lop_exp_typed_okI: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (LOp aop) e\<^sub>2) :: imm\<langle>1\<rangle>\<close>
  using assms unfolding typed_ok_exp.simps by auto

lemma lop_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> (BinOp e\<^sub>1 (LOp aop) e\<^sub>2) :: imm\<langle>1\<rangle>\<close>
    shows \<open>\<exists>sz. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>)\<close>
  using assms unfolding typed_ok_exp.simps by simp

lemma uop_exp_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (UnOp uop e) :: imm\<langle>sz\<rangle>\<close>
  using assms by auto

lemma not_exp_typed_okI:
    fixes e :: exp
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (~ e) :: imm\<langle>sz\<rangle>\<close>
  unfolding BIL_Syntax.not_exp.simps using assms by (rule uop_exp_typed_okI)

lemma uop_exp_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> (UnOp uop e) :: imm\<langle>sz\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>\<close>
  using assms by auto

lemma cast_widen_exp_typed_okI:
  assumes \<open>sz > 0\<close> and \<open>sz \<ge> nat'\<close> and \<open> \<Gamma> \<turnstile> e :: imm\<langle>nat'\<rangle>\<close>
      and \<open>widen = Signed \<or> widen = Unsigned\<close>
    shows \<open>\<Gamma> \<turnstile> widen:sz[e] :: imm\<langle>sz\<rangle>\<close>
  using assms by auto

lemma cast_widen_exp_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> widen:sz[e] :: imm\<langle>sz\<rangle>\<close>
      and \<open>widen = Signed \<or> widen = Unsigned\<close>
    shows \<open>\<exists>sz'. sz > 0 \<and> sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)\<close>
  using assms by auto

lemma cast_narrow_exp_typed_okI:
  assumes \<open>sz > 0\<close> and \<open>nat' \<ge> sz\<close> and \<open>\<Gamma> \<turnstile> e :: imm\<langle>nat'\<rangle>\<close>
      and \<open>narrow = High \<or> narrow = Low\<close>
    shows \<open>\<Gamma> \<turnstile> (narrow:sz[e]) :: imm\<langle>sz\<rangle>\<close>
  using assms by auto

lemma cast_narrow_exp_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> (narrow:sz[e]) :: imm\<langle>sz\<rangle>\<close>
      and \<open>narrow = High \<or> narrow = Low\<close>
    shows \<open>\<exists>sz'. sz > 0 \<and> sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)\<close>
  using assms by auto

(*
lemma T_LET:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: t\<close>
      and \<open>name \<notin> dom\<^sub>\<Gamma> \<Gamma>\<close> (* TODO this is inferred *)
      and \<open>((name, t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'\<close>
    shows \<open>\<Gamma> \<turnstile> (Let (name, t) e\<^sub>1 e\<^sub>2) :: t'\<close>
  using assms by auto
*)

lemma ite_exp_typed_okI:
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: t\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>3 :: t\<close>
    shows \<open>\<Gamma> \<turnstile> ite e\<^sub>1 e\<^sub>2 e\<^sub>3 :: t\<close>
  using assms by auto

lemma ite_exp_typed_okE:
  assumes \<open>\<Gamma> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) :: t\<close>
    shows \<open>(\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: t) \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: t)\<close>
  using assms by auto

lemma extract_exp_typed_okI: 
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>\<close> and \<open>sz\<^sub>1 \<ge> sz\<^sub>2\<close>
    shows \<open>\<Gamma> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e] :: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle>\<close>
  using assms unfolding typed_ok_exp.simps(22) by blast

lemma extract_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e] :: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle>\<close>
    shows \<open>\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>) \<and> sz\<^sub>1 \<ge> sz\<^sub>2\<close>
  using assms unfolding typed_ok_exp.simps(22) by auto
  
lemma concat_exp_typed_okI: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (e\<^sub>1::exp) @ e\<^sub>2 :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms unfolding typed_ok_exp.simps(22) by auto

lemma concat_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> (e\<^sub>1::exp) @ e\<^sub>2 :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
    shows \<open>\<exists>sz\<^sub>1 sz\<^sub>2. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>)\<close>
  using assms unfolding typed_ok_exp.simps(22) by auto
  
lemmas T_LOAD = load_exp_typed_okI
lemmas T_STORE = store_exp_typed_okI
lemmas T_AOP = aop_exp_typed_okI
lemmas T_LOP = lop_exp_typed_okI
lemmas T_UOP = uop_exp_typed_okI
(*lemmas T_NEG = neg_exp_typed_okI*)
lemmas T_NOT = not_exp_typed_okI
lemmas T_CAST_WIDEN = cast_widen_exp_typed_okI
lemmas T_CAST_NARROW = cast_narrow_exp_typed_okI
lemmas T_ITE = ite_exp_typed_okI
lemmas T_EXTRACT = extract_exp_typed_okI
lemmas T_CONCAT = concat_exp_typed_okI


context value_typed_ok
begin


lemma T_MEM_val:
  \<open>\<And>nat sz num\<^sub>1 v v' \<Gamma>. \<lbrakk>(num\<^sub>1 \<Colon> nat) is ok; sz > 0; \<Gamma> \<turnstile> v :: mem\<langle>nat, sz\<rangle>;
                          \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>\<rbrakk>
                     \<Longrightarrow> \<Gamma> \<turnstile> (v[(num\<^sub>1 \<Colon> nat) \<leftarrow> v', sz])::val :: mem\<langle>nat, sz\<rangle>\<close>
  apply simp
  apply (rule word_is_okE)
   by auto


lemma T_MEM_exp:
  \<open>\<And>nat sz num\<^sub>1 v v' \<Gamma>. \<lbrakk>(num\<^sub>1 \<Colon> nat) is ok; sz > 0; \<Gamma> \<turnstile> v :: mem\<langle>nat, sz\<rangle>;
                          \<Gamma> \<turnstile> v' :: imm\<langle>sz\<rangle>\<rbrakk>
                     \<Longrightarrow> \<Gamma> \<turnstile> (v[(num\<^sub>1 \<Colon> nat) \<leftarrow> v', sz])::exp :: mem\<langle>nat, sz\<rangle>\<close>
  unfolding storage_constructor_exp_def typed_ok_exp.simps
  by (rule T_MEM_val, blast+)



lemma storage_add_is_ok:
  assumes \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) is ok\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (mem[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])::val :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  apply (rule T_MEM_val)
  apply (rule assms(2))
  using assms typed_ok_val.elims(2) apply fastforce
  using assms(1, 3) by blast+
(*
lemma storage_add_is_ok':
  assumes \<open>\<Gamma> \<turnstile> mem :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])::val :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  using assms apply (rule_tac word_exhaust[of w\<^sub>a\<^sub>d\<^sub>d\<^sub>r], auto)
  apply (drule storage_add_is_ok)
  sledgehammer
  apply (rule storage_add_is_ok)
  
  using T_MEM_val
  using T_MEM_val
  using assms
  
  apply (rule_tac is_ok_judgement_type_val_class.T_MEM_Word_cons)
  using typing_val_immediate typing_val_mem by blast+
*)
end
(*
method solve_T_EXP = (
  match conclusion in
    \<open>_ \<turnstile> _[_, _]:u_ :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_LOAD, linarith, linarith, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> _ with [_, _]:u_ \<leftarrow> _ :: mem\<langle>_, _\<rangle>\<close> \<Rightarrow> \<open>rule T_STORE, linarith, linarith, solve_T_EXP, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> ite _ _ _ :: _\<close> \<Rightarrow> \<open>rule T_ITE, solve_T_EXP, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> extract:_:_[_] :: imm\<langle>_ - _ + _\<rangle>\<close> \<Rightarrow> \<open>rule T_EXTRACT, solve_T_EXP, linarith\<close>
  \<bar> \<open>_ \<turnstile> (_::exp) @ _ :: imm\<langle>_ + _\<rangle>\<close> \<Rightarrow> \<open>rule T_CONCAT, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> pad:_[_] :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_CAST_WIDEN, linarith, linarith, solve_T_EXP, blast\<close>
  \<bar> \<open>_ \<turnstile> extend:_[_] :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_CAST_WIDEN, linarith, linarith, solve_T_EXP, blast\<close>
  \<bar> \<open>_ \<turnstile> high:_[_] :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_CAST_NARROW, linarith, linarith, solve_T_EXP, blast\<close>
  \<bar> \<open>_ \<turnstile> low:_[_] :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_CAST_NARROW, linarith, linarith, solve_T_EXP, blast\<close>
  \<bar> \<open>_ \<turnstile> (UnOp _ _) :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_UOP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> (BinOp _ (AOp _) _) :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_AOP, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> (BinOp _ (LOp _) _) :: imm\<langle>1\<rangle>\<close> \<Rightarrow> \<open>rule T_LOP, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> (_ :\<^sub>t _) :: _\<close> \<Rightarrow> \<open>rule T_VAR, linarith, solve_TG, solve_TWF\<close>
)
*)

lemma T_WIDE_LOAD: 
  assumes \<open>0 < sz'\<close> and \<open>sz' \<le> sz\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz'\<close>
      and \<open>\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>\<close>
      and \<open>cast = extend \<or> cast = pad\<close>
    shows \<open>\<Gamma> \<turnstile> cast:sz[e\<^sub>1[e\<^sub>2, el]:usz'] :: imm\<langle>sz\<rangle>\<close>
  apply (rule T_CAST_WIDEN[of _ sz'])
  using assms(1,2) apply linarith+
  subgoal
    apply (rule T_LOAD[of sz\<^sub>m\<^sub>e\<^sub>m _ _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r])
    using assms(1,3-) by blast+
  using assms(6) by assumption

method solve_T_EXP = (
  match conclusion in
  \<comment> \<open>solve_T_EXP cannot prove expressions requiring a fixed variable not in the conclusion to 
      be specified. However, we can identify the value of the fixed variables in certain static 
      expression patterns\<close>
  
  \<comment> \<open>Cast-Load - we know the non-conclusive cast variable must be equal to the output of the load\<close>
    \<open>_ \<turnstile> extend:_[_[_, el]:usz] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_WIDE_LOAD[of _ _ 8 _ _ 64], linarith, linarith, fastforce, solve_T_EXP, solve_T_EXP, blast\<close>
  \<bar> \<open>_ \<turnstile> pad:_[_[_, el]:usz] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_WIDE_LOAD[of _ _ 8 _ _ 64], linarith, linarith, fastforce, solve_T_EXP, solve_T_EXP, blast\<close>

  \<comment> \<open>Cast-Cast - we know the non-conclusive cast variable must be equal to the output of the nested 
      cast\<close>
  \<bar>  \<open>_ \<turnstile> pad:_[_:sz[_]] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_WIDEN[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> extend:_[_:sz[_]] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_WIDEN[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> pad:_[_:sz[_]] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_NARROW[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> extend:_[_:sz[_]] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_NARROW[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>

  \<comment> \<open>Cast-Var - we know the non-conclusive cast variable must be equal to an immediate variables 
      size\<close>
  \<bar>  \<open>_ \<turnstile> extend:_[(_ :\<^sub>t imm\<langle>sz\<rangle>)] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_WIDEN[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> pad:_[(_ :\<^sub>t imm\<langle>sz\<rangle>)] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_WIDEN[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> low:_[(_ :\<^sub>t imm\<langle>sz\<rangle>)] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_NARROW[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>
  \<bar>  \<open>_ \<turnstile> high:_[(_ :\<^sub>t imm\<langle>sz\<rangle>)] :: imm\<langle>_\<rangle>\<close> for sz \<Rightarrow> \<open>rule T_CAST_NARROW[of _ sz], linarith, linarith, solve_T_EXP, blast\<close>

  \<comment> \<open>Ignore unprovable cases\<close>
  \<bar> \<open>_ \<turnstile> _:_[_] :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>succeed\<close>

  \<comment> \<open>Provable cases\<close>
  \<bar> \<open>_ \<turnstile> (_ :\<^sub>t _) :: _\<close> \<Rightarrow> \<open>solve_T_VAR\<close>
  \<bar> \<open>_ \<turnstile> UnOp _ _ :: _\<close> \<Rightarrow> \<open>rule T_UOP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> BinOp _ (AOp _) _ :: _\<close> \<Rightarrow> \<open>rule T_AOP; solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> BinOp _ (LOp _) _ :: _\<close> \<Rightarrow> \<open>rule T_LOP; solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> _[_, _]:u_ :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>rule T_LOAD[of 8 _ _ _ 64], presburger, linarith, solve_T_EXP, solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> _ with [_, el]:u_ \<leftarrow> _ :: mem\<langle>_, _\<rangle>\<close> \<Rightarrow> \<open>rule T_STORE, fastforce, linarith; solve_T_EXP\<close>
  \<bar> \<open>_ \<turnstile> _ \<Colon> _ :: imm\<langle>_\<rangle>\<close> \<Rightarrow> \<open>solve_T_WORD\<close>
  \<bar> _ \<Rightarrow> \<open>succeed\<close>
)

end
