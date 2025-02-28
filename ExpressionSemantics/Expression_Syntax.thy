
section \<open>Syntax\<close>

theory Expression_Syntax
  imports "../Val_Instance" (*TODO*)
          "../Formula_Syntax"
begin

text \<open>Some evaluation rules depend on the type of a value. Since there are two canonical forms for
each type, we avoid duplicating each rule by defining the following metafunction:\<close>

method solve_typeI_scaffold methods recurs = (
  rule type_wordI type_storageI type_unknownI type_plusI |
  (rule type_succ_recI, recurs) | \<comment> \<open>TODO non-recursive\<close>
  (rule type_storage_addrI, recurs) 
) 

method solve_typeI uses add = (
  (solves \<open>rule add\<close>) | 
  solve_typeI_scaffold \<open>solve_typeI add: add\<close>
) 

instantiation exp :: exp
begin

definition 
  var_constructor_exp :: \<open>string \<Rightarrow> Type \<Rightarrow> exp\<close>
where
  \<open>(a :\<^sub>t b) \<equiv> EVar (a :\<^sub>t b)\<close>

definition
  word_constructor_exp :: \<open>nat \<Rightarrow> nat \<Rightarrow> exp\<close>
where
  \<open>(num \<Colon> sz) = Val (num \<Colon> sz)\<close>

definition
  unknown_constructor_exp :: \<open>string \<Rightarrow> Type \<Rightarrow> exp\<close>
where
  \<open>(unknown[str]: sz) = Val (unknown[str]: sz)\<close>

definition
  storage_constructor_exp :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> exp\<close>
where
  \<open>(v[a \<leftarrow> v', sz]) = Val (v[a \<leftarrow> v', sz])\<close>

definition 
  lsr_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 >> e2 = (BinOp e1 (AOp RShift) e2)\<close>

definition 
  lsl_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 << e2 = (BinOp e1 (AOp LShift) e2)\<close>

definition 
  asr_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 >>> e2 = (BinOp e1 (AOp ARShift) e2)\<close>

definition 
  land_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 && e2 = (BinOp e1 (AOp And) e2)\<close>

definition 
  lor_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 || e2 = (BinOp e1 (AOp Or) e2)\<close>

definition 
  xor_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 xor e2 = (BinOp e1 (AOp Xor) e2)\<close>

definition 
  sdivide_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 sdiv e2 = (BinOp e1 (AOp SDivide) e2)\<close>

definition 
  smod_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 smod e2 = (BinOp e1 (AOp SMod) e2)\<close>

definition
  not_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>not_exp exp = (UnOp Not exp)\<close>

definition 
  lt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 lt e2 = (BinOp e1 (LOp Lt) e2)\<close>

definition 
  le_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 le e2 = (BinOp e1 (LOp Le) e2)\<close>

definition 
  slt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 slt e2 = (BinOp e1 (LOp Slt) e2)\<close>

definition 
  sle_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 sle e2 = (BinOp e1 (LOp Sle) e2)\<close>

definition 
  uminus_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>uminus_exp e1 = (UnOp Neg e1)\<close>

definition 
  minus_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>minus_exp e1 e2 = (BinOp e1 (AOp Minus) e2)\<close>

definition 
  plus_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>plus_exp e1 e2 = (BinOp e1 (AOp Plus) e2)\<close>

definition 
  times_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>times_exp e1 e2 = (BinOp e1 (AOp Times) e2)\<close>

definition 
  modulo_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>modulo_exp e1 e2 = (BinOp e1 (AOp Mod) e2)\<close>

definition 
  divide_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>divide_exp e1 e2 = (BinOp e1 (AOp Divide) e2)\<close>

lemmas bop_syntax = modulo_exp_def divide_exp_def times_exp_def plus_exp_def minus_exp_def
                    sle_exp_def slt_exp_def lsr_exp_def lsl_exp_def asr_exp_def land_exp_def 
                    lor_exp_def xor_exp_def sdivide_exp_def smod_exp_def lt_exp_def le_exp_def

function
  type_exp :: \<open>exp \<Rightarrow> Type\<close>
where
  \<open>type_exp (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close> |
  \<open>type_exp (unknown[str]: t) = t\<close> |
  \<open>type_exp (mem[(num \<Colon> sz\<^sub>1) \<leftarrow> v, sz\<^sub>2]) = mem\<langle>sz\<^sub>1, sz\<^sub>2\<rangle>\<close> |
  \<open>\<lbrakk>\<forall>num sz. v \<noteq> num \<Colon> sz; \<forall>str t. v \<noteq> unknown[str]: t; \<forall>mem w v' sz. v \<noteq> (mem[w \<leftarrow> v', sz])\<rbrakk> 
      \<Longrightarrow> type_exp v = undefined\<close>
  subgoal for P x 
    by (metis type_word.cases)
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def
  by auto
termination by lexicographic_order

function
  is_ok_exp :: \<open>exp \<Rightarrow> bool\<close>
where 
  \<open>is_ok_exp (num \<Colon> sz) = ((num \<Colon> sz)::val) is ok\<close> |
  \<open>\<lbrakk>\<forall>num sz. x \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> is_ok_exp x = False\<close>
proof -
  fix P :: bool
    and x :: exp
  assume word: "\<And>num sz. x = num \<Colon> sz \<Longrightarrow> P"
    and not_word: "\<And>xa. \<lbrakk>\<forall>num sz. xa \<noteq> num \<Colon> sz; x = xa\<rbrakk> \<Longrightarrow> P"
  thus P
  unfolding word_constructor_exp_def proof (cases x)
    case (Val v)
    thus ?thesis 
    proof (cases v rule: val_exhaust)
      case (Word num sz)
      show ?thesis 
        apply (rule word)
        unfolding Word Val word_constructor_exp_def by auto
    next
      case (Unknown str t)
      show ?thesis 
        apply (rule not_word[OF _ refl])
        unfolding Unknown Val word_constructor_exp_def by auto
    next
      case (Storage mem w v' sz)
      show ?thesis 
        apply (rule not_word[OF _ refl])
        unfolding Storage Val word_constructor_exp_def by auto
    qed
  qed auto
qed (unfold word_constructor_exp_def, auto)
termination by lexicographic_order

function (* TODO this should be an inductive predicate with a deterministic proof *)
  typed_ok_exp :: \<open>TypingContext \<Rightarrow> exp \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  (* Var *)
  \<open>typed_ok_exp \<Gamma> (id' :\<^sub>t t) t' = ((id' :\<^sub>t t) \<in> set \<Gamma> \<and> (\<Gamma> is ok) \<and> (t is ok) \<and> t = t')\<close> |
  (* Load *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1[e\<^sub>2, ed]:usz) t = (sz > 0 \<and> (\<exists>sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and>
                                             (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>)) \<and> t = imm\<langle>sz\<rangle>)\<close> |
  (* Store *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 with [e\<^sub>2, ed]:usz \<leftarrow> e\<^sub>3) mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> = (sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<and> sz > 0 \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: imm\<langle>sz\<rangle>)
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>) 
                                                    \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>))\<close> |
  \<open>typed_ok_exp _ (_ with [_, _]:u_ \<leftarrow> _) imm\<langle>_\<rangle> = False\<close> |
  (* BinOp *)
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) imm\<langle>sz\<rangle> = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>))\<close> |
  \<open>typed_ok_exp \<Gamma> (BinOp e\<^sub>1 (LOp lop) e\<^sub>2) t = ((\<exists>sz. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<rangle>)) \<and> t = imm\<langle>1\<rangle>)\<close> | 
  \<open>typed_ok_exp _ (BinOp _ _ _) mem\<langle>_, _\<rangle> = False\<close> |
  (* UnOp *)
  \<open>typed_ok_exp \<Gamma> (UnOp uop e) imm\<langle>sz\<rangle> = (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp _ (UnOp _ _) mem\<langle>_,_\<rangle> = False\<close> |
  (* Cast *)
  \<open>typed_ok_exp \<Gamma> (pad:sz[e]) t = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)) \<and> t = imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp \<Gamma> (extend:sz[e]) t = (sz > 0 \<and> (\<exists>sz'. sz \<ge> sz' \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)) \<and> t = imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp \<Gamma> (high:sz[e]) t = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)) \<and> t = imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_exp \<Gamma> (low:sz[e]) t = (sz > 0 \<and> (\<exists>sz'. sz' \<ge> sz \<and> (\<Gamma> \<turnstile> e :: imm\<langle>sz'\<rangle>)) \<and> t = imm\<langle>sz\<rangle>)\<close> |
  (* Let *)
  \<open>typed_ok_exp \<Gamma> (Let (id' :\<^sub>t t) e\<^sub>1 e\<^sub>2) t' = (id' \<notin> dom\<^sub>\<Gamma> \<Gamma> \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: t) \<and> (((id' :\<^sub>t t) # \<Gamma>) \<turnstile> e\<^sub>2 :: t'))\<close> |
  (* Ite *)
  \<open>typed_ok_exp \<Gamma> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) t = ((\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: t) \<and> (\<Gamma> \<turnstile> e\<^sub>3 :: t))\<close> |
  (* extract *)
  \<open>typed_ok_exp \<Gamma> (extract:sz\<^sub>1:sz\<^sub>2[e]) t = (sz\<^sub>1 \<ge> sz\<^sub>2 \<and> (\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>)) \<and> t = imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>)\<close> |
  (* concat *)
  \<open>typed_ok_exp \<Gamma> (e\<^sub>1 \<copyright> e\<^sub>2) t = (\<exists>sz\<^sub>1 sz\<^sub>2. t = imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle> \<and> (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>))\<close> |
  (* val *)
  \<open>typed_ok_exp \<Gamma> (Val v) t = (\<Gamma> \<turnstile> v :: t)\<close>
  unfolding var_constructor_exp_def 
proof -
  fix P :: bool
    and x :: "Var.var list \<times> exp \<times> Type"
  assume EVarE: "\<And>\<Gamma> id' t t'. x = (\<Gamma>, EVar (id' :\<^sub>t t), t') \<Longrightarrow> P"
    and LoadE: "\<And>\<Gamma> e\<^sub>1 e\<^sub>2 ed sz t. x = (\<Gamma>, e\<^sub>1[e\<^sub>2, ed]:usz, t) \<Longrightarrow> P"
    and StoreE:"\<And>\<Gamma> e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. x = (\<Gamma>, e\<^sub>1 with [e\<^sub>2, ed]:usz \<leftarrow> e\<^sub>3, mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) \<Longrightarrow> P"
    and StoreImmE:"\<And>uu uv uw ux uy uz va. x = (uu, uv with [uw, ux]:uuy \<leftarrow> uz, imm\<langle>va\<rangle>) \<Longrightarrow> P"
    and AopE:"\<And>\<Gamma> e\<^sub>1 aop e\<^sub>2 sz. x = (\<Gamma>, BinOp e\<^sub>1 (AOp aop) e\<^sub>2, imm\<langle>sz\<rangle>) \<Longrightarrow> P"
    and LopE:"\<And>\<Gamma> e\<^sub>1 lop e\<^sub>2 t. x = (\<Gamma>, BinOp e\<^sub>1 (LOp lop) e\<^sub>2, t) \<Longrightarrow> P"
    and BopMemE:"\<And>vb vc vd ve vf vg. x = (vb, BinOp vc vd ve, mem\<langle>vf, vg\<rangle>) \<Longrightarrow> P"
    and UnOpE:"\<And>\<Gamma> uop e sz. x = (\<Gamma>, UnOp uop e, imm\<langle>sz\<rangle>) \<Longrightarrow> P"
    and UnOpMemE:"\<And>vh vi vj vk vl. x = (vh, UnOp vi vj, mem\<langle>vk, vl\<rangle>) \<Longrightarrow> P"
    and PadE:"\<And>\<Gamma> sz e t. x = (\<Gamma>, pad:sz[e], t) \<Longrightarrow> P"
    and ExtendE:"\<And>\<Gamma> sz e t. x = (\<Gamma>, extend:sz[e], t) \<Longrightarrow> P"
    and HighE:"\<And>\<Gamma> sz e t. x = (\<Gamma>, high:sz[e], t) \<Longrightarrow> P"
    and LowE:"\<And>\<Gamma> sz e t. x = (\<Gamma>, low:sz[e], t) \<Longrightarrow> P"
    and LetE:"\<And>\<Gamma> id' t e\<^sub>1 e\<^sub>2 t'. x = (\<Gamma>, exp.Let (id' :\<^sub>t t) e\<^sub>1 e\<^sub>2, t') \<Longrightarrow> P"
    and IteE:"\<And>\<Gamma> e\<^sub>1 e\<^sub>2 e\<^sub>3 t. x = (\<Gamma>, ite e\<^sub>1 e\<^sub>2 e\<^sub>3, t) \<Longrightarrow> P"
    and ExtractE:"\<And>\<Gamma> sz\<^sub>1 sz\<^sub>2 e t. x = (\<Gamma>, extract:sz\<^sub>1:sz\<^sub>2[e], t) \<Longrightarrow> P"
    and ConcatE:"\<And>\<Gamma> e\<^sub>1 e\<^sub>2 t. x = (\<Gamma>, e\<^sub>1 \<copyright> e\<^sub>2, t) \<Longrightarrow> P"
    and ValE: "\<And>\<Gamma> v t. x = (\<Gamma>, Val v, t) \<Longrightarrow> P"
  show P
  proof (cases x)
    case (fields \<Gamma> e t)
    show ?thesis 
    proof (cases e)
      case (Val v)
      show ?thesis
        apply (rule ValE)
        unfolding Val fields by auto
    next
      case (EVar var)
      show ?thesis
      proof (cases var rule: var_exhaust)
        case (Var id t)
        show ?thesis 
          apply (rule EVarE)
          unfolding fields EVar Var by auto 
      qed
    next
      case (Load x31 x32 x33 x34)
      show ?thesis 
        apply (rule LoadE)
        unfolding Load fields by auto
    next
      case (Store x41 x42 x43 x44 x45)
      show ?thesis 
      proof (cases t)
        case (Imm x1)
        show ?thesis 
          apply (rule StoreImmE)
          unfolding Store Imm fields by auto
      next
        case (Mem x21 x22)
        show ?thesis 
          apply (rule StoreE)
          unfolding Store Mem fields by auto
      qed
    next
      case (BinOp x51 bop x53)
      show ?thesis 
      proof (cases t)
        case (Imm x1)
        show ?thesis 
        proof (cases bop)
          case (AOp x1)
          show ?thesis
          apply (rule AopE)
          unfolding AOp Imm BinOp fields by auto
        next
          case (LOp x2)
          show ?thesis
            apply (rule LopE)
            unfolding LOp Imm BinOp fields by auto
        qed
      next
        case (Mem x21 x22)
        show ?thesis
          apply (rule BopMemE)
          unfolding Mem BinOp fields by auto
      qed
    next
      case (UnOp x61 x62)
      show ?thesis 
      proof (cases t)
        case (Imm x1)
        show ?thesis 
          apply (rule UnOpE)
          unfolding Imm UnOp fields by auto
      next
        case (Mem x21 x22)
        show ?thesis 
          apply (rule UnOpMemE)
          unfolding Mem UnOp fields by auto
      qed
    next
      case (Cast cast x72 x73)
      show ?thesis 
      proof (cases cast)
        case Unsigned
        show ?thesis 
          apply (rule PadE)
          unfolding Unsigned Cast fields by auto
      next
        case Signed
        show ?thesis 
          apply (rule ExtendE)
          unfolding Signed Cast fields by auto
      next
        case High
        show ?thesis 
          apply (rule HighE)
          unfolding High Cast fields by auto          
      next
        case Low
        show ?thesis 
          apply (rule LowE)
          unfolding Low Cast fields by auto          
      qed
    next
      case (Let var x82 x83)
      show ?thesis 
      proof (cases var rule: var_exhaust)
        case (Var id t)
        show ?thesis 
          apply (rule LetE)
          unfolding Let Var fields by auto
      qed
    next
      case (Ite x91 x92 x93)
      show ?thesis 
        apply (rule IteE)
        unfolding Ite fields by auto
    next
      case (Extract x101 x102 x103)
      show ?thesis 
        apply (rule ExtractE)
        unfolding Extract fields by auto
    next
      case (Concat x111 x112)
      show ?thesis 
        apply (rule ConcatE)
        unfolding Concat fields by auto
    qed
  qed
qed auto
termination by lexicographic_order

instance
  apply standard 
  apply auto
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def 
            var_constructor_exp_def bop_syntax 
  apply auto
proof -
  fix \<Gamma> :: "Var.var list"
    and a :: exp
    and t :: Type
  assume typed_ok: "\<Gamma> \<turnstile> a :: t"
  thus "t is ok"
  proof (induct rule: typed_ok_exp.induct)
    case (18 \<Gamma> v t)
    thus ?case 
      unfolding typed_ok_exp.simps
      by (rule t_is_ok)
  qed auto
qed
    
end

subsubsection \<open>Syntax for UOPs\<close>

locale uop_lemmas =
    fixes uop_fun :: \<open>exp \<Rightarrow> exp\<close> and uop :: UnOp
  assumes uop_simps: \<open>\<And>e. uop_fun e = UnOp uop e\<close>
begin

lemma simps[simp]:
  \<open>uop_fun w \<noteq> Val v\<close> \<open>Val v \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> e\<^sub>1 \<copyright> e\<^sub>2\<close> \<open>(e\<^sub>1 \<copyright> e\<^sub>2) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close> \<open>(e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close> \<open>(e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (Cast cast sz e)\<close> \<open>(Cast cast sz e) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close> \<open>(Let var e\<^sub>1 e\<^sub>2) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close> \<open>(ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e])\<close> \<open>(extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e]) \<noteq> uop_fun w\<close>
  \<open>uop_fun w \<noteq> BinOp e\<^sub>1 bop e\<^sub>2\<close> \<open>BinOp e\<^sub>1 bop e\<^sub>2  \<noteq> uop_fun w\<close>
  unfolding uop_simps by simp_all

lemma unop_inject[simp]: 
    \<open>(uop_fun e = UnOp uop' e') \<longleftrightarrow> (uop = uop' \<and> e = e')\<close>
    \<open>(UnOp uop' e' = uop_fun e) \<longleftrightarrow> (uop' = uop \<and> e' = e)\<close>
  by (auto simp add: uop_simps)

lemma inject[simp]: \<open>(uop_fun e = uop_fun e') \<longleftrightarrow> (e = e')\<close>
  by (simp add: uop_simps)

lemma capture_avoiding_sub[simp]:
  \<open>[v\<sslash>var](uop_fun e) = uop_fun ([v\<sslash>var]e)\<close>
  unfolding uop_simps by auto
end

interpretation not: uop_lemmas not Not by (standard, unfold not_exp_def,  rule refl)
interpretation neg: uop_lemmas uminus Neg by (standard, unfold uminus_exp_def,  rule refl)

lemma uop_simps[simp]:
  fixes w :: exp shows \<open>\<sim> w \<noteq> - w'\<close> \<open>- w' \<noteq> \<sim> w\<close>
  unfolding uminus_exp_def not_exp_def by simp_all

subsubsection \<open>Syntax for BOPs\<close>

text \<open>Lemmas that target all BOPs\<close>

locale bop_lemmas =
    fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and bop :: BinOp
  assumes bop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 bop e\<^sub>2\<close>
begin

lemma simps[simp]:
  \<open>\<And>v e\<^sub>3 e\<^sub>4. bop_fun e\<^sub>3 e\<^sub>4 \<noteq> Val v\<close>
  \<open>\<And>v e\<^sub>3 e\<^sub>4. Val v \<noteq> bop_fun e\<^sub>3 e\<^sub>4\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4. bop_fun e\<^sub>3 e\<^sub>4 \<noteq> e\<^sub>1 \<copyright> e\<^sub>2\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4. (e\<^sub>1 \<copyright> e\<^sub>2) \<noteq> bop_fun e\<^sub>3 e\<^sub>4\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 en sz e\<^sub>3 e\<^sub>4. bop_fun e\<^sub>3 e\<^sub>4 \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 en sz e\<^sub>3 e\<^sub>4. (e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> bop_fun e\<^sub>3 e\<^sub>4\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4 e\<^sub>5 en sz. bop_fun e\<^sub>4 e\<^sub>5 \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4 e\<^sub>5 en sz. (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> bop_fun e\<^sub>4 e\<^sub>5\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e cast sz. bop_fun e\<^sub>1 e\<^sub>2 \<noteq> (Cast cast sz e)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e cast sz. (Cast cast sz e) \<noteq> bop_fun e\<^sub>1 e\<^sub>2\<close>
  \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2 var. bop_fun e\<^sub>3 e\<^sub>4 \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close>
  \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2 var. (Let var e\<^sub>1 e\<^sub>2) \<noteq> bop_fun e\<^sub>3 e\<^sub>4\<close>
  \<open>\<And>e\<^sub>4 e\<^sub>5 e\<^sub>1 e\<^sub>2 e\<^sub>3. bop_fun e\<^sub>4 e\<^sub>5 \<noteq> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close>
  \<open>\<And>e\<^sub>4 e\<^sub>5 e\<^sub>1 e\<^sub>2 e\<^sub>3. (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> bop_fun e\<^sub>4 e\<^sub>5\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e sz\<^sub>l\<^sub>o\<^sub>w sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h. bop_fun e\<^sub>1 e\<^sub>2 \<noteq> (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e])\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e sz\<^sub>l\<^sub>o\<^sub>w sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h. (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e]) \<noteq> bop_fun e\<^sub>1 e\<^sub>2\<close>
  \<open>\<And>uop e\<^sub>1 e\<^sub>2 e\<^sub>3. UnOp uop e\<^sub>1 \<noteq> bop_fun e\<^sub>2 e\<^sub>3\<close>
  \<open>\<And>uop e\<^sub>1 e\<^sub>2 e\<^sub>3. bop_fun e\<^sub>2 e\<^sub>3 \<noteq> UnOp uop e\<^sub>1\<close>
  \<open>-e \<noteq> bop_fun e\<^sub>1 e\<^sub>2\<close> \<open>bop_fun e\<^sub>1 e\<^sub>2 \<noteq> -e\<close>
  \<open>\<sim>e \<noteq> bop_fun e\<^sub>1 e\<^sub>2\<close> \<open>bop_fun e\<^sub>1 e\<^sub>2 \<noteq> \<sim>e\<close>
  unfolding bop_simps by simp_all

lemma binop_inject[simp]: 
    \<open>(bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1' bop' e\<^sub>2') \<longleftrightarrow> (e\<^sub>1 = e\<^sub>1' \<and> bop = bop' \<and> e\<^sub>2 = e\<^sub>2')\<close>
    \<open>(BinOp e\<^sub>1' bop' e\<^sub>2' = bop_fun e\<^sub>1 e\<^sub>2) \<longleftrightarrow> (e\<^sub>1' = e\<^sub>1 \<and> bop' = bop \<and> e\<^sub>2' = e\<^sub>2)\<close>
  by (auto simp add: bop_simps)

lemma inject[simp]: \<open>(bop_fun e\<^sub>1 e\<^sub>2 = bop_fun e\<^sub>1' e\<^sub>2') \<longleftrightarrow> (e\<^sub>1 = e\<^sub>1' \<and> e\<^sub>2 = e\<^sub>2')\<close>
  by (simp add: bop_simps)

lemma capture_avoiding_sub[simp]:
  \<open>[v\<sslash>var](bop_fun e\<^sub>1 e\<^sub>2) = bop_fun ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2)\<close>
  unfolding bop_simps by auto

end

text \<open>Lemmas that target arithmetic BOPs\<close>

locale aop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and aop :: AOp
  assumes aop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (AOp aop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>AOp aop\<close>
  by (standard, rule aop_simps)

end

interpretation plus: aop_lemmas \<open>(+)\<close> \<open>Plus\<close> by (standard, unfold plus_exp_def, rule refl)
interpretation minus: aop_lemmas \<open>(-)\<close> \<open>Minus\<close> by (standard, unfold minus_exp_def, rule refl)
interpretation times: aop_lemmas \<open>(*)\<close> \<open>Times\<close> by (standard, unfold times_exp_def, rule refl)
interpretation divide: aop_lemmas \<open>(div)\<close> \<open>Divide\<close> by (standard, unfold divide_exp_def, rule refl)
interpretation mod: aop_lemmas \<open>(mod)\<close> \<open>Mod\<close> by (standard, unfold modulo_exp_def, rule refl)
interpretation sdivide: aop_lemmas \<open>(sdiv)\<close> \<open>SDivide\<close> by (standard, unfold sdivide_exp_def, rule refl)
interpretation smod: aop_lemmas \<open>(smod)\<close> \<open>SMod\<close> by (standard, unfold smod_exp_def, rule refl)
interpretation land: aop_lemmas \<open>(&&)\<close> \<open>And\<close> by (standard, unfold land_exp_def, rule refl)
interpretation lor: aop_lemmas \<open>(||)\<close> \<open>Or\<close> by (standard, unfold lor_exp_def, rule refl)
interpretation xor: aop_lemmas \<open>(xor)\<close> \<open>Xor\<close> by (standard, unfold xor_exp_def, rule refl)
interpretation lsl: aop_lemmas \<open>(<<)\<close> \<open>LShift\<close> by (standard, unfold lsl_exp_def, rule refl)
interpretation lsr: aop_lemmas \<open>(>>)\<close> \<open>RShift\<close> by (standard, unfold lsr_exp_def, rule refl)
interpretation asr: aop_lemmas \<open>(>>>)\<close> \<open>ARShift\<close> by (standard, unfold asr_exp_def, rule refl)

text \<open>Lemmas that target logical BOPs\<close>

locale lop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and lop :: LOp
  assumes lop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (LOp lop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>LOp lop\<close>
  by (standard, rule lop_simps)

end

interpretation lt:  lop_lemmas \<open>(le)\<close>  Le  by (standard, unfold le_exp_def,  rule refl)
interpretation le:  lop_lemmas \<open>(lt)\<close>  Lt  by (standard, unfold lt_exp_def,  rule refl)
interpretation sle: lop_lemmas \<open>(sle)\<close> Sle by (standard, unfold sle_exp_def, rule refl)
interpretation slt: lop_lemmas \<open>(slt)\<close> Slt by (standard, unfold slt_exp_def, rule refl)


subsubsection \<open>Syntax for values\<close>
(* TODO im sure this could be improved *)


lemma storage_not_nested_exp[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz] \<noteq> Val v\<close>
  unfolding storage_constructor_exp_def by simp

(* TODO add to simpset *)
lemmas Val_simp_word = word_constructor_exp_def[symmetric]
lemmas Val_simp_storage = storage_constructor_exp_def[symmetric]
lemmas Val_simp_unknown = unknown_constructor_exp_def[symmetric]

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)

lemma exp_exhaust:
  obtains 
    (Word) num sz where \<open>e = (num \<Colon> sz)\<close>
  | (Unknown) str t where \<open>e = (unknown[str]: t)\<close>
  | (Storage) mem w v' sz where \<open>e = (mem[w \<leftarrow> v', sz])\<close>
  | (Var) id t where \<open>e = (id :\<^sub>t t)\<close>
  | (Concat) e\<^sub>1 e\<^sub>2 where \<open>e = e\<^sub>1 \<copyright> e\<^sub>2\<close>
  | (Load) e\<^sub>1 e\<^sub>2 en sz where \<open>e = (e\<^sub>1[e\<^sub>2, en]:usz)\<close>
  | (Store) e\<^sub>1 e\<^sub>2 en sz e\<^sub>3 where \<open>e = (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close>
  | (BinOp) e\<^sub>1 e\<^sub>2 bop where \<open>e = BinOp e\<^sub>1 bop e\<^sub>2\<close>
  | (UnOp) e\<^sub>1 uop where \<open>e = UnOp e\<^sub>1 uop\<close>
  | (Cast) cast sz e\<^sub>1 where \<open>e = (cast:sz[e\<^sub>1])\<close>
  | (Let) var e\<^sub>1 e\<^sub>2 where \<open>e = (Let var e\<^sub>1 e\<^sub>2)\<close>
  | (Ite) e\<^sub>1 e\<^sub>2 e\<^sub>3 where \<open>e = (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close>
  | (Extract) e\<^sub>1 sz\<^sub>1 sz\<^sub>2 where \<open>e = (Extract sz\<^sub>1 sz\<^sub>2 e\<^sub>1)\<close>
  apply (rule exp_syntax_exhaust[of e])
  apply blast+
  apply (cases e)
  subgoal for v
    apply (rule val_exhaust[of v])
    by (simp_all add: Val_simp_word Val_simp_storage Val_simp_unknown)
  apply (metis var_constructor_exp_def var_exhaust)
  apply blast+
  apply (rule Store, blast)
  apply (rule BinOp, blast)
  apply (rule UnOp, blast)
  apply (rule Cast, blast)
  apply (rule Let, blast)
  apply (rule Ite, blast)
  apply (rule Extract, blast)
  subgoal for e\<^sub>1 e\<^sub>2
    by auto
  .

locale not_exp_val =
    fixes exp :: exp
  assumes not_val[simp]: \<open>\<And>v. exp \<noteq> Val v\<close>
begin

lemma not_val'[simp]: \<open>\<And>v. Val v \<noteq> exp\<close>
  using not_val by blast

lemma not_true[simp]: \<open>exp \<noteq> true\<close> \<open>true \<noteq> exp\<close>
  unfolding  word_constructor_exp_def by (rule not_val not_val')+

lemma not_false[simp]: \<open>exp \<noteq> false\<close> \<open>false \<noteq> exp\<close>
  unfolding  word_constructor_exp_def by (rule not_val not_val')+

lemma not_bv_concat[simp]: \<open>exp \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) \<noteq> exp\<close>
  unfolding bv_concat.simps unfolding word_constructor_exp_def by (rule not_val not_val')+
end

locale neq_exp =
    fixes exp :: exp
  assumes not_load[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 en sz. exp \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close>
      and not_store[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz. exp \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close>
      and not_binop[simp]: \<open>\<And>bop e\<^sub>1 e\<^sub>2. exp \<noteq> (BinOp e\<^sub>1 bop e\<^sub>2)\<close>
      and not_unop[simp]: \<open>\<And>uop e\<^sub>1. exp \<noteq> (UnOp uop e\<^sub>1)\<close>
      and not_cast[simp]: \<open>\<And>e\<^sub>1 cast sz. exp \<noteq> ((cast::Cast):sz[e\<^sub>1])\<close>
      and not_let[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 var. exp \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close>
      and not_ite[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3. exp \<noteq> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close>
      and not_extract[simp]: \<open>\<And>e\<^sub>1 sz\<^sub>2 sz\<^sub>1. exp \<noteq> (Extract sz\<^sub>1 sz\<^sub>2 e\<^sub>1)\<close>
      and not_concat[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2. exp \<noteq> e\<^sub>1 \<copyright> e\<^sub>2\<close>
begin

lemma not_load'[simp]: \<open>(e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> exp\<close>
  using not_load by auto

lemma not_store'[simp]: \<open>(e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> exp\<close>
  using not_store by auto

lemma not_binop'[simp]: \<open>(BinOp e\<^sub>1 bop e\<^sub>2) \<noteq> exp\<close>
  using not_binop by auto

lemma not_unop'[simp]: \<open>(UnOp uop e\<^sub>1) \<noteq> exp\<close>
  using not_unop by auto

lemma not_cast'[simp]: \<open>((cast::Cast):sz[e\<^sub>1]) \<noteq> exp\<close>
  using not_cast by auto

lemma not_let'[simp]: \<open>(Let var e\<^sub>1 e\<^sub>2) \<noteq> exp\<close>
  using not_let by auto

lemma not_ite'[simp]: \<open>(Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> exp\<close>
  using not_ite by auto

lemma not_extract'[simp]: \<open>(extract:sz\<^sub>1:sz\<^sub>2[e]) \<noteq> exp\<close>
  using not_extract by auto

lemma not_concat'[simp]: \<open>e\<^sub>1 \<copyright> e\<^sub>2 \<noteq> exp\<close>
  using not_concat by auto

lemma not_other_bops[simp]: 
  \<open>e\<^sub>1 + e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 + e\<^sub>2\<close> 
  \<open>e\<^sub>1 - e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 - e\<^sub>2\<close> 
  \<open>e\<^sub>1 * e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 * e\<^sub>2\<close> 
  \<open>e\<^sub>1 div e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 div e\<^sub>2\<close> 
  \<open>e\<^sub>1 mod e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 mod e\<^sub>2\<close> 
  \<open>e\<^sub>1 sdiv e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 sdiv e\<^sub>2\<close> 
  \<open>e\<^sub>1 smod e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 smod e\<^sub>2\<close> 
  \<open>e\<^sub>1 && e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 && e\<^sub>2\<close> 
  \<open>e\<^sub>1 || e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 || e\<^sub>2\<close> 
  \<open>e\<^sub>1 xor e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 xor e\<^sub>2\<close> 
  \<open>e\<^sub>1 << e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 << e\<^sub>2\<close> 
  \<open>e\<^sub>1 >> e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 >> e\<^sub>2\<close> 
  \<open>e\<^sub>1 >>> e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 >>> e\<^sub>2\<close> 
  \<open>e\<^sub>1 le e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 le e\<^sub>2\<close> 
  \<open>e\<^sub>1 lt e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 lt e\<^sub>2\<close> 
  \<open>e\<^sub>1 sle e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 sle e\<^sub>2\<close> 
  \<open>e\<^sub>1 slt e\<^sub>2 \<noteq> exp\<close> \<open>exp \<noteq> e\<^sub>1 slt e\<^sub>2\<close> 
  unfolding bop_syntax by simp_all

lemma not_other_uops[simp]: \<open>-e \<noteq> exp\<close> \<open>exp \<noteq> -e\<close> \<open>\<sim>e \<noteq> exp\<close> \<open>exp \<noteq> \<sim>e\<close>
  unfolding uminus_exp_def not_exp_def by simp_all

end

locale neq_exp_and_val = not_exp_val + neq_exp


interpretation var: neq_exp_and_val \<open>(id' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by (standard, auto)

interpretation val: neq_exp \<open>Val v\<close>
  by (standard, auto)

interpretation storage: neq_exp \<open>(v[w \<leftarrow> v', sz])\<close>
  unfolding storage_constructor_exp_def by (standard, auto)

interpretation word: neq_exp \<open>(num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def by (standard, auto)

interpretation unknown: neq_exp \<open>(unknown[str]: t)\<close>
  unfolding unknown_constructor_exp_def by (standard, auto)

interpretation true: neq_exp \<open>true\<close>
  by (standard, auto)

interpretation false: neq_exp \<open>false\<close>
  by (standard, auto)

interpretation concat: neq_exp \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding bv_concat.simps by (standard, auto)

interpretation plus: neq_exp \<open>(num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_plus.simps by (standard, auto)

interpretation minus: neq_exp \<open>(num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_minus.simps by (standard, auto)

interpretation times: neq_exp \<open>(num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_times.simps by (standard, auto)

interpretation divide: neq_exp \<open>(num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_divide.simps by (standard, auto)

interpretation sdivide: neq_exp \<open>(num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_sdivide.simps by (standard, auto)

interpretation mod: neq_exp \<open>(num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_mod\<^sub>b\<^sub>v.simps by (standard, auto)

interpretation smod: neq_exp \<open>(num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_smod.simps by (standard, auto)

interpretation lsl: neq_exp \<open>(num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lsl.simps by (standard, auto)

interpretation lsr: neq_exp \<open>(num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lsr.simps by (standard, auto)

interpretation asr: neq_exp \<open>(num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_asr.simps by (standard, auto)

interpretation land: neq_exp \<open>(num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_land.simps by (standard, auto)

interpretation lor: neq_exp \<open>(num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lor.simps by (standard, auto)

interpretation xor: neq_exp \<open>(num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_xor.simps by (standard, auto)

interpretation lt: neq_exp \<open>(num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lt.simps by (standard, auto)

interpretation le: neq_exp \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lt.simps bv_lor.simps bv_eq_def by (standard, auto)

interpretation slt: neq_exp \<open>(num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_slt.simps by (standard, auto)

interpretation sle: neq_exp \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_slt.simps bv_lor.simps bv_eq_def by (standard, auto)

interpretation uminus: neq_exp \<open>-\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  unfolding bv_uminus.simps by (standard, auto)

interpretation not: neq_exp \<open>~\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  unfolding bv_negation.simps by (standard, auto)

interpretation xtract: neq_exp \<open>ext (num \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w\<close>
  unfolding xtract.simps by (standard, auto)

lemma bops_no_overlap[simp]:
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') + ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') - ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') * ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') div ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sdiv ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') mod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') smod ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') << ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') >>> ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') && ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') || ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') xor ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') lt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') slt ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') le ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)\<close>
    \<open>(num\<^sub>1' \<Colon> sz') sle ((num\<^sub>2' \<Colon> sz')::exp) \<noteq> (num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bop_syntax by simp_all

lemma capture_avoiding_var[simp]: \<open>[val\<sslash>(nm :\<^sub>t tp)](nm :\<^sub>t tp) = Val val\<close>
  by (simp add: var_constructor_exp_def)

lemma capture_avoiding_var_neq[intro]: \<open>var \<noteq> (nm :\<^sub>t tp) \<Longrightarrow> [val\<sslash>var](nm :\<^sub>t tp) = (nm :\<^sub>t tp)\<close>
  by (simp add: var_constructor_exp_def)

lemma capture_avoiding_var_name_neq[intro]: \<open>nm1 \<noteq> nm2 \<Longrightarrow> [val\<sslash>(nm1 :\<^sub>t tp)](nm2 :\<^sub>t tp) = (nm2 :\<^sub>t tp)\<close>
  by (simp add: capture_avoiding_var_neq)

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
  shows \<open>\<Gamma> \<turnstile> (\<sim> e) :: imm\<langle>sz\<rangle>\<close>
  unfolding not_exp_def
  using assms by (rule uop_exp_typed_okI)

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
    shows \<open>\<Gamma> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e] :: imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>\<close>
  using assms unfolding typed_ok_exp.simps by blast

lemma extract_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> extract:sz\<^sub>1:sz\<^sub>2[e] :: imm\<langle>Suc (sz\<^sub>1 - sz\<^sub>2)\<rangle>\<close>
    shows \<open>\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>) \<and> sz\<^sub>1 \<ge> sz\<^sub>2\<close>
  using assms unfolding typed_ok_exp.simps by auto
  
lemma concat_exp_typed_okI: 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>\<close>
    shows \<open>\<Gamma> \<turnstile> (e\<^sub>1::exp) \<copyright> e\<^sub>2 :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
  using assms unfolding typed_ok_exp.simps by auto

lemma concat_exp_typed_okE: 
  assumes \<open>\<Gamma> \<turnstile> (e\<^sub>1::exp) \<copyright> e\<^sub>2 :: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
    shows \<open>\<exists>sz\<^sub>1 sz\<^sub>2. (\<Gamma> \<turnstile> e\<^sub>1 :: imm\<langle>sz\<^sub>1\<rangle>) \<and> (\<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>2\<rangle>)\<close>
  using assms unfolding typed_ok_exp.simps by auto
  
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

(*
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
*)

method typec_exp = (fastforce)

end
