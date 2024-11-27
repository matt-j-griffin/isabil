
section \<open>Syntax\<close>

theory Expression_Syntax
  imports "../Val_Instance" (*TODO*)
          "../Formula_Syntax"
begin

text \<open>Some evaluation rules depend on the type of a value. Since there are two canonical forms for
each type, we avoid duplicating each rule by defining the following metafunction:\<close>

method solve_typeI_scaffold methods recurs = (
  assumption | 
  rule type_wordI type_storageI type_unknownI type_trueI type_falseI type_plusI |
  (rule type_succ_recI, recurs) |
  (rule type_storage_addrI, recurs) 
) 

method solve_typeI = (
  solve_typeI_scaffold solve_typeI
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
  negation_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>negation_exp e1 = (UnOp Not e1)\<close>

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
termination by (standard, auto)

instance 
  apply standard 
  apply auto
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def 
            var_constructor_exp_def true_word false_word bop_syntax 
  by auto

end

subsubsection \<open>Syntax for UOPs\<close>

lemma uminus_simps[simp]:
  \<open>- w \<noteq> Val v\<close> \<open>Val v \<noteq> - w\<close>
  \<open>- w \<noteq> e\<^sub>1 \<copyright> e\<^sub>2\<close> \<open>(e\<^sub>1 \<copyright> e\<^sub>2) \<noteq> - w\<close>
  \<open>- w \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close> \<open>(e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> - w\<close>
  \<open>- w \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close> \<open>(e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> - w\<close>
  \<open>- w \<noteq> (Cast cast sz e)\<close> \<open>(Cast cast sz e) \<noteq> - w\<close>
  \<open>- w \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close> \<open>(Let var e\<^sub>1 e\<^sub>2) \<noteq> - w\<close>
  \<open>- w \<noteq> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close> \<open>(ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> - w\<close>
  \<open>- w \<noteq> (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e])\<close> \<open>(extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e]) \<noteq> - w\<close>
  \<open>- w \<noteq> BinOp e\<^sub>1 bop e\<^sub>2\<close> \<open>BinOp e\<^sub>1 bop e\<^sub>2  \<noteq> - w\<close>
  unfolding uminus_exp_def by simp_all

lemma inject[simp]: 
  \<open>(- v = - v') \<longleftrightarrow> (v = v')\<close>
  \<open>(UnOp uop v = - v') \<longleftrightarrow> (uop = Neg \<and> v = v')\<close>
  \<open>(- v = UnOp uop v') \<longleftrightarrow> (Neg = uop \<and> v = v')\<close>
  unfolding uminus_exp_def by auto

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
  unfolding bop_simps by simp_all

lemma binop_inject[simp]: 
    \<open>(bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1' bop' e\<^sub>2') \<longleftrightarrow> (e\<^sub>1 = e\<^sub>1' \<and> bop = bop' \<and> e\<^sub>2 = e\<^sub>2')\<close>
    \<open>(BinOp e\<^sub>1' bop' e\<^sub>2' = bop_fun e\<^sub>1 e\<^sub>2) \<longleftrightarrow> (e\<^sub>1' = e\<^sub>1 \<and> bop' = bop \<and> e\<^sub>2' = e\<^sub>2)\<close>
  by (auto simp add: bop_simps)

lemma inject[simp]: \<open>(bop_fun e\<^sub>1 e\<^sub>2 = bop_fun e\<^sub>1' e\<^sub>2') \<longleftrightarrow> (e\<^sub>1 = e\<^sub>1' \<and> e\<^sub>2 = e\<^sub>2')\<close>
  by (simp add: bop_simps)

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
  unfolding true_word word_constructor_exp_def by (rule not_val not_val')+

lemma not_false[simp]: \<open>exp \<noteq> false\<close> \<open>false \<noteq> exp\<close>
  unfolding false_word word_constructor_exp_def by (rule not_val not_val')+

lemma not_bv_concat[simp]: \<open>exp \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) \<noteq> exp\<close>
  unfolding bv_concat.simps unfolding word_constructor_exp_def by (rule not_val not_val')+
end

locale not_exp =
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

lemma not_other_uops[simp]: \<open>-e \<noteq> exp\<close> \<open>exp \<noteq> -e\<close>
  unfolding uminus_exp_def by simp_all

end

locale not_exp_and_val = not_exp_val + not_exp


interpretation var: not_exp_and_val \<open>(id' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by (standard, auto)

interpretation val: not_exp \<open>Val v\<close>
  by (standard, auto)

interpretation storage: not_exp \<open>(v[w \<leftarrow> v', sz])\<close>
  unfolding storage_constructor_exp_def by (standard, auto)

interpretation word: not_exp \<open>(num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def by (standard, auto)

interpretation unknown: not_exp \<open>(unknown[str]: t)\<close>
  unfolding unknown_constructor_exp_def by (standard, auto)

interpretation true: not_exp \<open>true\<close>
  unfolding true_word by (standard, auto)

interpretation false: not_exp \<open>false\<close>
  unfolding false_word by (standard, auto)

interpretation concat: not_exp \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding bv_concat.simps by (standard, auto)

interpretation plus: not_exp \<open>(num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_plus.simps by (standard, auto)

interpretation minus: not_exp \<open>(num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_minus.simps by (standard, auto)

interpretation times: not_exp \<open>(num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_times.simps by (standard, auto)

interpretation divide: not_exp \<open>(num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_divide.simps by (standard, auto)

interpretation sdivide: not_exp \<open>(num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_sdivide.simps by (standard, auto)

interpretation mod: not_exp \<open>(num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_mod\<^sub>b\<^sub>v.simps by (standard, auto)

interpretation smod: not_exp \<open>(num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_smod.simps by (standard, auto)

interpretation lsl: not_exp \<open>(num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lsl.simps by (standard, auto)

interpretation lsr: not_exp \<open>(num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lsr.simps by (standard, auto)

interpretation asr: not_exp \<open>(num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_asr.simps by (standard, auto)

interpretation land: not_exp \<open>(num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_land.simps by (standard, auto)

interpretation lor: not_exp \<open>(num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lor.simps by (standard, auto)

interpretation xor: not_exp \<open>(num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_xor.simps by (standard, auto)

interpretation lt: not_exp \<open>(num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lt.simps by (standard, auto)

interpretation le: not_exp \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lt.simps bv_lor.simps bv_eq_def by (standard, auto)

interpretation slt: not_exp \<open>(num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_slt.simps by (standard, auto)

interpretation sle: not_exp \<open>(num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_slt.simps bv_lor.simps bv_eq_def by (standard, auto)

interpretation uminus: not_exp \<open>-\<^sub>b\<^sub>v (num \<Colon> sz)\<close>
  unfolding bv_uminus.simps by (standard, auto)

interpretation xtract: not_exp \<open>ext (num \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w\<close>
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

end
