
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

fun 
  lsr_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 >> e2 = (BinOp e1 (AOp RShift) e2)\<close>

fun 
  lsl_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 << e2 = (BinOp e1 (AOp LShift) e2)\<close>

fun 
  asr_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 >>> e2 = (BinOp e1 (AOp ARShift) e2)\<close>

fun 
  land_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 && e2 = (BinOp e1 (AOp And) e2)\<close>

fun 
  lor_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 || e2 = (BinOp e1 (AOp Or) e2)\<close>

fun 
  xor_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 xor e2 = (BinOp e1 (AOp Xor) e2)\<close>

fun 
  sdivide_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 sdiv e2 = (BinOp e1 (AOp SDivide) e2)\<close>

fun 
  smod_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 smod e2 = (BinOp e1 (AOp SMod) e2)\<close>

fun 
  negation_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>negation_exp e1 = (UnOp Not e1)\<close>
(*
definition 
  true_exp :: exp
where
  \<open>true_exp = (Val true)\<close>

definition 
  false_exp :: exp
where
  \<open>false_exp = (Val false)\<close>
*)
fun 
  lt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 lt e2 = (BinOp e1 (LOp Lt) e2)\<close>

fun 
  le_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 le e2 = (BinOp e1 (LOp Le) e2)\<close>

fun 
  slt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 slt e2 = (BinOp e1 (LOp Slt) e2)\<close>

fun 
  sle_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 sle e2 = (BinOp e1 (LOp Sle) e2)\<close>

fun 
  uminus_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>uminus_exp e1 = (UnOp Neg e1)\<close>

fun 
  minus_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>minus_exp e1 e2 = (BinOp e1 (AOp Minus) e2)\<close>

fun 
  plus_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>plus_exp e1 e2 = (BinOp e1 (AOp Plus) e2)\<close>

fun 
  times_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>times_exp e1 e2 = (BinOp e1 (AOp Times) e2)\<close>

fun 
  modulo_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>modulo_exp e1 e2 = (BinOp e1 (AOp Mod) e2)\<close>

fun 
  divide_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>divide_exp e1 e2 = (BinOp e1 (AOp Divide) e2)\<close>
(*
lemma true_not_false_exp: \<open>(true::exp) \<noteq> false\<close>
  by (simp add: false_exp_def true_exp_def)
*)
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
  (*using true_not_false_exp*) apply auto
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def 
            var_constructor_exp_def append_exp_def true_word false_word
  by auto

end

lemma plus_binop_inject[simp]: 
    \<open>e\<^sub>1 + e\<^sub>2 = BinOp e\<^sub>3 bop e\<^sub>4 \<longleftrightarrow> (e\<^sub>3 = e\<^sub>1 \<and> e\<^sub>4 = e\<^sub>2 \<and> bop = AOp Plus)\<close>
    \<open>BinOp e\<^sub>3 bop e\<^sub>4 = e\<^sub>1 + e\<^sub>2 \<longleftrightarrow> (e\<^sub>3 = e\<^sub>1 \<and> e\<^sub>4 = e\<^sub>2 \<and> bop = AOp Plus)\<close>
  by auto

lemma exp_def_simps[simp]:
  \<open>\<And>e\<^sub>1 e\<^sub>2 en sz e\<^sub>3 e\<^sub>4. e\<^sub>3 + e\<^sub>4 \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 en sz e\<^sub>3 e\<^sub>4. (e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> e\<^sub>3 + e\<^sub>4\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4 e\<^sub>5 en sz. e\<^sub>4 + e\<^sub>5 \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e\<^sub>3 e\<^sub>4 e\<^sub>5 en sz. (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> e\<^sub>4 + e\<^sub>5\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e cast sz. e\<^sub>1 + e\<^sub>2 \<noteq> (Cast cast sz e)\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e cast sz. (Cast cast sz e) \<noteq> e\<^sub>1 + e\<^sub>2\<close>
  \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2 var. e\<^sub>3 + e\<^sub>4 \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close>
  \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2 var. (Let var e\<^sub>1 e\<^sub>2) \<noteq> e\<^sub>3 + e\<^sub>4\<close>
  \<open>\<And>e\<^sub>4 e\<^sub>5 e\<^sub>1 e\<^sub>2 e\<^sub>3. e\<^sub>4 + e\<^sub>5 \<noteq> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close>
  \<open>\<And>e\<^sub>4 e\<^sub>5 e\<^sub>1 e\<^sub>2 e\<^sub>3. (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> e\<^sub>4 + e\<^sub>5\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e sz\<^sub>l\<^sub>o\<^sub>w sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h. e\<^sub>1 + e\<^sub>2 \<noteq> (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e])\<close>
  \<open>\<And>e\<^sub>1 e\<^sub>2 e sz\<^sub>l\<^sub>o\<^sub>w sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h. (extract:sz\<^sub>l\<^sub>o\<^sub>w:sz\<^sub>h\<^sub>i\<^sub>g\<^sub>h[e]) \<noteq> e\<^sub>1 + e\<^sub>2\<close>
  \<open>\<And>uop e\<^sub>1 e\<^sub>2 e\<^sub>3. UnOp uop e\<^sub>1 \<noteq> e\<^sub>2 + e\<^sub>3\<close>
  \<open>\<And>uop e\<^sub>1 e\<^sub>2 e\<^sub>3. e\<^sub>2 + e\<^sub>3 \<noteq> UnOp uop e\<^sub>1\<close>
  by simp_all

declare plus_exp.simps[simp del]


lemma storage_not_nested_exp[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz] \<noteq> Val v\<close>
  unfolding storage_constructor_exp_def by simp

(* TODO add to simpset *)
lemmas Val_simp_word = word_constructor_exp_def[symmetric]

lemmas Val_simp_storage = storage_constructor_exp_def[symmetric]

lemmas Val_simp_unknown = unknown_constructor_exp_def[symmetric]

no_notation List.append (infixr "@" 65)
no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)

lemma exp_exhaust:
  obtains 
    (Word) num sz where \<open>e = (num \<Colon> sz)\<close>
  | (Unknown) str t where \<open>e = (unknown[str]: t)\<close>
  | (Storage) mem w v' sz where \<open>e = (mem[w \<leftarrow> v', sz])\<close>
  | (Var) id t where \<open>e = (id :\<^sub>t t)\<close>
  | (Concat) e\<^sub>1 e\<^sub>2 where \<open>e = e\<^sub>1 @ e\<^sub>2\<close>
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
    unfolding append_exp_def by auto
  .

locale not_exp_val =
    fixes exp :: exp
  assumes not_val[simp]: \<open>\<And>v. exp \<noteq> Val v\<close>
begin

lemma not_true[simp]: \<open>exp \<noteq> true\<close>
  unfolding true_word word_constructor_exp_def by (rule not_val)

lemma not_false[simp]: \<open>exp \<noteq> false\<close>
  unfolding false_word word_constructor_exp_def by (rule not_val)

lemma not_bv_concat[simp]: \<open>exp \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding bv_concat.simps unfolding word_constructor_exp_def by (rule not_val)
end

locale not_exp =
    fixes exp :: exp
  assumes not_load[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 en sz. exp \<noteq> (e\<^sub>1[e\<^sub>2, en]:usz)\<close>
      and not_store[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz. exp \<noteq> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3)\<close>
      and not_binop[simp]: \<open>\<forall>bop e\<^sub>1 e\<^sub>2. exp \<noteq> (BinOp e\<^sub>1 bop e\<^sub>2)\<close>
      and not_unop[simp]: \<open>\<forall>uop e\<^sub>1. exp \<noteq> (UnOp uop e\<^sub>1)\<close>
      and not_cast[simp]: \<open>\<forall>e\<^sub>1 cast sz. exp \<noteq> ((cast::Cast):sz[e\<^sub>1])\<close>
      and not_let[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 var. exp \<noteq> (Let var e\<^sub>1 e\<^sub>2)\<close>
      and not_ite[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 e\<^sub>3. exp \<noteq> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3)\<close>
      and not_extract[simp]: \<open>\<forall>e\<^sub>1 sz\<^sub>2 sz\<^sub>1. exp \<noteq> (Extract sz\<^sub>1 sz\<^sub>2 e\<^sub>1)\<close>
begin

lemma not_load'[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 en sz. (e\<^sub>1[e\<^sub>2, en]:usz) \<noteq> exp\<close>
  using not_load by auto

lemma not_store'[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 e\<^sub>3 en sz. (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<noteq> exp\<close>
  using not_store by auto

lemma not_binop'[simp]: \<open>\<forall>bop e\<^sub>1 e\<^sub>2. (BinOp e\<^sub>1 bop e\<^sub>2) \<noteq> exp\<close>
  using not_binop by auto

lemma not_unop'[simp]: \<open>\<forall>uop e\<^sub>1. (UnOp uop e\<^sub>1) \<noteq> exp\<close>
  using not_unop by auto

lemma not_cast'[simp]: \<open>\<forall>e\<^sub>1 cast sz. ((cast::Cast):sz[e\<^sub>1]) \<noteq> exp\<close>
  using not_cast by auto

lemma not_let'[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 var. (Let var e\<^sub>1 e\<^sub>2) \<noteq> exp\<close>
  using not_let by auto

lemma not_ite'[simp]: \<open>\<forall>e\<^sub>1 e\<^sub>2 e\<^sub>3. (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<noteq> exp\<close>
  using not_ite by auto

lemma not_extract'[simp]: \<open>\<forall>e\<^sub>1 sz\<^sub>2 sz\<^sub>1. (Extract sz\<^sub>1 sz\<^sub>2 e\<^sub>1) \<noteq> exp\<close>
  using not_extract by auto

end


locale not_exp_and_val = not_exp_val + not_exp


interpretation concat: not_exp_and_val \<open>e\<^sub>1 @ e\<^sub>2\<close>
  apply (standard, auto)
  unfolding append_exp_def by auto

interpretation var: not_exp_and_val \<open>(id' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def by (standard, auto)

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

interpretation concat_bv: not_exp \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
  unfolding bv_concat.simps by (standard, auto)

end
