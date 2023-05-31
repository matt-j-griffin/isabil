
section \<open>Syntax\<close>

theory Expression_Syntax
  imports "../Val_Instance" (*TODO*)
          "../Formula_Syntax"
begin

text \<open>Some evaluation rules depend on the type of a value. Since there are two canonical forms for
each type, we avoid duplicating each rule by defining the following metafunction:\<close>

function (* TODO val_constructor/syntax*)
  type :: \<open>val \<Rightarrow> Type\<close>
where
  type_storageI: \<open>type (_[(_ \<Colon> nat') \<leftarrow> _, sz]) = mem\<langle>nat',sz\<rangle>\<close> | 
  type_wordI: \<open>type (_ \<Colon> nat') = imm\<langle>nat'\<rangle>\<close> | 
  type_unknownI: \<open>type (unknown[_]: t) = t\<close>
  subgoal for P x
    apply (cases x rule: val_exhaust)
    apply simp_all
    using word_exhaust by blast
  by auto

termination by (standard, auto)

lemma type_storage_not_imm[simp]: \<open>type (mem[w \<leftarrow> v', sz]) \<noteq> imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close>
  apply (rule notI)
  apply (erule type.elims)
  by simp_all

lemma type_word_not_mem[simp]: \<open>type (num \<Colon> sz) \<noteq> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  apply (rule notI)
  apply (erule type.elims)
  by simp_all

(*
lemma type_unknownE:
  assumes \<open>type (unknown[str]: t') = t\<close>
    shows \<open>t = t'\<close>
  using assms unfolding type.simps by clarify

lemma type_unknown_not_mem[simp]: \<open>type (num \<Colon> sz) \<noteq> mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
  apply (rule notI)
  apply (erule type.elims)
  by simp_all
*)


context word_constructor
begin

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

end

instantiation exp :: exp
begin

definition 
  var_constructor_exp :: \<open>string \<Rightarrow> Type \<Rightarrow> exp\<close>
where
  \<open>(a :\<^sub>t b) \<equiv> Var (a :\<^sub>t b)\<close>

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

definition 
  true_exp :: exp
where
  \<open>true_exp = (Val true)\<close>

definition 
  false_exp :: exp
where
  \<open>false_exp = (Val false)\<close>

fun 
  lt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 lt e2 = (BinOp e1 (LOp Lt) e2)\<close>

fun 
  lteq_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 lteq e2 = (BinOp e1 (LOp Le) e2)\<close>

fun 
  slt_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 slt e2 = (BinOp e1 (LOp Slt) e2)\<close>

fun 
  slteq_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>e1 slteq e2 = (BinOp e1 (LOp Sle) e2)\<close>

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

declare plus_exp.simps[simp del]

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

lemma true_not_false_exp: \<open>(true::exp) \<noteq> false\<close>
  by (simp add: false_exp_def true_exp_def)

instance 
  apply standard 
  unfolding storage_constructor_exp_def word_constructor_exp_def unknown_constructor_exp_def 
            var_constructor_exp_def append_exp_def
  apply (simp_all add: true_not_false_exp true_exp_def false_exp_def)
  apply (simp add: true_word)  
  apply (simp add: false_word)
  done

end
(* TODO add to simpset *)
lemma Val_simp_word: \<open>Val (a \<Colon> b) = (a \<Colon> b)\<close>
  by (simp add: word_constructor_exp_def)

lemma Val_simp_storage: \<open>Val (v[a \<leftarrow> v', sz]) = (v[a \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def)

lemma Val_simp_unknown: \<open>Val (unknown[str]: t) = unknown[str]: t\<close>
  by (simp add: unknown_constructor_exp_def)

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
  assumes not_val[simp]: \<open>\<forall>v. exp \<noteq> Val v\<close>
      and not_true[simp]: \<open>exp \<noteq> true\<close>
      and not_false[simp]: \<open>exp \<noteq> false\<close>

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
  unfolding true_exp_def false_exp_def append_exp_def by auto

interpretation var: not_exp_and_val \<open>(id' :\<^sub>t t)\<close>
  unfolding var_constructor_exp_def apply (standard, auto)
  unfolding true_exp_def false_exp_def by auto

interpretation storage: not_exp \<open>(v[w \<leftarrow> v', sz])\<close>
  unfolding storage_constructor_exp_def by (standard, auto)

interpretation word: not_exp \<open>(num \<Colon> sz)\<close>
  unfolding word_constructor_exp_def by (standard, auto)

interpretation unknown: not_exp \<open>(unknown[str]: t)\<close>
  unfolding unknown_constructor_exp_def by (standard, auto)

interpretation true: not_exp \<open>true\<close>
  unfolding true_exp_def by (standard, auto)

interpretation false: not_exp \<open>false\<close>
  unfolding false_exp_def by (standard, auto)

function
  concat_en :: \<open>val \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>concat_en (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) be = ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |
  \<open>concat_en (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) el = ((num\<^sub>2 \<Colon> sz\<^sub>2) \<cdot> (num\<^sub>1 \<Colon> sz\<^sub>1))\<close> |
  \<open>concat_en (_ \<Colon> sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) _ = unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (_ \<Colon> sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t) _ = unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) be
    = (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>)\<close> |
  \<open>concat_en (unknown[str\<^sub>l\<^sub>e\<^sub>f\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t\<rangle>) (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>) el
    = (unknown[str\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t]: imm\<langle>sz\<^sub>l\<^sub>e\<^sub>f\<^sub>t + sz\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t\<rangle>)\<close> |
  \<open>\<lbrakk>type v\<^sub>1 = mem\<langle>_, _\<rangle> \<or> type v\<^sub>2 = mem\<langle>_, _\<rangle>\<rbrakk> \<Longrightarrow> concat_en v\<^sub>1 v\<^sub>2 _ = undefined\<close>
  subgoal for P x 
    apply (cases x)
    apply simp
    subgoal for v\<^sub>1 v\<^sub>2 en
      apply (cases en)
      apply simp_all
      subgoal
        apply (cases v\<^sub>1 rule: val_exhaust)
        apply simp_all
        subgoal
          apply (cases v\<^sub>2 rule: val_exhaust)
          apply simp_all
          subgoal for str t
            apply (cases t)
            apply simp_all
            by blast
          subgoal
            by (metis type.simps(1) word_exhaust)
          .
        subgoal for str t
          apply (cases t)
          subgoal
            apply (cases v\<^sub>2 rule: val_exhaust)
            apply simp_all
            subgoal for str' t'
              apply (cases t')
              apply simp_all
              by blast
            by (metis type.elims unknown_storage_neq word_storage_neq)
          using type.simps(3) by blast
        by (metis type.elims unknown_storage_neq word_storage_neq)
      subgoal
        apply (cases v\<^sub>1 rule: val_exhaust)
        apply simp_all
        subgoal
          apply (cases v\<^sub>2 rule: val_exhaust)
          apply simp_all
          subgoal for str t
            apply (cases t)
            apply simp_all
            by blast
          subgoal
            by (metis type.simps(1) word_exhaust)
          .
        subgoal for str t
          apply (cases t)
          subgoal
            apply (cases v\<^sub>2 rule: val_exhaust)
            apply simp_all
            subgoal for str' t'
              apply (cases t')
              apply simp_all
              by blast
            by (metis type.elims unknown_storage_neq word_storage_neq)
          using type.simps(3) by blast
        by (metis type.elims unknown_storage_neq word_storage_neq)
      .
    .
  by auto

termination by (standard, auto)

function
  load_byte :: \<open>val \<Rightarrow> word \<Rightarrow> val\<close>
where
  \<open>\<lbrakk>w\<^sub>m\<^sub>e\<^sub>m = w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, _]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = v\<^sub>m\<^sub>e\<^sub>m\<close> |
  \<open>\<lbrakk>w\<^sub>m\<^sub>e\<^sub>m \<noteq> w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk> \<Longrightarrow> load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> _, _]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = load_byte mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close> |
  \<open>load_byte (unknown[str]: mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) _ = unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<close> |
  \<open>type v = imm\<langle>_\<rangle> \<Longrightarrow> load_byte v _ = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for v w
      apply (cases v rule: val_exhaust)
      apply auto
      using type.simps(2) apply blast
      subgoal for str t
        apply (cases t, auto)
        by (metis type.simps(3))
      by fastforce
    .
  apply simp_all
  apply (metis Type.distinct(1) type.cases type.simps(1) unknown_storage_neq word_storage_neq)
  by auto

termination 
  apply (relation \<open>(\<lambda>p. size_class.size (fst p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  unfolding storage_constructor_val_def
  by (rule mlex_less, simp)

function
  load :: \<open>val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>v\<^sub>a\<^sub>l]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l _ = (
      load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>v\<^sub>a\<^sub>l]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    undefined     
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    undefined     
  )\<close> |
  \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
      let 
        v\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en;
        v\<^sub>l\<^sub>e\<^sub>f\<^sub>t = load_byte (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r
      in concat_en v\<^sub>l\<^sub>e\<^sub>f\<^sub>t v\<^sub>r\<^sub>i\<^sub>g\<^sub>h\<^sub>t en
  )\<close> |
  \<open>load (unknown[str]: _) _ sz\<^sub>v\<^sub>a\<^sub>l _ = unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle> \<close> |
  \<open>load (_ \<Colon> _) _ _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, simp)
    subgoal for v
      apply (cases v rule: val_exhaust)
      apply auto
      by (metis gr0I linorder_less_linear)
    .
  by auto

termination
  apply (relation "(\<lambda>p. size_class.size (fst (snd (snd p)))) <*mlex*> (\<lambda>p. size_class.size (fst p)) <*mlex*> {}")
  by (simp_all add: wf_mlex mlex_less)

subsubsection \<open>Store\<close>

function
  store :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<comment> \<open>Big endian store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) be = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - 1) \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l'), sz\<^sub>m\<^sub>e\<^sub>m]
        in
          store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l' - 1) \<sim> lo : 0) be
  )\<close> |
  \<comment> \<open>Little endian store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) el = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>m\<^sub>e\<^sub>m - 1) \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m]
        in
          store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (ext (num \<Colon> sz\<^sub>v\<^sub>a\<^sub>l) \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - 1) \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) el
  )\<close> |
  \<comment> \<open>Unknown store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>) en = (
    case type mem of mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow>
        let 
          sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
          mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>), sz\<^sub>m\<^sub>e\<^sub>m] in
            store mem' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l'\<rangle>) en
  )\<close> |
  \<comment> \<open>Byte store\<close>
  \<open>\<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; type v\<^sub>v\<^sub>a\<^sub>l = imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0\<rbrakk> \<Longrightarrow> store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l _ = (
    case type v\<^sub>v\<^sub>a\<^sub>l of imm\<langle>sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Rightarrow> (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  (* Illegal cases *)
  \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; type v\<^sub>v\<^sub>a\<^sub>l = imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> store mem _ v\<^sub>v\<^sub>a\<^sub>l _ = undefined\<close> |
  \<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = mem\<langle>_,sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk> \<Longrightarrow> store mem _ _ _ = undefined\<close> |
  \<open>\<lbrakk>type val = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> store _ _ val _ = undefined\<close>|
  \<open>\<lbrakk>type mem = imm\<langle>_\<rangle>\<rbrakk> \<Longrightarrow> store mem _ _ _ = undefined\<close>
  subgoal
    for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l en
      apply (cases \<open>type v\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
      apply (cases \<open>type v\<^sub>v\<^sub>a\<^sub>l\<close>, simp_all)
      subgoal for sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz\<^sub>v\<^sub>a\<^sub>l
        apply (cases \<open>sz\<^sub>m\<^sub>e\<^sub>m = 0\<close>, simp_all)
        apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
        apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m\<close>, simp_all)
        apply (rule linorder_neqE_nat, auto)
        apply (rule val_exhaust[of v\<^sub>m\<^sub>e\<^sub>m], auto)
        subgoal
          apply (rule val_exhaust[of v\<^sub>v\<^sub>a\<^sub>l], auto)
          subgoal by (cases en)
          .
        subgoal
          apply (rule val_exhaust[of v\<^sub>v\<^sub>a\<^sub>l], auto)
          subgoal by (cases en)
          .
        .
      .
    .
  by auto
termination
  apply (relation \<open>(\<lambda>(_,_,v\<^sub>v\<^sub>a\<^sub>l,_). case (type v\<^sub>v\<^sub>a\<^sub>l) of imm\<langle>sz\<rangle> \<Rightarrow> size_class.size sz) <*mlex*> {}\<close>)
  subgoal
    apply (rule wf_mlex)
    by blast
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv xtract.simps
    by simp
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv xtract.simps
    by simp
  subgoal
    apply (rule mlex_less)
    unfolding case_prod_beta snd_conv fst_conv
    by simp
  .

subsubsection \<open>Expression evaluation\<close>

context word_constructor
begin

primrec 
  operator_unop :: \<open>UnOp \<Rightarrow> ('a \<Rightarrow> 'a)\<close>
where
  \<open>operator_unop Not = bv_negation\<close> |
  \<open>operator_unop Neg = bv_uminus\<close>

primrec
  operator_lop :: \<open>LOp \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)\<close>
where
  \<open>operator_lop Eq = (=\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Neq = (\<noteq>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Lt = (<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Le = (\<le>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Slt = (<\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Sle = (\<le>\<^sub>s\<^sub>b\<^sub>v)\<close>

primrec
  operator_aop :: \<open>AOp \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)\<close>
where
  \<open>operator_aop Plus = (+\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Minus = (-\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Times = (*\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Divide = (div\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SDivide = (div\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Mod = (%\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SMod = (%\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop And = (&\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Or = (|\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Xor = (xor\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop LShift = (<<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop RShift = (>>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop ARShift = (>>>\<^sub>b\<^sub>v)\<close>
end

context val_syntax
begin

function 
  eval_unop :: \<open>UnOp \<Rightarrow> 'a \<Rightarrow> 'a\<close>
where
  \<open>eval_unop _ (unknown[str]: t) = unknown[str]: t\<close> |
  \<open>eval_unop uop (num \<Colon> sz) = (operator_unop uop) ((num \<Colon> sz))\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_unop _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for uop v
      apply (rule val_syntax_exhaust[of v])
      by force+
    .
  by auto
termination by (standard, auto)

function 
  eval_binop :: \<open>BinOp \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
where
  \<open>eval_binop (AOp _) (unknown[str]: t) _ = unknown[str]: t\<close> |
  \<open>eval_binop (LOp _) (unknown[str]: _) _ = unknown[str]: imm\<langle>1\<rangle>\<close> |
  \<open>\<lbrakk>\<forall>str t. v \<noteq> unknown[str]: t\<rbrakk> \<Longrightarrow> eval_binop (AOp _) v (unknown[str]: t) = unknown[str]: t\<close> |
  \<open>\<lbrakk>\<forall>str t. v \<noteq> unknown[str]: t\<rbrakk> \<Longrightarrow> eval_binop (LOp _) v (unknown[str]: _) = unknown[str]: imm\<langle>1\<rangle>\<close> |
  \<open>eval_binop (AOp aop) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)
      = (operator_aop aop (num\<^sub>1 \<Colon> sz\<^sub>1) ((num\<^sub>2 \<Colon> sz\<^sub>2)))\<close> |
  \<open>eval_binop (LOp lop) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2)
      = (operator_lop lop (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |
  \<open>\<lbrakk>(\<forall>str t. v\<^sub>1 \<noteq> unknown[str]: t); (\<forall>str t. v\<^sub>2 \<noteq> unknown[str]: t);
    (\<forall>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. v\<^sub>1 \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1) \<or> v\<^sub>2 \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2))
   \<rbrakk> \<Longrightarrow> eval_binop _ v\<^sub>1 v\<^sub>2 = undefined\<close>
  subgoal for P x
    apply (cases x)
    subgoal for binop v\<^sub>1 v\<^sub>2
      apply (cases binop)
      subgoal for aop
        apply (rule val_syntax_exhaust[of v\<^sub>1])
        apply (rule val_syntax_exhaust[of v\<^sub>2])
        by force+
      subgoal for lop
        apply (rule val_syntax_exhaust[of v\<^sub>1])
        apply (rule val_syntax_exhaust[of v\<^sub>2])
        by force+
      .
    .
  by auto

termination by (standard, auto)

end


function 
  eval_cast :: \<open>Cast \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> val\<close>
where 
  \<open>eval_cast _ sz (unknown[str]: _) = unknown[str]: imm\<langle>sz\<rangle>\<close> |
  \<open>eval_cast low sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>eval_cast high sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz - 1) \<sim> lo : (sz - sz')\<close> |
  \<open>eval_cast extend sz' (num \<Colon> sz) = exts (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>eval_cast pad sz' (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : (sz' - 1) \<sim> lo : 0\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_cast _ _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for cast sz' v
      apply (cases v rule: val_exhaust)
      subgoal for num sz
        apply (cases cast)
        by force+
      apply force
      by fastforce
    .
  by auto

termination by (standard, auto)

function 
  eval_if :: \<open>val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val\<close>
where 
  \<open>eval_if (unknown[str]: _) v _ = unknown[str]: (type v)\<close> |
  \<open>eval_if true v _ = v\<close> |
  \<open>eval_if false _ v = v\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); v \<noteq> true; v \<noteq> false\<rbrakk> \<Longrightarrow> eval_if v _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>1 v\<^sub>2 v\<^sub>3
      apply (cases v\<^sub>1 rule: val_exhaust)
      by blast+
    .
  by auto

termination by (standard, auto)

function 
  eval_extract :: \<open>nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_extract sz\<^sub>1 sz\<^sub>2 (unknown[str]: t) = unknown[str]:imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>\<close> |
  \<open>eval_extract sz\<^sub>1 sz\<^sub>2 (num \<Colon> sz) = ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<close> |
  \<open>\<lbrakk>(\<forall>str t. v \<noteq> unknown[str]: t); (\<forall>num sz. v \<noteq> (num \<Colon> sz))\<rbrakk> \<Longrightarrow> eval_extract _ _ v = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for sz\<^sub>1 sz\<^sub>2 v
      apply (cases v rule: val_exhaust)
      by force+
    .
  by auto
termination by (standard, auto)

function 
  eval_concat :: \<open>val \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_concat (unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) (_ \<Colon> sz\<^sub>2) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) (unknown[_]: imm\<langle>sz\<^sub>2\<rangle>) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (_ \<Colon> sz\<^sub>1) (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) = unknown[str]:imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close> |
  \<open>eval_concat (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) = (num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)\<close> |
  \<open>\<lbrakk>type v\<^sub>1 = mem\<langle>_,_\<rangle> \<or> type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_concat v\<^sub>1 v\<^sub>2 = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for v\<^sub>1 v\<^sub>2
      apply (cases v\<^sub>1 rule: val_exhaust)
      subgoal
        apply (cases v\<^sub>2 rule: val_exhaust)
        apply force
        subgoal for _ t
          apply (cases t)
          apply blast
          by (metis type.simps(3))
        subgoal for _ w
          apply (cases w rule: word_exhaust)
          by (metis type.simps(1))
        .
      subgoal for _ t
        apply (cases t)
        subgoal
          apply (cases v\<^sub>2 rule: val_exhaust)
          apply blast
          subgoal for _ t'
            apply (cases t')
            apply blast
            apply clarsimp
            by blast
          by (metis type.simps(1) word_exhaust)        
        by (metis type.simps(3))
      by (metis type.simps(1) word_exhaust)
    .
  by auto
termination by (standard, auto)

lemma concat_en_be: \<open>concat_en v1 v2 be = eval_concat v1 v2\<close>
  by (induct v1 v2 rule: eval_concat.induct, auto)

lemma concat_en_el: \<open>concat_en v2 v1 el = eval_concat v1 v2\<close>
  apply (induct v1 v2 rule: eval_concat.induct, auto)
  using concat_en.simps(7) by blast+

function 
  eval_load :: \<open>val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>eval_load _ (unknown[str]: imm\<langle>_\<rangle>) sz\<^sub>v\<^sub>a\<^sub>l _ = unknown[str]: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>\<close> |
  \<open>eval_load v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) sz\<^sub>v\<^sub>a\<^sub>l en = load v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) sz\<^sub>v\<^sub>a\<^sub>l en\<close> |
  \<open>\<lbrakk>type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_load _ v\<^sub>2 _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for _ v\<^sub>2
      apply (cases v\<^sub>2 rule: val_exhaust)
      apply blast
      subgoal for _ t
        apply (cases t)
        apply blast
        using type.simps(3) by blast
      by (metis storage_constructor_val_def type.elims unknown_constructor_val_def val.distinct(5))
    .
  by auto
termination by (standard, auto)

function 
  eval_store :: \<open>val \<Rightarrow> val \<Rightarrow> Endian \<Rightarrow> val \<Rightarrow> val\<close>
where
  \<open>eval_store v\<^sub>1 (unknown[str]: imm\<langle>_\<rangle>) _ _ = unknown[str]: (type v\<^sub>1)\<close> |
  \<open>eval_store v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) en v\<^sub>3 = store v\<^sub>1 (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) v\<^sub>3 en\<close> |
  \<open>\<lbrakk>type v\<^sub>2 = mem\<langle>_,_\<rangle>\<rbrakk> \<Longrightarrow> eval_store _ v\<^sub>2 _ _ = undefined\<close>
  subgoal for P x
    apply (cases x, clarify)
    subgoal for _ v\<^sub>2
      apply (cases v\<^sub>2 rule: val_exhaust, safe)
      apply blast
      subgoal for _ t
        apply (cases t, safe)
        apply blast
        by (metis type.simps(3))
      apply auto
      by (metis type.elims unknown_storage_neq word_storage_neq)
    .
  by auto
termination by (standard, auto)

function
  eval_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val\<close>
where
  \<open>eval_exp _ (Val v) = v\<close> |
  \<open>eval_exp \<Delta> (name' :\<^sub>t t) = (if (name' :\<^sub>t t) \<in> dom \<Delta> then (the (\<Delta> (name' :\<^sub>t t))) else (unknown[[]]: t))\<close> | (* TODO a string method to describe ids*)
  \<open>eval_exp \<Delta> (UnOp uop e) = eval_unop uop (eval_exp \<Delta> e)\<close> |
  \<open>eval_exp \<Delta> (BinOp e\<^sub>1 binop e\<^sub>2) = eval_binop binop (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Cast cast sz e) = eval_cast cast sz (eval_exp \<Delta> e)\<close> |
  \<open>eval_exp \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (eval_exp (\<Delta> (var \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = eval_if (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) (eval_exp \<Delta> e\<^sub>3)\<close> |
  \<open>eval_exp \<Delta> (extract:sz\<^sub>1:sz\<^sub>2[e]) = (eval_extract sz\<^sub>1 sz\<^sub>2 (eval_exp \<Delta> e))\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1 @ e\<^sub>2) = eval_concat (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1[e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l) = eval_load (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) sz\<^sub>v\<^sub>a\<^sub>l en\<close> |
  \<open>eval_exp \<Delta> (e\<^sub>1 with [e\<^sub>2, en]:usz\<^sub>v\<^sub>a\<^sub>l \<leftarrow>  e\<^sub>3) = eval_store (eval_exp \<Delta> e\<^sub>1) (eval_exp \<Delta> e\<^sub>2) en (eval_exp \<Delta> e\<^sub>3)\<close>
  subgoal for P x
    apply (cases x)
    subgoal for \<Delta> e
      apply (rule exp_exhaust[of e])
      apply auto
      apply (simp add: word_constructor_exp_def)
      apply (simp add: unknown_constructor_exp_def)
      by (simp add: storage_constructor_exp_def)
    .
  unfolding var_constructor_exp_def append_exp_def by auto
termination
  apply standard
  unfolding append_exp_def
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  apply (rule mlex_less, force)+
  done

lemma eval_exp_true[simp]: \<open>eval_exp \<Delta> true = true\<close>
  by (simp add: true_exp_def)

lemma eval_exp_false[simp]: \<open>eval_exp \<Delta> false = false\<close>
  by (simp add: false_exp_def)

lemma eval_exp_word[simp]: \<open>eval_exp \<Delta> (num \<Colon> sz) = (num \<Colon> sz)\<close>
  by (simp add: word_constructor_exp_def)

lemma eval_exp_unknown[simp]: \<open>eval_exp \<Delta> (unknown[str]: t) = (unknown[str]: t)\<close>
  by (simp add: unknown_constructor_exp_def)

lemma eval_exp_storage[simp]: \<open>eval_exp \<Delta> (v[w \<leftarrow> v', sz]) = (v[w \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def)

lemma eval_exp_val: \<open>v' = eval_exp \<Delta> (Val v) \<Longrightarrow> v = v'\<close>
  by simp

function
  step_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto> _\<close> 401)
where
  \<open>(_ \<turnstile> (Val v) \<leadsto> _) = False\<close> |
  \<open>\<lbrakk>\<forall>v. e \<noteq> (Val v)\<rbrakk> \<Longrightarrow> (\<Delta> \<turnstile> e \<leadsto> e') = (
    e \<noteq> e' \<and>
    eval_exp \<Delta> e = eval_exp \<Delta> e'
  )\<close>
  subgoal for P x
    apply (cases x)
    subgoal for \<Delta> e\<^sub>1 e\<^sub>2
      apply (cases \<open>\<exists>v. e\<^sub>1 = (Val v)\<close>)
      by blast+
    .
  by auto
termination by (standard, auto)

lemmas var_simps = Immediate_simp Val_simp_word Val_simp_storage Val_simp_unknown

end