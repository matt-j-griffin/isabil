
section \<open>Syntax\<close>

theory Expression_Syntax
  imports "../Val_Instance" (*TODO*)
          "../Formula_Syntax"
begin

text \<open>Some evaluation rules depend on the type of a value. Since there are two canonical forms for
each type, we avoid duplicating each rule by defining the following metafunction:\<close>

context val_syntax
begin

function
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

end

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

declare eval_exp.simps[simp del]

lemma eval_exp_true[simp]: \<open>eval_exp \<Delta> true = true\<close>
  by (simp add: true_exp_def eval_exp.simps)

lemma eval_exp_false[simp]: \<open>eval_exp \<Delta> false = false\<close>
  by (simp add: false_exp_def eval_exp.simps)

lemma eval_exp_word[simp]: \<open>eval_exp \<Delta> (num \<Colon> sz) = (num \<Colon> sz)\<close>
  by (simp add: word_constructor_exp_def eval_exp.simps)

lemma eval_exp_unknown[simp]: \<open>eval_exp \<Delta> (unknown[str]: t) = (unknown[str]: t)\<close>
  by (simp add: unknown_constructor_exp_def eval_exp.simps)

lemma eval_exp_storage[simp]: \<open>eval_exp \<Delta> (v[w \<leftarrow> v', sz]) = (v[w \<leftarrow> v', sz])\<close>
  by (simp add: storage_constructor_exp_def eval_exp.simps)

lemma eval_exp_val: \<open>v' = eval_exp \<Delta> (Val v) \<Longrightarrow> v = v'\<close>
  unfolding eval_exp.simps by simp

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


fun
  eval_exps_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close>)
where
  \<open>(\<Delta> \<turnstile> e \<leadsto>* v) = (v = eval_exp \<Delta> e)\<close>


inductive
  eval_exp' :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<Rrightarrow> _\<close> [400, 400, 400] 401)
where
  \<comment> \<open>Var rules\<close>
  VarIn: \<open>\<lbrakk>((name' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> Val val\<close> |
  VarNotIn: \<open>\<lbrakk>((name' :\<^sub>t t)) \<notin> dom \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> unknown[str]: t\<close> |

  \<comment> \<open>Load\<close>
  LoadStepAddr: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'; e\<^sub>2 \<noteq> e\<^sub>2'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<Rrightarrow> (e\<^sub>1[e\<^sub>2', ed]:usz)\<close> |
  LoadStepMem: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'; e\<^sub>1 \<noteq> e\<^sub>1'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<Rrightarrow> (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close> |
  LoadByte: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> Val v'\<close> | 
  LoadByteFromNext: \<open>\<lbrakk>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ((v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<Rrightarrow> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<close> |
  LoadUnMem: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<Rrightarrow> unknown[str]: imm\<langle>sz\<rangle>\<close> |
  LoadUnAddr: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<Rrightarrow> unknown[str]: imm\<langle>sz'\<rangle>\<close> |
  LoadWordBe: \<open>\<lbrakk>sz > sz\<^sub>m\<^sub>e\<^sub>m; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> |
  LoadWordEl: \<open>\<lbrakk>sz > sz\<^sub>m\<^sub>e\<^sub>m; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> |

  \<comment> \<open>Store\<close>
  StoreStepVal: \<open>\<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> |
  StoreStepAddr: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreStepMem: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreWordBe: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreWordEl: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreVal: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<Rrightarrow> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close> |
  StoreUnAddr: \<open>type v = t \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>, ed]:usz' \<leftarrow> (Val v')) \<Rrightarrow> (unknown[str]: t)\<close> |


  \<comment> \<open>Let rules\<close>
  LetStep: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<Rrightarrow> (Let var e\<^sub>1' e\<^sub>2)\<close> |
  Let: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<Rrightarrow> [v\<sslash>var]e\<close> |
  (* one missing rule *)

  \<comment> \<open>If rules\<close>
  IfStepCond: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<close> |
  IfStepThen: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<Rrightarrow> ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<close> |
  IfStepElse: \<open>\<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Rrightarrow> ite e\<^sub>1 e\<^sub>2 e\<^sub>3'\<close> |
  IfTrue: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> (Val v\<^sub>2)\<close> |
  IfFalse: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> (Val v\<^sub>3)\<close> |
  IfUnknown: \<open>\<lbrakk>type v\<^sub>2 = t'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> unknown[str]: t'\<close> |

  \<comment> \<open>Binary operation rules\<close>
  BopRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<Rrightarrow> BinOp (Val v) bop e\<^sub>2'\<close> |
  BopLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<Rrightarrow> BinOp e\<^sub>1' bop e\<^sub>2\<close> |

  AopUnkRhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e \<Rrightarrow> unknown[str]: t\<close> |
  AopUnkLhs: \<open>\<Delta> \<turnstile> BinOp e (AOp aop) (unknown[str]: t) \<Rrightarrow> unknown[str]: t\<close> |

  LopUnkRhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e \<Rrightarrow> unknown[str]: imm\<langle>1\<rangle>\<close> |
  LopUnkLhs: \<open>\<Delta> \<turnstile> BinOp e (LOp lop) (unknown[str]: t) \<Rrightarrow> unknown[str]: imm\<langle>1\<rangle>\<close> |

  \<comment> \<open>Arithmetic rules\<close>
  Plus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Minus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Times: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Div: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SDiv: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Mod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SMod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsl: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Asr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Logical rules\<close>
  LAnd: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  XOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  (*these aren't really right*)
  EqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<Rrightarrow> true\<close> |
  EqDiff: \<open>((num\<^sub>1 \<Colon> sz)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> false\<close> |
  NeqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<Rrightarrow> false\<close> |
  NeqDiff: \<open>((num\<^sub>1 \<Colon> sz)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz)) (LOp Neq) (num\<^sub>2 \<Colon> sz) \<Rrightarrow> true\<close> |
  Less: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLess: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Unary op\<close>
  Uop: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (UnOp uop e) \<Rrightarrow> (UnOp uop e')\<close> |
  UopUnk: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<Rrightarrow> (unknown[str]: t)\<close> |
  Not: \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<Rrightarrow> (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |
  Neg: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<Rrightarrow> (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |

  \<comment> \<open>Concat\<close>
  ConcatRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<Rrightarrow> (e\<^sub>1 @ e\<^sub>2')\<close> |
  ConcatLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<Rrightarrow> (e\<^sub>1' @ (Val v\<^sub>2))\<close> |
  ConcatRhsUn: \<open>type v = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  ConcatLhsUn: \<open>type v = imm\<langle>sz\<^sub>2\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  Concat: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |

  \<comment> \<open>Extract\<close>
  Extract: \<open>sz\<^sub>2 \<le> sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<Rrightarrow> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)\<close> |
  ExtractReduce: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Rrightarrow> (extract:sz\<^sub>1:sz\<^sub>2[e'])\<close> |
  ExtractUn: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<Rrightarrow> (unknown[str]: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>)\<close> |

  \<comment> \<open>Cast\<close>
  CastReduce: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz e) \<Rrightarrow> (Cast cast sz e')\<close> |
  CastUnk: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<rangle>)\<close> |
  CastLow: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastHigh: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))\<close> |
  CastSigned: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastUnsigned: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>

inductive_cases VarE: \<open>\<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> e\<close>

inductive_cases LoadStepAddrE: \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<Rrightarrow> e\<close>
inductive_cases LoadStepMemE: \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<Rrightarrow> e\<close>
inductive_cases LoadByteE: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> e\<close> 
inductive_cases LoadByteFromNextE: \<open>\<Delta> \<turnstile> ((v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<Rrightarrow> e\<close>
inductive_cases LoadUnMemE: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<Rrightarrow> e\<close> 
inductive_cases LoadUnAddrE: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<Rrightarrow> e\<close> 
inductive_cases LoadWordBeE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> e\<close>
inductive_cases LoadWordElE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> e\<close>

inductive_cases StoreStepValE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> e\<close>
inductive_cases StoreStepAddrE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases StoreStepMemE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases StoreWordBeE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<Rrightarrow> e\<close>
inductive_cases StoreWordElE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<Rrightarrow> e\<close>
inductive_cases StoreValE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<Rrightarrow> e\<close>
inductive_cases StoreUnAddrE: \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle>, ed]:usz' \<leftarrow> (Val v')) \<Rrightarrow> e\<close>

inductive_cases IfStepCondE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfStepThenE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfStepElseE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Rrightarrow> e\<close>
inductive_cases IfTrueE: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfFalseE: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfUnknownE: \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>

inductive_cases LetStepE: \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<Rrightarrow> e\<close>
inductive_cases LetE: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<Rrightarrow> e'\<close>

inductive_cases BopRhsE: \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<Rrightarrow> e\<close>
inductive_cases BopLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<Rrightarrow> e\<close>
inductive_cases AOpE: \<open>\<Delta> \<turnstile> (BinOp e\<^sub>1 (AOp aop) e\<^sub>2) \<Rrightarrow> e'\<close>

inductive_cases PlusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases MinusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases TimesE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases DivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SDivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases ModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LslE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases AsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LAndE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases XOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases EqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases EqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz) (LOp Eq) (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases NeqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases NeqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz)) (LOp Neq) (num\<^sub>2 \<Colon> sz) \<Rrightarrow> e\<close>
inductive_cases LessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SignedLessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SignedLessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases UopE: \<open>\<Delta> \<turnstile> (UnOp uop e) \<Rrightarrow> e'\<close>
inductive_cases UopUnkE: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<Rrightarrow> e\<close>
inductive_cases NotE: \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases NegE: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases ConcatRhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<Rrightarrow> e\<close>
inductive_cases ConcatLhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<Rrightarrow> e\<close>
inductive_cases ConcatRhsUnE: \<open>\<Delta> \<turnstile> ((Val v) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<Rrightarrow> e\<close>
inductive_cases ConcatLhsUnE: \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<Rrightarrow> e\<close>
inductive_cases ConcatE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close>
inductive_cases ExtractE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<Rrightarrow> e\<close>
inductive_cases ExtractReduceE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Rrightarrow> e'\<close>
inductive_cases ExtractUnE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<Rrightarrow> e\<close>
inductive_cases CastReduceE: \<open>\<Delta> \<turnstile> (Cast cast sz e) \<Rrightarrow> e'\<close>
inductive_cases CastUnkE: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<Rrightarrow> e\<close>
inductive_cases CastLowE: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastHighE: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastSignedE: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastUnsignedE: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>

lemma Val_not_inject: "v \<noteq> v' \<Longrightarrow> Val v \<noteq> Val v'"
  by simp

lemma storage_not_nested_val[intro]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>1 \<leftarrow> v', sz] \<noteq> v\<close>
  unfolding storage_constructor_val_def by simp

lemma storage_not_val[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>1 \<leftarrow> v', sz] \<noteq> Val v\<close>
  unfolding storage_constructor_exp_def
  apply (rule Val_not_inject)
  by (rule storage_not_nested_val)

lemma step_exp_neq': \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> e \<noteq> e'\<close>
proof (induct rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  then show ?case 
    using var.not_val by blast
next
  case (VarNotIn name' t \<Delta> str)
  then show ?case by simp
next
  case (Plus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding plus_exp.simps bv_plus.simps by simp
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by simp
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by simp
next
  case (Extract sz\<^sub>2 sz\<^sub>1 \<Delta> num sz)
  then show ?case
    unfolding xtract.simps by simp
next
  case (CastLow \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastHigh \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastSigned \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastUnsigned \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (Let \<Delta> var v e)
  then show ?case 
    apply (induct e, auto)
    apply (drule capture_val, elim disjE)
    apply simp_all
    sledgehammer
    sorry
next
qed simp_all

lemma step_exp_neq: \<open>\<not>(\<Delta> \<turnstile> e \<Rrightarrow> e)\<close>
  using step_exp_neq' by auto

lemma eval_exp'_val_no_step_intermediary: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> e \<noteq> (Val v)\<close>
  by (induct rule: eval_exp'.induct, simp_all)

lemma step_exp_not_val[simp]: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<Rrightarrow> e)\<close>
  using eval_exp'_val_no_step_intermediary by blast

lemma step_exp_not_word[simp]: \<open>\<not>(\<Delta> \<turnstile> (num \<Colon> sz) \<Rrightarrow> e)\<close>
  unfolding word_constructor_exp_def by (rule step_exp_not_val)

lemma step_exp_not_unknown[simp]: \<open>\<not>(\<Delta> \<turnstile> (unknown[str]: t) \<Rrightarrow> e)\<close>
  unfolding unknown_constructor_exp_def by (rule step_exp_not_val)

lemma step_exp_not_true[simp]: \<open>\<not>(\<Delta> \<turnstile> true \<Rrightarrow> e)\<close>
  unfolding true_exp_def by (rule step_exp_not_val)

lemma step_exp_not_false[simp]: \<open>\<not>(\<Delta> \<turnstile> false \<Rrightarrow> e)\<close>
  unfolding false_exp_def by (rule step_exp_not_val)

lemma step_exp_not_storage[simp]: \<open>\<not>(\<Delta> \<turnstile> v[w \<leftarrow> v', sz] \<Rrightarrow> e')\<close>
  unfolding storage_constructor_exp_def by (rule step_exp_not_val)


text \<open>We describe a well formed delta as one which\<close>

definition
  wf\<Delta> :: \<open>variables \<Rightarrow> bool\<close>
where
  \<open>wf\<Delta> \<Delta> = (\<forall>var \<in> dom \<Delta>. var_type var = type (the (\<Delta> var)))\<close>


function
  no_unknowns :: \<open>variables \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>no_unknowns _ (unknown[_]: _) = False\<close> |
  \<open>no_unknowns _ (_ \<Colon> _) = True\<close> |
  \<open>no_unknowns _ (_[_ \<leftarrow> _, _]) = True\<close> |
  \<open>no_unknowns \<Delta> (name' :\<^sub>t t) = ((name' :\<^sub>t t) \<in> dom \<Delta> \<and> (\<forall>str t. the (\<Delta> (name' :\<^sub>t t)) \<noteq> unknown[str]: t))\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1[e\<^sub>2, _]:u_) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1 with [e\<^sub>2, _]:u_ \<leftarrow> e\<^sub>3) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2 \<and> no_unknowns \<Delta> e\<^sub>3)\<close> |
  \<open>no_unknowns \<Delta> (BinOp e\<^sub>1 _ e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (UnOp _ e) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (Cast _ _ e) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (Let _ e\<^sub>1 e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2 \<and> no_unknowns \<Delta> e\<^sub>3)\<close> |
  \<open>no_unknowns \<Delta> (extract:_:_[e]) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1 @ e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close>
  subgoal for P x
    apply (cases x, simp)
    subgoal for \<Delta> e
      by (cases e rule: exp_exhaust, auto)
    .
  apply auto
  apply (metis var_not_unknown_neq)
  apply (metis concat_not_unknown_neq)
  apply (metis var_not_word_neq)
  apply (metis var_not_word_neq)
  apply (metis concat_not_word_neq)
  apply (metis concat_not_word_neq)
  apply (metis var_not_storage_neq)
  apply (metis var_not_storage_neq)
  apply (metis concat_not_storage_neq)+
  done
termination 
  apply standard
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  unfolding append_exp_def
  by (rule mlex_less, force)+

lemma no_unknowns_ext[simp]: \<open>no_unknowns \<Delta> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w)\<close>
  unfolding xtract.simps by simp

lemma no_unknowns_succ[simp]: \<open>no_unknowns \<Delta> (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
  unfolding succ.simps by simp

lemma no_unknowns_true[simp]: \<open>no_unknowns \<Delta> true\<close>
  by (simp add: true_word)

lemma no_unknowns_false[simp]: \<open>no_unknowns \<Delta> false\<close>
  by (simp add: false_word)

lemma no_unknowns_Val[intro]: \<open>\<forall>str t. val \<noteq> unknown[str]: t \<Longrightarrow> no_unknowns \<Delta> (Val val)\<close>
  apply (cases val rule: val_exhaust)
  apply auto
  unfolding Val_simp_word Val_simp_storage by simp_all

lemma step_exp_no_unknowns:
  assumes \<open>\<Delta> \<turnstile> e \<Rrightarrow> e'\<close> and \<open>wf\<Delta> \<Delta>\<close> and \<open>no_unknowns \<Delta> e\<close>
    shows \<open>no_unknowns \<Delta> e'\<close>
using assms proof (induction rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  then show ?case 
    apply auto
    apply (rule no_unknowns_Val)
    apply auto
    subgoal for y str t'
      apply (erule allE[of _ str], erule allE[of _ t])
      unfolding val_var_in_vars.simps wf\<Delta>_def 
      by (metis val_syntax_class.type_unknownI var.sel(2) var_constructor_var_def)
    .
next
  case (LoadByte \<Delta> v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz ed)
  then show ?case 
    apply auto
    sorry
next
  case (LoadByteFromNext num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  then show ?case 
    apply auto
    sorry
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by auto
next
  case (SignedLess \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_le.simps bv_land.simps bv_eq_def by auto
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_le.simps bv_land.simps bv_eq_def by auto
qed (unfold no_unknowns.simps, simp_all)


lemma eval_exp'_deterministic:
  assumes \<open>\<Delta> \<turnstile> e \<Rrightarrow> e\<^sub>1\<close> and \<open>\<Delta> \<turnstile> e \<Rrightarrow> e\<^sub>2\<close>
    shows \<open>e\<^sub>1 = e\<^sub>2\<close>
using assms proof (induction arbitrary: e\<^sub>2 rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  show ?case 
    using VarIn(2) apply (rule VarE, simp_all)
    using VarIn.hyps apply (rule var_in_deterministic, blast)
    using VarIn.hyps val_var_in_vars.simps by blast
next
  case (VarNotIn name' t \<Delta> str)
  show ?case 
    using VarNotIn(2) apply (rule VarE, simp_all)
    using VarNotIn.hyps apply (simp add: val_var_in_vars.simps)
    subgoal sorry
    .
next
  case (LoadStepAddr \<Delta> e\<^sub>2' e\<^sub>2'' e\<^sub>1 ed sz)
  show ?case 
    using LoadStepAddr(4) apply (rule LoadStepAddrE)
    using LoadStepAddr.hyps apply auto
    by (rule LoadStepAddr.IH)
next
  case (LoadStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 ed sz)
  show ?case 
    using LoadStepMem(4) apply (rule LoadStepMemE)
    using LoadStepMem.hyps apply auto
    by (rule LoadStepMem.IH)
next
  case (LoadByte \<Delta> v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz ed)
  then show ?case 
    apply (rule LoadByteE, auto)
    apply (simp_all add: storage_constructor_exp_def)
    by fastforce+
next
  case (LoadByteFromNext num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  show ?case 
    using LoadByteFromNext(2) apply (rule LoadByteFromNextE)
    using LoadByteFromNext.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    by fastforce+
next
  case (LoadUnMem \<Delta> str t v ed sz)
  then show ?case 
    apply (rule LoadUnMemE)
    apply auto
    sorry
next
  case (LoadUnAddr \<Delta> v w v' sz str t ed sz')
  then show ?case 
    apply (rule LoadUnAddrE)
    by auto
next
  case (LoadWordBe sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    using LoadWordBe(3) apply (rule LoadWordBeE)
    using LoadWordBe.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    sorry
next
  case (LoadWordEl sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    using LoadWordEl(3) apply (rule LoadWordElE)
    using LoadWordEl.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    sorry
next
  case (StoreStepVal \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2 en sz)
  show ?case 
    using StoreStepVal(3) apply (rule StoreStepValE)
    using StoreStepVal.hyps apply auto
    by (rule StoreStepVal.IH) 
next
  case (StoreStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 en sz v\<^sub>3)
  show ?case 
    using StoreStepAddr(3) apply (rule StoreStepAddrE)
    using StoreStepAddr.hyps apply auto
    by (rule StoreStepAddr.IH) 
next
  case (StoreStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 en sz v\<^sub>3)
  show ?case 
    using StoreStepMem(3) apply (rule StoreStepMemE)
    using StoreStepMem.hyps apply auto
    by (rule StoreStepMem.IH) 
next
  case (StoreWordBe sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    using StoreWordBe(4) apply (rule StoreWordBeE)
    using StoreWordBe.hyps by auto
next
  case (StoreWordEl sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    using StoreWordEl(4) apply (rule StoreWordElE)
    using StoreWordEl.hyps by auto
next
  case (StoreVal v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m \<Delta> num ed v')
  show ?case 
    using StoreVal(2) apply (rule StoreValE)
    using StoreVal.hyps by auto
next
  case (StoreUnAddr v t \<Delta> str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r ed sz' v')
  show ?case 
    using StoreUnAddr(2) apply (rule StoreUnAddrE)
    using StoreUnAddr.hyps by auto
next
  case (LetStep \<Delta> e\<^sub>1 e\<^sub>1' var e\<^sub>2)
  show ?case 
    using LetStep(3) apply (rule LetStepE)
    using LetStep.hyps apply auto
    by (rule LetStep.IH) 
next
  case (IfStepCond \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 v\<^sub>3)
  show ?case 
    using IfStepCond(3) apply (rule IfStepCondE)
    using IfStepCond.hyps apply auto
    by (rule IfStepCond.IH) 
next
  case (IfStepThen \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 v\<^sub>3)
  show ?case 
    using IfStepThen(3) apply (rule IfStepThenE)
    using IfStepThen.hyps apply auto
    by (rule IfStepThen.IH) 
next
  case (IfStepElse \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2)
  show ?case 
    using IfStepElse(3) apply (rule IfStepElseE)
    using IfStepElse.hyps apply auto
    by (rule IfStepElse.IH) 
next
  case (IfTrue \<Delta> v\<^sub>2 v\<^sub>3)
  then show ?case
    apply (rule IfTrueE)
    apply auto
    using unknown_not_true by metis    
next
  case (IfFalse \<Delta> v\<^sub>2 v\<^sub>3)
  then show ?case 
    apply (rule IfFalseE)
    apply auto
    using unknown_not_false by metis
next
  case (IfUnknown v\<^sub>2 t' \<Delta> str t v\<^sub>3)
  show ?case 
    using IfUnknown(2) apply (rule IfUnknownE)
    using IfUnknown.hyps by auto
next
  case (BopRhs \<Delta> e\<^sub>2' e\<^sub>2'' v bop)
  show ?case 
    using BopRhs(3) apply (rule BopRhsE)
    using BopRhs.hyps apply auto
    apply (rule BopRhs.IH, blast)
    sorry
next
  case (BopLhs \<Delta> e\<^sub>1 e\<^sub>1' bop e\<^sub>2')
  show ?case 
    using BopLhs(3) apply (rule BopLhsE)
    using BopLhs.hyps apply auto
    apply (rule BopLhs.IH, blast)
    sorry
next
  case (AopUnkRhs \<Delta> str t aop e)
  then show ?case sorry
next
  case (AopUnkLhs \<Delta> e aop str t)
  then show ?case sorry
next
  case (LopUnkRhs \<Delta> str t lop e)
  then show ?case sorry
next
  case (LopUnkLhs \<Delta> e lop str t)
  then show ?case sorry
next
  case (Plus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule PlusE)
    by auto
next
  case (Minus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule MinusE)
    by auto
next
  case (Times \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule TimesE)
    by auto
next
  case (Div \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule DivE)
    by auto
next
  case (SDiv \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SDivE)
    by auto
next
  case (Mod \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule ModE)
    by auto
next
  case (SMod \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SModE)
    by auto    
next
  case (Lsl \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LslE)
    by auto
next
  case (Lsr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LsrE)
    by auto
next
  case (Asr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule AsrE)
    by auto
next
  case (LAnd \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LAndE)
    by auto
next
  case (LOr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case
    apply (rule LOrE)
    by auto
next
  case (XOr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule XOrE)
    by auto
next
  case (EqSame \<Delta> num sz)
  then show ?case 
    apply (rule EqSameE)
    apply auto    
    by (simp add: bv_eq_def)
next
  case (EqDiff num\<^sub>1 sz num\<^sub>2 \<Delta>)
  show ?case 
    using EqDiff(2) apply (rule EqDiffE)
    apply auto
    by (metis EqDiff.hyps bv_eq_def bv_negation_true_false true_neq_false_word)
next
  case (NeqSame \<Delta> num sz)
  then show ?case 
    apply (rule NeqSameE)
    apply auto
    by (simp add: bv_eq_def)
next
  case (NeqDiff num\<^sub>1 sz num\<^sub>2 \<Delta>)
  show ?case 
    using NeqDiff(2) apply (rule NeqDiffE)
    apply auto
    by (metis NeqDiff.hyps bv_eq_def bv_negation_true_false true_neq_false_word)
next
  case (Less \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LessE)
    by auto
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LessEqE)
    by auto
next
  case (SignedLess \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SignedLessE)
    by auto
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SignedLessEqE)
    by auto
next
  case (Uop \<Delta> e e' uop)
  show ?case
    using Uop(3) apply (rule UopE)
    using Uop.hyps apply auto
    by (rule Uop.IH) 
next
  case (UopUnk \<Delta> uop str t)
  then show ?case 
    apply (rule UopUnkE)
    by auto    
next
  case (Not \<Delta> num sz)
  then show ?case
    apply (rule NotE)
    by auto
next
  case (Neg \<Delta> num sz)
  then show ?case 
    apply (rule NegE)
    by auto
next
  case (ConcatRhs \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1)
  show ?case 
    using ConcatRhs(3) apply (rule ConcatRhsE)
    using ConcatRhs.hyps apply auto
    apply (metis var_not_concat)
    apply (metis var_not_concat)
    by (rule ConcatRhs.IH)
next
  case (ConcatLhs \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2)
  show ?case 
    using ConcatLhs(3) apply (rule ConcatLhsE)
    using ConcatLhs.hyps apply auto
    apply (metis var_not_concat)
    apply (metis var_not_concat)
    by (rule ConcatLhs.IH)
next
  case (ConcatRhsUn v sz\<^sub>1 \<Delta> str sz\<^sub>2)
  show ?case 
    using ConcatRhsUn(2) apply (rule ConcatRhsUnE)
    using ConcatRhsUn.hyps apply auto
    apply (metis var_not_concat)+
    defer
    using unknown_constructor_exp_def apply fastforce
    sorry
next
  case (ConcatLhsUn v sz\<^sub>2 \<Delta> str sz\<^sub>1)
  show ?case 
    using ConcatLhsUn(2) apply (rule ConcatLhsUnE)
    using ConcatLhsUn.hyps apply auto
    apply (metis var_not_concat)+
    defer
    using unknown_constructor_exp_def apply fastforce
    sorry    
next
  case (Concat \<Delta> num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2)
  then show ?case 
    apply (rule ConcatE)
    apply auto
    apply (metis var_not_concat)
    by (metis var_not_concat)
next
  case (Extract sz\<^sub>2 sz\<^sub>1 \<Delta> num sz)
  show ?case 
    using Extract(2) apply (rule ExtractE)
    using Extract.hyps by auto
next
  case (ExtractReduce \<Delta> e e' sz\<^sub>1 sz\<^sub>2)
  show ?case 
    using ExtractReduce(3) apply (rule ExtractReduceE)
    using ExtractReduce.hyps apply auto
    by (rule ExtractReduce.IH)
next
  case (ExtractUn \<Delta> sz\<^sub>1 sz\<^sub>2 str t)
  then show ?case 
    apply (rule ExtractUnE)
    by auto
next
  case (CastReduce \<Delta> e e' cast sz)
  show ?case 
    using CastReduce(3) apply (rule CastReduceE)
    using CastReduce.hyps apply auto
    by (rule CastReduce.IH)
next
  case (CastUnk \<Delta> e e' cast sz str t)
  show ?case 
    using CastUnk(3) apply (rule CastUnkE)
    using CastUnk.hyps
    by auto
next
  case (CastLow \<Delta> sz num sz')
  then show ?case
    apply (rule CastLowE)
    by auto
next
  case (CastHigh \<Delta> sz num sz')
  then show ?case 
    apply (rule CastHighE)
    by auto
next
  case (CastSigned \<Delta> sz num sz')
  then show ?case 
    apply (rule CastSignedE)
    by auto
next
  case (CastUnsigned \<Delta> sz num sz')
  then show ?case 
    apply (rule CastUnsignedE)
    by auto
qed


declare bv_plus.simps[simp del]
declare plus_exp.simps[simp del]


end