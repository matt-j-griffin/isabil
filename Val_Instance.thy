theory Val_Instance
  imports BIL_Syntax Bitvector_Instance
begin            
(*
class val = val_syntax + (* TODO *)
  assumes val_induct: \<open>\<And>Q v. \<lbrakk>\<And>num sz. Q (num \<Colon> sz); \<And>str t. Q (unknown[str]: t); 
                        \<And>mem w v' sz. Q (mem[w \<leftarrow> v', sz])\<rbrakk> \<Longrightarrow> Q v\<close>
      and val_exhaust[case_names Word Unknown Storage]: 
        \<open>\<And>Q v. \<lbrakk>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q; \<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q; 
                        \<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>

      and storage_v_size[simp]: \<open>\<And>v w v' sz. size_class.size v < size_class.size (v[w \<leftarrow> v', sz])\<close>
*)

instantiation val :: val_syntax
begin

definition
  word_constructor_val :: \<open>nat \<Rightarrow> nat \<Rightarrow> val\<close>
where
  \<open>(num \<Colon> sz) = (Immediate (num \<Colon> sz))\<close>

definition
  unknown_constructor_val :: \<open>string \<Rightarrow> Type \<Rightarrow> val\<close>
where
  \<open>(unknown[str]: sz) = Unknown str sz\<close>

definition
  storage_constructor_val :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> val\<close>
where
  \<open>(v[a \<leftarrow> v', sz]) = Storage v a v' sz\<close>
(*
definition 
  true_val :: val
where
  \<open>true_val = (Immediate true)\<close>

definition 
  false_val :: val
where
  \<open>false_val = (Immediate false)\<close>

lemma true_not_false_val[simp]: \<open>(true::val) \<noteq> false\<close>
  unfolding false_val_def true_val_def
  using not_true_eq_false by (metis val.inject(1))
*)
lemma valI:
  fixes v :: val
  assumes imm: \<open>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q\<close>
      and unk: \<open>\<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q\<close>
      and mem: \<open>\<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q\<close>
    shows Q
  apply (cases v rule: val.exhaust)
  subgoal for w 
    apply (cases w rule: word_exhaust)
    subgoal for num sz apply (rule imm[of num sz])
      by (simp add: word_constructor_val_def)
    .
  subgoal by (rule unk, unfold unknown_constructor_val_def)
  subgoal by (rule mem, unfold storage_constructor_val_def)
  .

function
  is_ok_val :: \<open>val \<Rightarrow> bool\<close>
where 
  \<open>is_ok_val (num \<Colon> sz) = ((num \<Colon> sz)::word) is ok\<close> |
  \<open>\<lbrakk>\<forall>num sz. x \<noteq> (num \<Colon> sz)\<rbrakk> \<Longrightarrow> is_ok_val x = False\<close>
  subgoal for P x
    by (rule valI, blast+)
  unfolding word_constructor_val_def
  by auto 
termination by lexicographic_order

function
  type_val :: \<open>val \<Rightarrow> Type\<close>
where
  \<open>type_val (num \<Colon> sz) = imm\<langle>sz\<rangle>\<close> |
  \<open>type_val (unknown[str]: t) = t\<close> |
  \<open>type_val (mem[(num \<Colon> sz\<^sub>1) \<leftarrow> v, sz\<^sub>2]) = mem\<langle>sz\<^sub>1, sz\<^sub>2\<rangle>\<close>
  subgoal for P x 
    apply (rule valI[of x])
    prefer 3 subgoal for mem w v' sz 
      apply (cases w rule: word_exhaust) 
      by simp
    by simp_all
  unfolding storage_constructor_val_def word_constructor_val_def unknown_constructor_val_def
  by simp_all
termination by lexicographic_order


function 
  typed_ok_val :: \<open>TypingContext \<Rightarrow> val \<Rightarrow> Type \<Rightarrow> bool\<close>
where
  \<open>typed_ok_val \<Gamma> (num \<Colon> sz) t = (((num \<Colon> sz)::word) is ok \<and> \<Gamma> is ok \<and> t = imm\<langle>sz\<rangle>)\<close> |
  \<open>typed_ok_val \<Gamma> (unknown[str]: t) t' = (t is ok \<and> \<Gamma> is ok \<and> t' = t)\<close> |
  \<open>typed_ok_val \<Gamma> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>v\<^sub>a\<^sub>l]) t = (((num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)::word) is ok \<and> sz\<^sub>v\<^sub>a\<^sub>l > 0 \<and>
     (\<Gamma> \<turnstile> v' :: imm\<langle>sz\<^sub>v\<^sub>a\<^sub>l\<rangle>) \<and> (\<Gamma> \<turnstile> v :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>v\<^sub>a\<^sub>l\<rangle>) \<and> t = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>v\<^sub>a\<^sub>l\<rangle>)\<close> |
  \<open>\<lbrakk>
     (\<forall>num sz. v \<noteq> (num \<Colon> sz)) \<and> (\<forall>str t'. v \<noteq> (unknown[str]: t')) \<and>
     (\<forall>mem num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz\<^sub>v\<^sub>a\<^sub>l. v \<noteq> (mem[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>v\<^sub>a\<^sub>l]))
   \<rbrakk> \<Longrightarrow> typed_ok_val _ v t = False\<close>  
  subgoal for P x
    apply (rule prod_cases3[of x])
    apply auto
    subgoal for a b c
      apply (case_tac b, auto)
      by blast+
    .
  unfolding storage_constructor_val_def word_constructor_val_def unknown_constructor_val_def
  apply (simp_all del: is_ok_word.simps)
  by blast+

termination
  apply standard
  apply (relation \<open>(\<lambda>p. size (fst (snd p))) <*mlex*> {}\<close>)
  apply (simp_all add: wf_mlex)
  unfolding storage_constructor_val_def
  by (rule mlex_less, auto)+

instance proof
  fix v :: val
    and t :: Type
    and t' :: Type
  assume type: "type v = t" "type v = t'"
  show "t' = t"
    apply (rule valI[where v = v])
    using type by auto
next
  fix \<Gamma> :: "Var.var list"
    and v :: val
    and t :: Type
  assume typed: "\<Gamma> \<turnstile> v :: t"
  show "t is ok"
    apply (rule valI[where v = v])
    using typed apply auto
    subgoal for _ w
      apply (cases w, auto)
      unfolding word_constructor_val_def[symmetric] word_constructor_word_def[symmetric] by auto
    done
next
  fix nat :: nat
    and sz :: nat
    and nat' :: nat
    and sz' :: nat
  show "(nat \<Colon> sz::val) = nat' \<Colon> sz' \<equiv> nat = nat' \<and> sz = sz'"
    unfolding word_constructor_val_def by auto
next
  fix mem mem' :: val
    and w w' :: word
    and v v' :: val
    and sz sz' :: nat
  show "(((mem[w \<leftarrow> v, sz])::val) = (mem'[w' \<leftarrow> v', sz'])) = (mem = mem' \<and> w = w' \<and> v = v' \<and> sz = sz')"
    unfolding storage_constructor_val_def by auto
next
  fix str :: "char list"
    and str' :: "char list"
    and t :: Type
    and t' :: Type
  show "((unknown[str]: t::val) = unknown[str']: t') = (str = str' \<and> t = t')"
    unfolding unknown_constructor_val_def by auto
next
  fix v :: val
    and w :: word
    and v' :: val
    and sz :: nat
    and num :: nat
    and sz' :: nat
  show "v[w \<leftarrow> v', sz] \<noteq> (num \<Colon> sz'::val)"
    unfolding storage_constructor_val_def word_constructor_val_def by auto
next
  fix v :: val
    and w :: word
    and v' :: val
    and sz :: nat
    and str :: "char list"
    and t :: Type
  show "v[w \<leftarrow> v', sz] \<noteq> (unknown[str]: t::val)"
    unfolding storage_constructor_val_def unknown_constructor_val_def by auto
next
  fix str :: "char list"
    and t :: Type
    and num :: nat
    and sz :: nat
  show "(num \<Colon> sz::val) \<noteq> unknown[str]: t"
    unfolding word_constructor_val_def unknown_constructor_val_def by auto
qed auto

end

lemma val_induct[case_names Word Unknown Storage]: 
  fixes v :: val
  assumes Word: \<open>\<And>num sz. Q (num \<Colon> sz)\<close> 
      and Unknown: \<open>\<And>str t. Q (unknown[str]: t)\<close>
      and Storage: \<open>\<And>mem w v' sz. Q mem \<Longrightarrow> Q (mem[w \<leftarrow> v', sz])\<close>  
  shows \<open>Q v\<close>
proof (rule val.induct)
  fix x show "Q (Immediate x)"
  proof (cases x rule: word_exhaust)
    case w: (Word num sz)
    show ?thesis 
      unfolding w word_constructor_val_def[symmetric] by (rule Word)
  qed
next
  fix str t show "Q (Unknown str t)"
    unfolding unknown_constructor_val_def[symmetric] by (rule Unknown)
next
  fix x1a :: val and x2 :: word and x3 :: val and x4 :: nat
  assume mem: "Q x1a" (*and "Q x3"*)
  thus "Q (Storage x1a x2 x3 x4)"
    unfolding storage_constructor_val_def[symmetric] by (rule Storage)
qed

lemma val_exhaust[case_names Word Unknown Storage]: 
  fixes v :: val
  shows \<open>\<lbrakk>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q; \<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q; 
                        \<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>
proof -
  assume word: "\<And>num sz. v = num \<Colon> sz \<Longrightarrow> Q"
    and "\<And>str t. v = unknown[str]: t \<Longrightarrow> Q"
    and "\<And>mem w v' sz. v = mem[w \<leftarrow> v', sz] \<Longrightarrow> Q"
  thus Q
  unfolding unknown_constructor_val_def storage_constructor_val_def
  proof (cases v)
    case (Immediate w)
    then show ?thesis 
      using word apply (cases w rule: word_exhaust, auto)
      unfolding word_constructor_val_def[symmetric] by auto
  qed auto
qed

lemma storage_v_size[simp]: 
  fixes v :: val
    and w :: word
    and v' :: val
    and sz :: nat
    shows \<open>size_class.size v < size_class.size ((v[w \<leftarrow> v', sz])::val)\<close>
proof -
  show "size v < size ((v[w \<leftarrow> v', sz])::val)"
    unfolding storage_constructor_val_def by auto
qed


lemmas Immediate_simp[simp] = word_constructor_val_def[symmetric]

lemma storage_not_nested_val[simp]: \<open>v[num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz] \<noteq> v\<close>
  unfolding storage_constructor_val_def by simp

end