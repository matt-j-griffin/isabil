theory Mem16_Intros
  imports Mem16 
          IsaBIL.Program_Intros
          IsaBIL.Expressions_Elims
begin

(** TODO **)
lemma storage16_nat_simps[simp, exp_cast_simps]: 
    \<open>16 - 1 = (15::nat)\<close> \<open>16 - 8 = (8::nat)\<close> \<open>15 - 8 = (7::nat)\<close>
    \<open>8 - 1 = (7::nat)\<close> \<open>Suc 7 = 8\<close>
  by auto (* after performing a store, attempt to unfold some nats *)

(** TODO **)
lemma storage64_nat_simps[simp, exp_cast_simps]: 
    \<open>64 - 56 = (8::nat)\<close> \<open>56 - 48 = (8::nat)\<close> \<open>48 - 40 = (8::nat)\<close> \<open>40 - 32 = (8::nat)\<close>
    \<open>63 - 8 = (55::nat)\<close> \<open>55 - 8 = (47::nat)\<close> \<open>47 - 8 = (39::nat)\<close> \<open>39 - 8 = (31::nat)\<close>
    \<open>64 - 1 = (63::nat)\<close> \<open>56 - 1 = (55::nat)\<close> \<open>48 - 1 = (47::nat)\<close> \<open>40 - 1 = (39::nat)\<close>
    \<open>Suc 55 = 56\<close> \<open>Suc 47 = 48\<close> \<open>Suc 39 = 40\<close> \<open>Suc 31 = 32\<close>
  by auto (* after performing a store, attempt to unfold some nats *)


\<comment> \<open>Little Endian\<close>

lemma step_exp_concat_word16_elI: \<open>\<Delta> \<turnstile> ((
            ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright>
            ext num \<Colon> sz \<sim> hi :  7 \<sim> lo : 0) \<leadsto> (ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 0)\<close>  
  apply (unfold xtract16_8_0[symmetric])
  by solve_expI

lemma step_exps_concat_word16_elI: \<open>\<Delta> \<turnstile> ((
            ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 8) \<copyright>
            ext num \<Colon> sz \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* (ext num \<Colon> sz \<sim> hi : 15 \<sim> lo : 0)\<close>  
  apply (unfold xtract16_8_0[symmetric])
  by solve_expsI

interpretation step_exps_concat_word16_elI: exp_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1.
    (\<And>\<Delta>. \<Delta> \<turnstile> ((ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 8) \<copyright> ext e\<^sub>1 \<sim> hi :  7 \<sim> lo : 0) \<leadsto>* 
          (ext e\<^sub>1 \<sim> hi : 15 \<sim> lo : 0))\<close>
  apply unfold_locales
  using step_exps_concat_word16_elI by blast


lemma step_exps_load_byte1_16_elI:
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u8 
                     \<leadsto>* ext (num \<Colon> sz) \<sim> hi : 7 \<sim> lo : 0\<close>
  unfolding storage_el16_def by (solve_expsI add: assms)

interpretation step_exps_load_byte1_16_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 0 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 7 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_byte1_16_elI by blast

lemma step_exps_load_byte2_16_elI:
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num \<Colon> sz))[succ (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u8 
                     \<leadsto>* ext (num \<Colon> sz) \<sim> hi : 15 \<sim> lo : 8\<close>
  using assms unfolding storage_el16_def apply -
  by solve_expsI

interpretation step_exps_load_byte2_16_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 0 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v w\<^sub>1 v\<^sub>2)[succ e\<^sub>1, el]:u8 \<leadsto>* ext e\<^sub>2 \<sim> hi : 15 \<sim> lo : 8)\<close>
  apply unfold_locales
  using step_exps_load_byte2_16_elI by blast

lemma step_exps_load_word16_elI:
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 
                        \<leadsto>* (ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 0)\<close>
  using assms unfolding storage_el16_def apply -
  by (solve_expsI add: step_exps_concat_word16_elI)

interpretation step_exps_load_word16_elI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 0 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, el]:u16 \<leadsto>* ext e\<^sub>2 \<sim> hi : 15 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_word16_elI by blast

lemmas step_exps_load_word16_el16I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 16, simplified]
lemmas step_exps_load_word16_el32I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 32, simplified]
lemmas step_exps_load_word16_el64I = step_exps_load_word16_elI[where sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r = 64, simplified]

lemma step_exps_load_next_byte16I: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
  unfolding storage_el16_def apply -
  by (solve_expsI add: nxt neq)

interpretation step_exps_load_next_byte16I: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk> 
          \<Longrightarrow> \<Delta> \<turnstile> (storage_el16 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte16I by blast 

(*
lemma step_exps_rtranclp_detD:
  assumes steps: "\<Delta> \<turnstile> a \<leadsto>* c" and caveat: "a \<noteq> c"
      and step: "\<Delta> \<turnstile> a \<leadsto> b" and unks: \<open>\<not> has_unknowns a\<close> \<open>\<not> has_unknowns b\<close> and npc: \<open>no_problem_children a\<close>
    shows "\<Delta> \<turnstile> b \<leadsto>* c"
  using steps apply (rule step_exps_converse_tranclpE)
  using caveat apply simp
  apply (drule step_exp_detD[OF step _ unks npc])
  by simp

lemma step_exps_rtranclpE':
  assumes steps: "\<Delta> \<turnstile> a \<leadsto>* c"
  obtains (step) b where "\<Delta> \<turnstile> a \<leadsto>* b" "\<Delta> \<turnstile> b \<leadsto>* c"
  using steps 
  using step_exps_reflI by presburger
*)

lemma inductTEST[consumes 1]:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto>* (Val v)\<close> \<open>\<forall>v. e \<noteq> Val v\<close>
      and Single: \<open>\<And>y. \<lbrakk>\<Delta> \<turnstile> y \<leadsto> Val v; \<forall>v. y \<noteq> Val v\<rbrakk> \<Longrightarrow> P y\<close>
      and Multiple: \<open>\<And>y z. \<lbrakk>\<Delta> \<turnstile> y \<leadsto> z; (step_exp \<Delta>)\<^sup>+\<^sup>+ z (Val v); \<forall>v. z \<noteq> Val v; P z\<rbrakk> \<Longrightarrow> P y\<close>
    shows \<open>P e\<close>
  using assms unfolding step_exps_def
  apply -
  apply (drule rtranclpD)
  apply (elim disjE conjE)
  apply simp
proof auto
  assume "(step_exp \<Delta>)\<^sup>+\<^sup>+ e (Val v)" "\<forall>v. e \<noteq> Val v"
  thus "P e"
  proof (induct rule: converse_tranclp_induct)
    case (base y)
    thus ?case by (rule Single)
  next
    case (step y z)
    have notz: \<open>\<forall>v. z \<noteq> Val v\<close>
      using step(2) apply auto 
      by (meson step_exp_valE.val tranclpD)
    note Pz = step(3)[OF notz]
    show ?case
      using step(1,2) notz Pz by (rule Multiple)
  qed
qed

fun 
  TTTT
where
  \<open>TTTT \<Delta> num sz (e' \<copyright> e) = (\<exists>num\<^sub>1 sz\<^sub>1. \<Delta> \<turnstile> e \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> \<Delta> \<turnstile> (e' \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* (num \<Colon> sz))\<close> |
  \<open>TTTT _ _ _ (_) = True\<close>

lemmas INDUCT[consumes 1] = inductTEST[where v = \<open>(_ \<Colon> _)\<close>, unfolded syntax_simps]

lemma GGGG:
  assumes \<open>\<Delta> \<turnstile> (e' \<copyright> e) \<leadsto>* (num \<Colon> sz)\<close>
  shows \<open>TTTT \<Delta> num sz (e' \<copyright> e)\<close>
using assms proof (induct rule: INDUCT)
  case 1
  then show ?case by simp
next
  case (2 y)
  then show ?case 
    apply (cases y)
    apply auto
    apply (erule step_exp_concat_rhsE)
    apply auto
    subgoal for num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2
      apply (rule exI[where x = num\<^sub>2])
      apply (rule exI[where x = sz\<^sub>2])
      apply (intro conjI)
      using step_exps_valsI(1) apply blast
      using step_exps_concatI.word.word by presburger
    .
next
  case (3 y z)
  then show ?case 
    apply (cases y)
    apply auto
    apply (erule step_exp_concat_rhsE)
    apply auto
    subgoal for e\<^sub>1 e\<^sub>2 e\<^sub>2' num\<^sub>1 sz\<^sub>1
      apply (rule exI[where x = num\<^sub>1])
      apply (rule exI[where x = sz\<^sub>1])
      apply auto
      using REDUCE by blast
    subgoal for e\<^sub>1 e\<^sub>1' v\<^sub>2 num\<^sub>1 sz\<^sub>1
      apply (rule exI[where x = num\<^sub>1])
      apply (rule exI[where x = sz\<^sub>1])
      apply auto
      using step_exps_concat_lhsI.word by blast
    subgoal for num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2
      by (simp add: bv_simps(39))
    .
qed

lemma step_exps_concat_lhs_reduce_totalE[elim]:
  assumes \<open>\<Delta> \<turnstile> (e' \<copyright> e) \<leadsto>* (num \<Colon> sz)\<close>
  obtains (H) num\<^sub>1 sz\<^sub>1 where \<open>\<Delta> \<turnstile> e \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>\<Delta> \<turnstile> (e' \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* (num \<Colon> sz)\<close>
  using GGGG[OF assms] by auto

fun 
  exps_concat_rhs_int
where
  \<open>exps_concat_rhs_int \<Delta> num sz (e' \<copyright> e) = (\<exists>num\<^sub>1 sz\<^sub>1. \<Delta> \<turnstile> e' \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1) \<and> \<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> e) \<leadsto>* (num \<Colon> sz))\<close> |
  \<open>exps_concat_rhs_int _ _ _ (_) = True\<close>

lemma step_exps_concat_rhs_reduce_total_intE:
  assumes \<open>\<Delta> \<turnstile> (e \<copyright> (num' \<Colon> sz')) \<leadsto>* (num \<Colon> sz)\<close>
  shows \<open>exps_concat_rhs_int \<Delta> num sz (e \<copyright> (num' \<Colon> sz'))\<close>
using assms proof (induct rule: INDUCT)
  case 1
  then show ?case by simp
next
  case (2 y)
  then show ?case 
    apply (cases y)
    apply auto
    apply (erule step_exp_concat_rhsE)
    apply auto
    subgoal for num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2
      apply (rule exI[where x = num\<^sub>1])
      apply (rule exI[where x = sz\<^sub>1])
      apply (intro conjI)
      using step_exps_valsI(1) apply blast
      using step_exps_concatI.word.word by presburger
    .
next
  case (3 y z)
  then show ?case 
    apply (cases y)
    apply auto
    apply (erule step_exp_concat_rhsE)
    apply auto
    subgoal for e\<^sub>1 e\<^sub>2 e\<^sub>2' num\<^sub>1 sz\<^sub>1
      apply (rule exI[where x = num\<^sub>1])
      apply (rule exI[where x = sz\<^sub>1])
      using REDUCE by blast
    subgoal for e\<^sub>1 e\<^sub>1' v\<^sub>2 num\<^sub>1 sz\<^sub>1
      apply (rule exI[where x = num\<^sub>1])
      apply (rule exI[where x = sz\<^sub>1])
      apply auto
      using REDUCE by blast
    subgoal for num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2
      by (simp add: bv_simps(39))
    .
qed

lemma step_exps_concat_rhs_reduce_totalE[elim]:
  assumes \<open>\<Delta> \<turnstile> (e \<copyright> (num' \<Colon> sz')) \<leadsto>* (num \<Colon> sz)\<close>
  obtains (H) num\<^sub>1 sz\<^sub>1 where \<open>\<Delta> \<turnstile> e \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num' \<Colon> sz')) \<leadsto>* (num \<Colon> sz)\<close>
  using step_exps_concat_rhs_reduce_total_intE[OF assms] by auto

lemma step_exp_load_word_el16_strictE[elim]:
  assumes major: \<open>\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u16 \<leadsto>* (num' \<Colon> sz')\<close> and caveat: \<open>type v = mem\<langle>sz, 8\<rangle>\<close>
  obtains (Next) num\<^sub>1 num\<^sub>2 sz\<^sub>1 sz\<^sub>2 where  \<open>\<Delta> \<turnstile> (Val v)[num \<Colon> sz, el]:u8 \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
          \<open>\<Delta> \<turnstile> (Val v)[succ (num \<Colon> sz), el]:u8 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
          \<open>\<Delta> \<turnstile> ((num\<^sub>2 \<Colon> sz\<^sub>2) \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* (num' \<Colon> sz')\<close>
using major caveat proof (elim step_exps_load_reduce_valE.word 
                               step_exp_load_word_el_strictE[where sz\<^sub>m\<^sub>e\<^sub>m = 8])
  fix e' str
  assume step: "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')" and e': "e' = unknown[str]: imm\<langle>16\<rangle>"
  show thesis
    using step unfolding e' by (meson step_exps_valE.unknown_imm word_unknown_neq)
next
  fix e' assume step: "\<Delta> \<turnstile> e' \<leadsto>* (num' \<Colon> sz')"
    and e': "e' = ((Val v)[succ (num \<Colon> sz), el]:u(16 - 8)) \<copyright> ((Val v)[num \<Colon> sz, el]:u8)"
  show thesis
    using step unfolding e' apply -
    apply (erule step_exps_concat_lhs_reduce_totalE)
    apply (erule step_exps_concat_rhs_reduce_totalE)
    apply (rule Next)
    by auto
qed auto

interpretation step_exp_load_word_el16_strictE: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz e\<^sub>2 v\<^sub>2 w\<^sub>2 _ e\<^sub>3 v\<^sub>3. (\<And>\<Delta> P. \<lbrakk>
    \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2; type v\<^sub>3 = mem\<langle>sz, 8\<rangle>;
    (\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. \<lbrakk>\<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1 \<Colon> sz\<^sub>1); 
      \<Delta> \<turnstile> e\<^sub>3[succ e\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2); 
      \<Delta> \<turnstile> ((num\<^sub>2 \<Colon> sz\<^sub>2) \<copyright> (num\<^sub>1 \<Colon> sz\<^sub>1)) \<leadsto>* e\<^sub>2\<rbrakk> \<Longrightarrow> P)
  \<rbrakk> \<Longrightarrow> P)\<close>
  apply standard
  using step_exp_load_word_el16_strictE by blast

lemma step_exps_load_next_word16_elI:
  assumes neq: \<open>w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>succ w \<noteq> (num\<^sub>1 \<Colon> sz\<^sub>1)\<close> \<open>w \<noteq> succ (num\<^sub>1 \<Colon> sz\<^sub>1)\<close>
      and type: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close> \<open>type v = mem\<langle>sz\<^sub>1, 8\<rangle>\<close>
      and is_ok: \<open>w is ok\<close> \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) is ok\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (storage_el16 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u16 \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
using nxt type(2) proof (elim step_exp_load_word_el16_strictE)
  obtain num where w: \<open>w = num \<Colon> sz\<^sub>1\<close>
    using type
    by (cases w rule: word_exhaust, simp)

  fix num\<^sub>1' num\<^sub>2' sz\<^sub>1' sz\<^sub>2' :: nat
  assume load1: "\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, el]:u8 \<leadsto>* (num\<^sub>1' \<Colon> sz\<^sub>1')"
    and load2: "\<Delta> \<turnstile> (Val v)[succ (num\<^sub>1 \<Colon> sz\<^sub>1), el]:u8 \<leadsto>* (num\<^sub>2' \<Colon> sz\<^sub>2')"
    and concat: "\<Delta> \<turnstile> ((num\<^sub>2' \<Colon> sz\<^sub>2') \<copyright> (num\<^sub>1' \<Colon> sz\<^sub>1')) \<leadsto>* (num\<^sub>2 \<Colon> sz\<^sub>2)"
  show ?thesis
    unfolding w storage_el16_def by (solve_expsI add: type neq[unfolded w] is_ok[unfolded w] load1 
        load2 concat)
qed

interpretation step_exps_load_next_word16_elI: exp_val_word_fixed_sz_syntax2_val3 
  \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta> w v'. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; w \<noteq> succ w\<^sub>1; type w = imm\<langle>sz\<^sub>1\<rangle>; type v\<^sub>3 = mem\<langle>sz\<^sub>1, 8\<rangle>;
        w is ok; w\<^sub>1 is ok; \<Delta> \<turnstile> e\<^sub>3[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> (storage_el16 v\<^sub>3 w v')[e\<^sub>1, el]:u16 \<leadsto>* e\<^sub>2)\<close>
  apply standard
  using step_exps_load_next_word16_elI by blast

lemma step_exps_store_word16_elI:
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
  shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (storage_el16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))\<close>
  unfolding storage_el16_def by (solve_expsI add: assms)

interpretation step_exps_store_word16_elI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. 
    (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, el]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_el16 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 16
  apply standard
  using step_exps_store_word16_elI by blast

\<comment> \<open>Big Endian\<close>

lemma step_exps_load_word16_beI: 
  assumes \<open>0 < sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be16 v (num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> sz))[num\<^sub>a \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u16 \<leadsto>* (ext num\<^sub>v \<Colon> sz \<sim> hi : 15 \<sim> lo : 0)\<close>
  using assms apply - 
  unfolding storage_be16_def by (solve_expsI add: step_exps_concat_word16_elI)

interpretation step_exps_load_word16_beI: exp2_val_word_sz_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2 w\<^sub>2 sz\<^sub>2.
    (\<And>\<Delta> v. 0 < sz\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile> (storage_be16 v w\<^sub>1 v\<^sub>2)[e\<^sub>1, be]:u16 \<leadsto>* ext e\<^sub>2 \<sim> hi : 15 \<sim> lo : 0)\<close>
  apply unfold_locales
  using step_exps_load_word16_beI by blast

lemma step_exps_load_next_byte16_beI: 
  assumes neq: \<open>w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close> \<open>succ w \<noteq> ((num\<^sub>1 \<Colon> sz\<^sub>1)::word)\<close>
      and nxt: \<open>\<Delta> \<turnstile> (Val v)[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
    shows \<open>\<Delta> \<turnstile> (storage_be16 v w v')[num\<^sub>1 \<Colon> sz\<^sub>1, en]:u8 \<leadsto>* e\<close>
  unfolding storage_be16_def apply -
  by (solve_expsI add: nxt neq)


interpretation step_exps_load_next_byte16_beI: exp_val2_word_sz1_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 w\<^sub>1 sz\<^sub>1 e\<^sub>2 v\<^sub>2.
    (\<And>\<Delta> v' e w en. \<lbrakk>w \<noteq> w\<^sub>1; succ w \<noteq> w\<^sub>1; \<Delta> \<turnstile> e\<^sub>2[e\<^sub>1, en]:u8 \<leadsto>* e\<rbrakk> 
          \<Longrightarrow> \<Delta> \<turnstile> (storage_be16 v\<^sub>2 w v')[e\<^sub>1, en]:u8 \<leadsto>* e)\<close>
  apply unfold_locales
  using step_exps_load_next_byte16_beI by blast 

lemma step_exps_store_word16_beI: 
  assumes \<open>type mem = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, 8\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val mem) with [num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:u16 \<leftarrow> (num\<^sub>v \<Colon> 16) \<leadsto>* (storage_be16 mem (num\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (num\<^sub>v \<Colon> 16))\<close>
  unfolding storage_be16_def by (solve_expsI add: assms)

interpretation step_exps_store_word16_beI: store_gt8_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 e\<^sub>2 w\<^sub>2 sz\<^sub>2 e\<^sub>3 v\<^sub>3. (\<And>\<Delta>. \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, be]:u16 \<leftarrow> e\<^sub>3 \<leadsto>* (storage_be16 v\<^sub>1 w\<^sub>2 v\<^sub>3))\<close> 16
  apply standard
  using step_exps_store_word16_beI by blast

\<comment> \<open>Automation\<close>
method fastsolve_exps_mem16I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  \<comment> \<open>Skip 16bit load on 16bit memory\<close>
  (rule step_exps_load_next_word16_elI.is_word2_val, solve_is_wordI, solve_is_wordI, solve_is_val, 
    solve_word_neq add: add, solve_word_neq add: add, solve_word_neq add: add, solve_type,
    solve_type, typec_word_is_ok add: add, typec_word_is_ok add: add, recurs?) |

  (rule step_exps_concat_word16_elI.is_word, solve_is_wordI) |
  (rule step_exps_load_word16_elI.is_word2 step_exps_load_word16_beI.is_word2 
        step_exps_load_byte1_16_elI.is_word2 step_exps_load_byte2_16_elI.is_word2, solve_is_wordI, 
    solve_is_wordI, (solves \<open>rule add\<close> | linarith)) |
  (rule step_exps_load_next_byte16I.is_word_val step_exps_load_next_byte16_beI.is_word_val, 
    solve_is_wordI, solve_is_val, solve_word_neq add: add, solve_word_neq add: add, recurs?) |
  (rule step_exps_store_word16_elI.is_word_val2 step_exps_store_word16_beI.is_word_val2, 
    defer_tac, solve_is_wordI, solve_is_wordI, solve_is_val, prefer_last,
    solve_type)
)

method solve_exps_mem16I_scaffold methods recurs solve_exp solve_type solve_is_val uses add = (
  fastsolve_exps_mem16I_scaffold recurs solve_exp solve_type solve_is_val add: add |

  print_fact conjI,
  solve_expsI_scaffold recurs solve_exp solve_type solve_is_val add: add
)

method solve_exps_mem16I uses add = (
  solves \<open>rule add\<close> |
  solve_exps_mem16I_scaffold \<open>solve_exps_mem16I add: add\<close> \<open>solve_expI add: add\<close> 
                             \<open>solve_type16I add: add\<close> \<open>solve_is_val16I add: add\<close> add: add
)

end
