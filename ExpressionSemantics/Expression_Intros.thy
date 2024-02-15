
section \<open>Introduction rules\<close>

theory Expression_Intros
  imports Expression_Rules
begin

subsection \<open>Preliminaries\<close>

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)
no_notation List.append (infixr "@" 65)
no_notation (ASCII) HOL.Not (\<open>~ _\<close> [40] 40)

subsection \<open>Vars\<close>

lemmas step_var_inI = VarIn
lemmas step_var_unI = VarNotIn

interpretation step_var_inI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> name t ed sz. (name :\<^sub>t t, v) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> (name :\<^sub>t t) \<leadsto> e)\<close>
  by (standard, rule step_var_inI)

subsection \<open>Loads\<close>

lemmas step_load_addrI = LoadStepAddr
lemmas step_load_memI = LoadStepMem
lemmas step_load_byteI = LoadByte
lemmas step_load_byte_from_nextI = LoadByteFromNext
lemmas step_load_un_addrI = LoadUnAddr
lemmas step_load_un_memI = LoadUnMem
lemmas step_load_word_beI = LoadWordBe
lemmas step_load_word_elI = LoadWordEl

interpretation step_load_memI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' ed sz. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e, ed]:usz \<leadsto> (e\<^sub>1'[e, ed]:usz))\<close>
  by (standard, rule step_load_memI)

interpretation step_load_un_memI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> str t ed sz. \<Delta> \<turnstile> (unknown[str]: t)[e, ed]:usz \<leadsto> unknown[str]: imm\<langle>sz\<rangle>)\<close>
  by (standard, rule step_load_un_memI)

interpretation step_load_byteI: word_exp_val_syntax \<open>\<lambda>w\<^sub>w w\<^sub>e _ e v'. (\<And>\<Delta> v sz ed. \<Delta> \<turnstile> v[w\<^sub>w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> e)\<close>
  by (standard, rule step_load_byteI)

interpretation step_load_byte_from_nextI: word_exp_val_syntax \<open>\<lambda>w\<^sub>w w\<^sub>e _ e v. (\<And>\<Delta> w v' sz ed. w \<noteq> w\<^sub>w \<Longrightarrow> \<Delta> \<turnstile> v[w \<leftarrow> v', sz][w\<^sub>e, ed]:usz \<leadsto> (e[w\<^sub>e, ed]:usz))\<close>
  apply (standard, rule step_load_byte_from_nextI)
  by simp

interpretation step_load_word_beI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, be]:usz \<leadsto> ((e\<^sub>1[e\<^sub>w, be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (e\<^sub>1[succ e\<^sub>w, be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close>
  by (standard, rule step_load_word_beI)

interpretation step_load_word_elI: load_multiple_syntax \<open>\<lambda>e\<^sub>1 v\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e\<^sub>w. (\<And>\<Delta> sz. sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1[e\<^sub>w, el]:usz \<leadsto> (e\<^sub>1[succ e\<^sub>w, el]:usz - sz\<^sub>m\<^sub>e\<^sub>m @ (e\<^sub>1[e\<^sub>w, el]:usz\<^sub>m\<^sub>e\<^sub>m)))\<close>
  by (standard, rule step_load_word_elI)
(*
lemma LOAD_WORD_EL_MEM_INTER: (* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close> and \<open>\<exists>num. w = (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
    shows \<open>\<Delta> \<turnstile> (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[w \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms(2) apply auto
  using assms(1) by (rule step_load_word_el.storageI)


lemmas LOAD_WORD_EL_MEM = step_load_word_el.storageI (* TODO *)

lemma LOAD_WORD_EL_MEM_SUCC: (* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM)

lemma LOAD_WORD_EL_MEM_SUCC2:(* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC)

lemma LOAD_WORD_EL_MEM_SUCC3:(* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m < sz\<close>
    shows \<open>\<Delta> \<turnstile> (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> (((v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ (v[succ (succ (succ (num\<^sub>1 \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))) \<leftarrow> num\<^sub>2 \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> 
  using assms 
  unfolding succ.simps(1)[of num\<^sub>1 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r] bv_plus.simps
  by (rule LOAD_WORD_EL_MEM_SUCC2)

lemmas LOAD_WORD_EL_MEM_WORD_ADDR = step_load_word_el.storageI (* TODO *)
*)
subsection \<open>Stores\<close>

lemmas step_store_step_valI = StoreStepVal
lemmas step_store_addrI = StoreStepAddr
lemmas step_store_memI = StoreStepMem
lemmas step_store_valI = StoreVal
lemmas step_store_un_addrI = StoreUnAddr

interpretation step_store_addrI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2' en sz. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> e))\<close>
  by (standard, rule step_store_addrI)

interpretation step_store_un_addrI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str ed sz. type v\<^sub>1 = t \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 with [unknown[str]: t', ed]:usz \<leftarrow> e\<^sub>2 \<leadsto> unknown[str]: t)\<close>
  by (standard, rule step_store_un_addrI)

interpretation step_store_memI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e' en sz. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> e with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e' with [e\<^sub>1, en]:usz \<leftarrow> e\<^sub>2))\<close>
  by (standard, rule step_store_memI)

interpretation step_store_valI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num en. \<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, en]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> e\<^sub>2 \<leadsto> (v\<^sub>1[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>2, sz\<^sub>m\<^sub>e\<^sub>m]))\<close>
  by (standard, rule step_store_valI)

lemmas step_store_word_beI = StoreWordBe
interpretation step_store_word_beI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num  sz  e. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz;
   e = e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, rule step_store_word_beI)

lemmas step_store_word_elI = StoreWordEl
interpretation step_store_word_elI: exp2_storage_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. (\<And>\<Delta> num sz e. \<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz;
   e = e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (low:sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])\<rbrakk> \<Longrightarrow>
\<Delta> \<turnstile> e\<^sub>1 with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leftarrow> e\<^sub>2 \<leadsto> (e with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (high:sz - sz\<^sub>m\<^sub>e\<^sub>m[e\<^sub>2])))\<close>
  by (standard, rule step_store_word_elI)
(*
lemmas STORE_STEP_MEM_WORD = step_store_mem.word.wordI (* TODO *)

lemmas STORE_WORD_EL_WORD = step_store_word_el.val.wordI (* TODO *)

lemmas STORE_WORD_EL_WORD_MEM = step_store_word_el.storage.wordI (* TODO *)

lemmas STORE_WORD = step_store_val.val.wordI (* TODO *)

lemmas STORE_WORD_IN_MEM = step_store_val.storage.wordI (* TODO *)

lemma STORE_STEP_MEM_BV_ADD: (* TODO *)
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4) \<leadsto> e\<^sub>1' with [(num\<^sub>2 \<Colon> sz\<^sub>2) +\<^sub>b\<^sub>v (num\<^sub>3 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>4 \<Colon> sz\<^sub>4)\<close>
  using assms unfolding bv_plus.simps by (rule STORE_STEP_MEM_WORD)

lemma STORE_STEP_MEM_SUCC: (* TODO *)
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3) \<leadsto> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> (num\<^sub>3 \<Colon> sz\<^sub>3)\<close>
  using assms unfolding succ.simps by (rule STORE_STEP_MEM_BV_ADD)

lemma STORE_STEP_MEM_SUCC_XTRACT: (* TODO *)
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz'' \<leadsto> e\<^sub>1' with [succ (num\<^sub>2 \<Colon> sz\<^sub>2), en]:usz \<leftarrow> ext (num\<^sub>3 \<Colon> sz\<^sub>3) \<sim> hi : sz' \<sim> lo : sz''\<close>
  using assms unfolding xtract.simps by (rule STORE_STEP_MEM_SUCC)

lemma STORE_XTRACT: (* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close> and \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<close>
    shows \<open>\<Delta> \<turnstile> (Val v with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  unfolding xtract.simps assms(2)[symmetric]
  apply (rule STORE_WORD)
  using assms(1,3) by blast+

lemma STORE_XTRACT_IN_MEM: (* TODO *)
  assumes \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>2 - sz\<^sub>3 + 1\<close>
    shows \<open>\<Delta> \<turnstile> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3) \<leadsto> (v[numa \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> numv \<Colon> sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> ext (num\<^sub>v\<^sub>a\<^sub>l \<Colon> sz\<^sub>1) \<sim> hi : sz\<^sub>2 \<sim> lo : sz\<^sub>3, sz\<^sub>m\<^sub>e\<^sub>m])\<close>
  using assms(1) unfolding xtract.simps assms(2)[symmetric]
  by (rule STORE_WORD_IN_MEM)
*)
subsection \<open>Let\<close>

lemmas step_let_stepI = LetStep
lemmas step_letI = Let

interpretation step_letI: exp_val_syntax \<open>\<lambda>e v. (\<And>\<Delta> e' var. \<Delta> \<turnstile> Let var e e' \<leadsto> [v\<sslash>var]e')\<close>
  by (standard, rule step_letI)

subsection \<open>Ite\<close>

lemmas step_ite_condI = IfStepCond
lemmas step_ite_thenI = IfStepThen
lemmas step_ite_elseI = IfStepElse
lemmas step_ite_trueI = IfTrue
lemmas step_ite_falseI = IfFalse
lemmas step_ite_unI = IfUnknown

interpretation step_ite_thenI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>1 e\<^sub>1' e\<^sub>2 e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> ite e\<^sub>1 e\<^sub>2 e \<leadsto> ite e\<^sub>1 e\<^sub>2' e)\<close>
  by (standard, rule step_ite_thenI)

interpretation step_ite_condI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta> e e'. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> ite e e\<^sub>1 e\<^sub>2 \<leadsto> ite e' e\<^sub>1 e\<^sub>2)\<close>
  by (standard, rule step_ite_condI)

interpretation step_ite_trueI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite true e\<^sub>1 e\<^sub>2 \<leadsto> e\<^sub>1)\<close>
  by (standard, rule step_ite_trueI)

interpretation step_ite_falseI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 _ _. (\<And>\<Delta>. \<Delta> \<turnstile> ite false e\<^sub>1 e\<^sub>2 \<leadsto> e\<^sub>2)\<close>
  by (standard, rule step_ite_falseI)

interpretation step_ite_unI: exp2_val_syntax \<open>\<lambda>e\<^sub>1 e\<^sub>2 v\<^sub>1 _. (\<And>\<Delta> t t' str . type v\<^sub>1 = t' \<Longrightarrow> \<Delta> \<turnstile> ite unknown[str]: t e\<^sub>1 e\<^sub>2 \<leadsto> unknown[str]: t')\<close>
  by (standard, rule step_ite_unI)


subsection \<open>Bop\<close>

lemmas step_bop_lhsI = BopLhs
lemmas step_bop_rhsI = BopRhs

interpretation step_bop_rhsI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>2 bop e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp e bop e\<^sub>2 \<leadsto> BinOp e bop e\<^sub>2')\<close>
  by (standard, rule step_bop_rhsI)

locale bop_lemmas =
    fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and bop :: BinOp
  assumes bop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 bop e\<^sub>2\<close>
begin

lemma lhsI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> bop_fun e\<^sub>1 e\<^sub>2 \<leadsto> bop_fun e\<^sub>1' e\<^sub>2\<close>
  using assms unfolding bop_simps by (rule step_bop_lhsI)

sublocale rhs: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>2 e\<^sub>2'. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> bop_fun e e\<^sub>2 \<leadsto> bop_fun e e\<^sub>2')\<close>
  apply standard
  unfolding bop_simps by (rule step_bop_rhsI)

end

lemmas step_aop_unk_rhsI = AopUnkRhs
lemmas step_aop_unk_lhsI = AopUnkLhs

locale aop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and aop :: AOp
  assumes aop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (AOp aop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>AOp aop\<close>
  by (standard, rule aop_simps)


lemma unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_lhsI)

lemma unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: t)\<close>
  unfolding aop_simps by (rule step_aop_unk_rhsI)

end

interpretation step_plusI: aop_lemmas \<open>(+)\<close> \<open>Plus\<close> by (standard, unfold plus_exp.simps, rule)
interpretation step_minusI: aop_lemmas \<open>(-)\<close> \<open>Minus\<close> by (standard, unfold minus_exp.simps, rule)
interpretation step_timesI: aop_lemmas \<open>(*)\<close> \<open>Times\<close> by (standard, unfold times_exp.simps, rule)
interpretation step_divideI: aop_lemmas \<open>(div)\<close> \<open>Divide\<close> by (standard, unfold divide_exp.simps, rule)
interpretation step_modI: aop_lemmas \<open>(mod)\<close> \<open>Mod\<close> by (standard, unfold modulo_exp.simps, rule)
interpretation step_sdivideI: aop_lemmas \<open>(sdiv)\<close> \<open>SDivide\<close> by (standard, unfold sdivide_exp.simps, rule)
interpretation step_smodI: aop_lemmas \<open>(smod)\<close> \<open>SMod\<close> by (standard, unfold smod_exp.simps, rule)
interpretation step_landI: aop_lemmas \<open>(&&)\<close> \<open>And\<close> by (standard, unfold land_exp.simps, rule)
interpretation step_lorI: aop_lemmas \<open>(||)\<close> \<open>Or\<close> by (standard, unfold lor_exp.simps, rule)
interpretation step_xorI: aop_lemmas \<open>(xor)\<close> \<open>Xor\<close> by (standard, unfold xor_exp.simps, rule)
interpretation step_lslI: aop_lemmas \<open>(<<)\<close> \<open>LShift\<close> by (standard, unfold lsl_exp.simps, rule)
interpretation step_lsrI: aop_lemmas \<open>(>>)\<close> \<open>RShift\<close> by (standard, unfold lsr_exp.simps, rule)
interpretation step_asrI: aop_lemmas \<open>(>>>)\<close> \<open>ARShift\<close> by (standard, unfold asr_exp.simps, rule)

lemmas step_lop_unk_rhsI = LopUnkRhs
lemmas step_lop_unk_lhsI = LopUnkLhs

locale lop_lemmas =
  fixes bop_fun :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> and lop :: LOp
  assumes lop_simps: \<open>bop_fun e\<^sub>1 e\<^sub>2 = BinOp e\<^sub>1 (LOp lop) e\<^sub>2\<close>
begin

sublocale bop_lemmas 
  where bop_fun = bop_fun 
    and bop = \<open>LOp lop\<close>
  by (standard, rule lop_simps)


lemma unk_lhsI: \<open>\<Delta> \<turnstile> bop_fun (unknown[str]: t) e \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_lhsI)

lemma unk_rhsI: \<open>\<Delta> \<turnstile> bop_fun e (unknown[str]: t) \<leadsto> (unknown[str]: imm\<langle>1\<rangle>)\<close>
  unfolding lop_simps by (rule step_lop_unk_rhsI)

end

interpretation step_ltI:  lop_lemmas \<open>(le)\<close>  Le  by (standard, unfold le_exp.simps, rule)
interpretation step_leI:  lop_lemmas \<open>(lt)\<close>  Lt  by (standard, unfold lt_exp.simps, rule)
interpretation step_sltI: lop_lemmas \<open>(sle)\<close> Sle by (standard, unfold sle_exp.simps, rule)
interpretation step_sleI: lop_lemmas \<open>(slt)\<close> Slt by (standard, unfold slt_exp.simps, rule)

lemmas step_plusI = Plus
lemmas step_minusI = Minus
lemmas step_timesI = Times
lemmas step_divI = Div
lemmas step_sdivI = SDiv
lemmas step_modI = Mod
lemmas step_smodI = SMod
lemmas step_lslI = Lsl
lemmas step_lsrI = Lsr
lemmas step_asrI = Asr
lemmas step_landI = LAnd
lemmas step_lorI = LOr
lemmas step_xorI = XOr

lemmas step_eq_sameI = EqSame
lemmas step_eq_diffI = EqDiff

lemmas step_neq_sameI = NeqSame
lemmas step_neq_diffI = NeqDiff

lemmas step_lessI = Less
lemmas step_less_eqI = LessEq
lemmas step_signed_lessI = SignedLess
lemmas step_signed_less_eqI = SignedLessEq

subsection \<open>Uop\<close>

lemmas step_uopI = Uop
lemmas step_notI = Not
lemmas step_negI = Neg
lemmas step_uop_unkI = UopUnk

lemma step_uop_unk_notI: \<open>\<Delta> \<turnstile> (~ (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding BIL_Syntax.not_exp.simps by (rule step_uop_unkI)

lemma step_uop_unk_negI: \<open>\<Delta> \<turnstile> (- (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close>
  unfolding uminus_exp.simps by (rule step_uop_unkI)

lemma step_not_falseI: \<open>\<Delta> \<turnstile> (~false) \<leadsto> true\<close>
  using bv_negation_false_true step_notI by (metis false_word)

lemma step_not_trueI: \<open>\<Delta> \<turnstile> (~true) \<leadsto> false\<close>
  using bv_negation_true_false step_notI by (metis true_word)

subsection \<open>Concat\<close>

lemmas step_concat_rhsI = ConcatRhs

lemmas step_concatI = Concat
interpretation step_concatI: exp2_val_is_word_syntax \<open>\<lambda>e\<^sub>1 _ e\<^sub>2 _. (\<And>\<Delta>. \<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<leadsto> (e\<^sub>1 \<cdot> e\<^sub>2))\<close>
  by (standard, rule step_concatI)

lemmas step_concat_lhsI = ConcatLhs
interpretation step_concat_lhsI: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e\<^sub>1 e\<^sub>1'. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ e) \<leadsto> (e\<^sub>1' @ e))\<close>
  by (standard, rule step_concat_lhsI)

lemmas step_concat_lhs_unI = ConcatLhsUn
interpretation step_concat_lhs_unI: exp_word_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>1 str. \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ e) \<leadsto> unknown[str]: imm\<langle>sz\<^sub>1 + sz\<rangle>)\<close>
  by (standard, rule step_concat_lhs_unI)

lemmas step_concat_rhs_unI = ConcatRhsUn
interpretation step_concat_rhs_unI: exp_word_syntax \<open>\<lambda>e v sz. (\<And>\<Delta> sz\<^sub>2 str. \<Delta> \<turnstile> (e @ unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) \<leadsto> unknown[str]: imm\<langle>sz + sz\<^sub>2\<rangle>)\<close>
  by (standard, rule step_concat_rhs_unI)

subsection \<open>Extract\<close>

lemmas step_extract_reduceI = ExtractReduce
lemmas step_extract_unI = ExtractUn
lemmas step_extractI = Extract

subsection \<open>Cast\<close>

lemmas step_cast_reduceI = CastReduce
lemmas step_cast_unkI = CastUnk
lemmas step_cast_lowI = CastLow
lemmas step_cast_highI = CastHigh
lemmas step_cast_signedI = CastSigned
lemmas step_cast_unsignedI = CastUnsigned

(* TODO move *)

lemmas solve_exp_simpset = (*mod_mod_trivial*) mod_Suc_eq not_dvd_plus_mod_neq not_dvd_Suc_Suc_mod_neq 
  not_dvd_Suc_mod_neq plus_mod_neq mod_Suc_neq
  plus_Suc_right_mod_neq plus_Suc_left_mod_neq 
  plus_Suc_Suc_right_mod_neq plus_Suc_Suc_left_mod_neq

method solve_word_neq = (simp (no_asm) add: solve_exp_simpset succ.simps bv_plus.simps; fail)
method solve_bv_neqI = (rule bv_not_eq_same_sz_true, (simp; fail))

method solve_expI = (
    \<comment> \<open>Attempt to discharge trivial rules (non assumptions)\<close>
  intro step_load_un_memI.syntaxs
  step_store_valI.storage.syntaxs step_store_valI.unknown.syntaxs
   
  step_letI.syntaxs
  step_ite_trueI.syntaxs2  step_ite_falseI.syntaxs2

  step_plusI step_plusI.unk_lhsI step_plusI.unk_rhsI
  step_minusI step_minusI.unk_lhsI step_minusI.unk_rhsI
  step_timesI step_timesI.unk_lhsI step_timesI.unk_rhsI 
  step_divI step_divideI.unk_lhsI step_divideI.unk_rhsI 
  step_sdivI step_sdivideI.unk_lhsI step_sdivideI.unk_rhsI 
  step_modI step_modI.unk_lhsI step_modI.unk_rhsI 
  step_smodI step_smodI.unk_lhsI step_smodI.unk_rhsI 
  step_lslI step_lslI.unk_lhsI step_lslI.unk_rhsI 
  step_lsrI step_lsrI.unk_lhsI step_lsrI.unk_rhsI
  step_asrI step_asrI.unk_lhsI step_asrI.unk_rhsI
  step_landI step_landI.unk_lhsI step_landI.unk_rhsI
  step_lorI step_lorI.unk_lhsI step_lorI.unk_rhsI
  step_xorI step_xorI.unk_lhsI step_xorI.unk_rhsI
  step_eq_sameI step_neq_sameI 
  step_lessI step_ltI.unk_lhsI step_ltI.unk_rhsI
  step_less_eqI step_leI.unk_lhsI step_leI.unk_rhsI
  step_signed_lessI step_sltI.unk_lhsI step_sltI.unk_rhsI
  step_signed_less_eqI step_sleI.unk_lhsI step_sleI.unk_rhsI
  step_lop_unk_lhsI step_lop_unk_rhsI step_aop_unk_rhsI step_aop_unk_lhsI

  step_concat_lhs_unI.word_syntaxs step_concat_rhs_unI.word_syntaxs
  
  |

  \<comment> \<open>Vars\<close>
  (rule step_var_inI.word, solve_in_var) |
  (rule step_var_inI, solve_in_var) |
  (rule step_var_unI, blast) |

  \<comment> \<open>Loads\<close>
  rule step_load_un_addrI |

  rule step_load_byteI.word.word | rule step_load_byteI.word.true | rule step_load_byteI.word.false | rule step_load_byteI.word.storage | rule step_load_byteI.word.unknown | rule step_load_byteI.word.xtract |
  rule step_load_byteI.word.succ | rule step_load_byteI.word.succ2 | rule step_load_byteI.word.succ3 | rule step_load_byteI.word.succ4 | rule step_load_byteI.word.succ5 | rule step_load_byteI.word.succ6 | rule step_load_byteI.word.succ7 |
  rule step_load_byteI.word.val |

  rule step_load_byteI.succ.word | rule step_load_byteI.succ.true | rule step_load_byteI.succ.false | rule step_load_byteI.succ.storage | rule step_load_byteI.succ.unknown | rule step_load_byteI.succ.xtract |
  rule step_load_byteI.succ.succ | rule step_load_byteI.succ.succ2 | rule step_load_byteI.succ.succ3 | rule step_load_byteI.succ.succ4 | rule step_load_byteI.succ.succ5 | rule step_load_byteI.succ.succ6 | rule step_load_byteI.succ.succ7 |
  rule step_load_byteI.succ.val |

  rule step_load_byteI.succ2.word | rule step_load_byteI.succ2.true | rule step_load_byteI.succ2.false | rule step_load_byteI.succ2.storage | rule step_load_byteI.succ2.unknown | rule step_load_byteI.succ2.xtract |
  rule step_load_byteI.succ2.succ | rule step_load_byteI.succ2.succ2 | rule step_load_byteI.succ2.succ3 | rule step_load_byteI.succ2.succ4 | rule step_load_byteI.succ2.succ5 | rule step_load_byteI.succ2.succ6 | rule step_load_byteI.succ2.succ7 |
  rule step_load_byteI.succ2.val |

  rule step_load_byteI.succ3.word | rule step_load_byteI.succ3.true | rule step_load_byteI.succ3.false | rule step_load_byteI.succ3.storage | rule step_load_byteI.succ3.unknown | rule step_load_byteI.succ3.xtract |
  rule step_load_byteI.succ3.succ | rule step_load_byteI.succ3.succ2 | rule step_load_byteI.succ3.succ3 | rule step_load_byteI.succ3.succ4 | rule step_load_byteI.succ3.succ5 | rule step_load_byteI.succ3.succ6 | rule step_load_byteI.succ3.succ7 |
  rule step_load_byteI.succ3.val |

  rule step_load_byteI.succ4.word | rule step_load_byteI.succ4.true | rule step_load_byteI.succ4.false | rule step_load_byteI.succ4.storage | rule step_load_byteI.succ4.unknown | rule step_load_byteI.succ4.xtract |
  rule step_load_byteI.succ4.succ | rule step_load_byteI.succ4.succ2 | rule step_load_byteI.succ4.succ3 | rule step_load_byteI.succ4.succ4 | rule step_load_byteI.succ4.succ5 | rule step_load_byteI.succ4.succ6 | rule step_load_byteI.succ4.succ7 |
  rule step_load_byteI.succ4.val |

  rule step_load_byteI.succ5.word | rule step_load_byteI.succ5.true | rule step_load_byteI.succ5.false | rule step_load_byteI.succ5.storage | rule step_load_byteI.succ5.unknown | rule step_load_byteI.succ5.xtract |
  rule step_load_byteI.succ5.succ | rule step_load_byteI.succ5.succ2 | rule step_load_byteI.succ5.succ3 | rule step_load_byteI.succ5.succ4 | rule step_load_byteI.succ5.succ5 | rule step_load_byteI.succ5.succ6 | rule step_load_byteI.succ5.succ7 |
  rule step_load_byteI.succ5.val |

  rule step_load_byteI.succ6.word | rule step_load_byteI.succ6.true | rule step_load_byteI.succ6.false | rule step_load_byteI.succ6.storage | rule step_load_byteI.succ6.unknown | rule step_load_byteI.succ6.xtract |
  rule step_load_byteI.succ6.succ | rule step_load_byteI.succ6.succ2 | rule step_load_byteI.succ6.succ3 | rule step_load_byteI.succ6.succ4 | rule step_load_byteI.succ6.succ5 | rule step_load_byteI.succ6.succ6 | rule step_load_byteI.succ6.succ7 |
  rule step_load_byteI.succ6.val |

  rule step_load_byteI.succ7.word | rule step_load_byteI.succ7.true | rule step_load_byteI.succ7.false | rule step_load_byteI.succ7.storage | rule step_load_byteI.succ7.unknown | rule step_load_byteI.succ7.xtract |
  rule step_load_byteI.succ7.succ | rule step_load_byteI.succ7.succ2 | rule step_load_byteI.succ7.succ3 | rule step_load_byteI.succ7.succ4 | rule step_load_byteI.succ7.succ5 | rule step_load_byteI.succ7.succ6 | rule step_load_byteI.succ7.succ7 |
  rule step_load_byteI.succ7.val |

  step_load_byteI.intro_syntax |

  (rule step_load_byte_from_nextI.word.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ2.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ3.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ4.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ5.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ6.storage, solve_word_neq) |
  (rule step_load_byte_from_nextI.succ7.storage, solve_word_neq) |

  (intro step_load_byte_from_nextI.syntaxs, linarith) | (* TODO *)

  (rule step_load_word_elI.storage.word, linarith) |
  (rule step_load_word_elI.storage_addr.succ, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ2, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ3, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ4, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ5, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ6, solve_typeI, linarith) |
  (rule step_load_word_elI.storage_addr.succ7, solve_typeI, linarith) |


  (intro step_load_word_beI.syntaxs step_load_word_elI.syntaxs, linarith) |
  (intro step_load_word_beI step_load_word_elI, linarith, solve_typeI) |
  (rule step_load_memI.bv_plus, solve_expI) |
  (intro step_load_memI.syntaxs, solve_expI) |
  (rule step_load_addrI, solve_expI) |

  \<comment> \<open>Store\<close>
  (rule step_store_step_valI, solve_expI) |
  (intro step_store_addrI.syntaxs, solve_expI) |
  (intro step_store_memI.syntaxs2, solve_expI) |
  (intro step_store_un_addrI.syntaxs2, solve_typeI) |
  (intro step_store_valI.val.syntaxs, solve_typeI) |
  (intro step_store_word_elI.storage.syntaxs step_store_word_elI.unknown.syntaxs step_store_word_beI.storage.syntaxs step_store_word_beI.unknown.syntaxs, linarith, blast) |
  (intro step_store_word_elI.val.syntaxs step_store_word_beI.val.syntaxs, solve_typeI, linarith, blast) |

  \<comment> \<open>Let\<close>
  (rule step_let_stepI, solve_expI) |

  \<comment> \<open>Ite\<close>
  (rule step_ite_elseI, solve_expI) |
  (intro step_ite_condI.syntaxs2, solve_expI) |
  (intro step_ite_thenI.syntaxs, solve_expI) |
  (intro step_ite_unI.syntaxs2, solve_typeI) |

  \<comment> \<open>Bop\<close>
  (intro step_plusI.lhsI step_minusI.lhsI step_timesI.lhsI step_divideI.lhsI step_sdivideI.lhsI 
   step_modI.lhsI step_smodI.lhsI step_lslI.lhsI step_lsrI.lhsI step_asrI.lhsI step_landI.lhsI 
   step_lorI.lhsI step_xorI.lhsI step_ltI.lhsI step_leI.lhsI step_sltI.lhsI step_sleI.lhsI, solve_expI) |
  (intro step_plusI.rhs.syntaxs step_minusI.rhs.syntaxs step_timesI.rhs.syntaxs step_divideI.rhs.syntaxs 
   step_sdivideI.rhs.syntaxs step_modI.rhs.syntaxs step_smodI.rhs.syntaxs step_lslI.rhs.syntaxs 
   step_lsrI.rhs.syntaxs step_asrI.rhs.syntaxs step_landI.rhs.syntaxs step_lorI.rhs.syntaxs 
   step_xorI.rhs.syntaxs step_leI.rhs.syntaxs step_ltI.rhs.syntaxs step_sleI.rhs.syntaxs 
   step_sltI.rhs.syntaxs, solve_expI) |

  \<comment> \<open>Plus\<close>
  (rule step_plusI) |
  (rule step_plusI.lhsI, solve_expI) |
 
  \<comment> \<open>Uop\<close>
  rule step_not_trueI | rule step_not_falseI | rule step_uop_unk_notI | rule step_uop_unk_negI |
  rule step_uop_unkI  | rule step_notI       | rule step_negI         |
  (rule step_uopI, solve_expI) |

  \<comment> \<open>Concat\<close>
  rule step_concatI | rule step_concatI.xtract.xtract |

  (rule step_concat_lhsI.word, solve_expI) | 
  (rule step_concat_lhsI.xtract, solve_expI) |

  (rule step_concat_rhsI, solve_expI) |
  (rule step_concat_lhs_unI, solve_typeI) |
  (rule step_concat_rhs_unI, solve_typeI) |

  \<comment> \<open>Extract\<close>
  rule step_extractI | rule step_extract_unI | 
  (rule step_extract_reduceI, solve_expI) |

  \<comment> \<open>Cast\<close>
  (rule step_cast_lowI) | 
  (rule step_cast_highI) | 
  (rule step_cast_signedI) | 
  (rule step_cast_unsignedI) | 
  (rule step_cast_unkI) | 
  (rule step_cast_reduceI, solve_expI)
)

text \<open>Match names of the rules from the manual\<close>

lemmas VAR_IN = step_var_inI
lemmas VAR_UNKNOWN = step_var_unI

lemmas LOAD_STEP_ADDR = step_load_addrI
lemmas LOAD_STEP_MEM = step_load_memI
lemmas LOAD_BYTE = step_load_byteI
lemmas LOAD_BYTE_FROM_NEXT = step_load_byte_from_nextI
lemmas LOAD_UN_MEM = step_load_un_memI
lemmas LOAD_UN_ADDR = step_load_un_addrI
lemmas LOAD_WORD_BE = step_load_word_beI
lemmas LOAD_WORD_EL = step_load_word_elI

lemmas STORE_STEP_VAL = step_store_step_valI
lemmas STORE_STEP_ADDR = step_store_addrI 
lemmas STORE_STEP_MEM = step_store_memI 
lemmas STORE_WORD_BE = step_store_word_beI
lemmas STORE_WORD_EL = step_store_word_elI
lemmas STORE_VAL = step_store_valI
lemmas STORE_UN_ADDR = step_store_un_addrI

lemmas LET_STEP = step_let_stepI
lemmas LET = step_letI

lemmas ITE_STEP_COND = step_ite_condI
lemmas ITE_STEP_THEN = step_ite_thenI
lemmas ITE_STEP_ELSE = step_ite_elseI
lemmas ITE_TRUE = step_ite_trueI
lemmas ITE_FALSE = step_ite_falseI
lemmas ITE_UNK = step_ite_unI

lemmas BOP_RHS = step_bop_rhsI
lemmas BOP_LHS = step_bop_lhsI

lemmas AOP_UNK_RHS = step_aop_unk_rhsI
lemmas AOP_UNK_LHS = step_aop_unk_lhsI

lemmas LOP_UNK_RHS = step_lop_unk_rhsI
lemmas LOP_UNK_LHS = step_lop_unk_lhsI

lemmas PLUS = step_plusI
lemmas MINUS = step_minusI
lemmas TIMES = step_timesI
lemmas DIV = step_divI
lemmas SDIV = step_sdivI
lemmas MOD = step_modI
lemmas SMOD = step_smodI
lemmas LSL = step_lslI
lemmas LSR = step_lsrI
lemmas ASR = step_asrI
lemmas LAND = step_landI
lemmas LOR = step_lorI
lemmas XOR = step_xorI

lemmas EQ_SAME = step_eq_sameI
lemmas EQ_DIFF = step_eq_diffI

lemmas NEQ_SAME = step_neq_sameI
lemmas NEQ_DIFF = step_neq_diffI

lemmas LESS = step_lessI
lemmas LESS_EQ = step_less_eqI
lemmas SIGNED_LESS = step_signed_lessI
lemmas SIGNED_LESS_EQ = step_signed_less_eqI

lemmas UOP = step_uopI
lemmas UOP_UNK = step_uop_unkI

lemmas NOT = step_notI
lemmas NEG = step_negI

lemmas CONCAT_RHS = step_concat_rhsI
lemmas CONCAT_LHS = step_concat_lhsI
lemmas CONCAT_RHS_UN = step_concat_rhs_unI
lemmas CONCAT_LHS_UN = step_concat_lhs_unI
lemmas CONCAT = step_concatI

lemmas EXTRACT_REDUCE = step_extract_reduceI
lemmas EXTRACT_UN = step_extract_unI
lemmas EXTRACT = step_extractI

lemmas CAST_REDUCE = step_cast_reduceI
lemmas CAST_UNK = step_cast_unkI
lemmas CAST_HIGH = step_cast_highI
lemmas CAST_LOW = step_cast_lowI
lemmas CAST_SIGNED = step_cast_signedI
lemmas CAST_UNSIGNED = step_cast_unsignedI

lemmas(in word_constructor) SUCC = succI

end
