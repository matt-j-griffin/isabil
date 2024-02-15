theory Expression_Syntax_Locales
  imports Expression_Syntax
begin

locale exp_val_word_sz_is_word_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes word: \<open>\<And>num sz. PROP P (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) sz\<close>
begin

lemma succ: \<open>PROP P (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) sz\<close> 
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ2: \<open>PROP P (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ3: \<open>PROP P (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ4: \<open>PROP P (succ (succ (succ (succ (num \<Colon> sz))))) (succ (succ (succ (succ (num \<Colon> sz))))) (succ (succ (succ (succ (num \<Colon> sz))))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ5: \<open>PROP P (succ (succ (succ (succ (succ (num \<Colon> sz)))))) (succ (succ (succ (succ (succ (num \<Colon> sz)))))) (succ (succ (succ (succ (succ (num \<Colon> sz)))))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ6: \<open>PROP P (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma succ7: \<open>PROP P (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) sz\<close>
  unfolding succ.simps bv_plus.simps by (rule word)

lemma true: \<open>PROP P true true true 1\<close>
  unfolding true_word by (rule word)

lemma false: \<open>PROP P false false false 1\<close>
  unfolding false_word by (rule word)

lemma bv_plus: \<open>PROP P ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) sz\<close>
  unfolding bv_plus.simps by (rule word)

lemma bv_leq: \<open>PROP P ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) 1\<close>
  unfolding bv_leq_true_or_false by (rule word)

lemma xtract: \<open>PROP P (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (sz\<^sub>1 - sz\<^sub>2 + 1)\<close> 
  unfolding xtract.simps by (rule word)

lemma xtract2: \<open>PROP P (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) (sz\<^sub>3 - sz\<^sub>4 + 1)\<close> 
  unfolding xtract.simps by (rule word)

lemmas word_syntax = word true false succ succ2 succ3 succ4 succ5 succ6 succ7 bv_plus bv_leq xtract xtract2

end

(*should be exp_val_word_sz_is_word_syntax *)
locale exp2_val_is_word_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes word2: \<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. PROP P (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>1 \<Colon> sz\<^sub>1) (num\<^sub>2 \<Colon> sz\<^sub>2) (num\<^sub>2 \<Colon> sz\<^sub>2)\<close>
begin

sublocale xtract: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) e v\<close>
  apply (standard)
  unfolding xtract.simps by (rule word2)

sublocale word: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (num \<Colon> sz) (num \<Colon> sz) e v \<close> 
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) e v \<close> 
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ2: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ3: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ4: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (succ (succ (num \<Colon> sz))))) (succ (succ (succ (succ (num \<Colon> sz))))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ5: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (succ (succ (succ (num \<Colon> sz)))))) (succ (succ (succ (succ (succ (num \<Colon> sz)))))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ6: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale succ7: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) e v \<close>
  apply (standard)
  unfolding succ.simps bv_plus.simps by (rule word2)

sublocale true: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P true true e v\<close>
  apply (standard)
  unfolding true_word by (rule word2)

sublocale false: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w _. P false false e v\<close>
  apply (standard)
  unfolding false_word by (rule word2)

lemmas word2_syntax = word.word_syntax succ.word_syntax succ2.word_syntax succ3.word_syntax 
  succ4.word_syntax succ5.word_syntax succ6.word_syntax succ7.word_syntax 
  true.word_syntax false.word_syntax xtract.word_syntax

end



locale exp_val_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes val: \<open>\<And>v. PROP P (Val v) v\<close>
begin

sublocale exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e v w sz. P e v\<close>
  apply standard
  unfolding word_constructor_exp_def by (rule val)

lemma storage: \<open>PROP P (v[w \<leftarrow> v', sz]) (v[w \<leftarrow> v', sz])\<close>
  unfolding storage_constructor_exp_def by (rule val)

lemma unknown: \<open>PROP P (unknown[str]: t) (unknown[str]: t)\<close>
  unfolding unknown_constructor_exp_def by (rule val)

lemmas syntaxs = word_syntax storage unknown val

method intro_syntax = (
  rule word | rule true | rule false | rule storage | rule unknown | rule xtract |
  rule succ | rule succ2 | rule succ3 | rule succ4 | rule succ5 | rule succ6 | rule succ7 |

  rule val 
)

end

locale exp_syntax =
  fixes Q :: \<open>exp \<Rightarrow> prop\<close>
  assumes val': \<open>\<And>v. PROP Q (Val v)\<close>
begin

sublocale exp_val_syntax
  where P = \<open>\<lambda>e _. Q e\<close>
  by (standard, rule val')

end











locale exp_word_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val: \<open>\<And>v sz. type v = imm\<langle>sz\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<close>
begin

lemma word: \<open>PROP P (num \<Colon> sz) (num \<Colon> sz) sz\<close>
  unfolding word_constructor_exp_def apply (rule val)
  by (rule type_wordI)

lemma true: \<open>PROP P true true 1\<close>
  unfolding true_exp_def apply (rule val)
  by (rule type_trueI)

lemma false: \<open>PROP P false false 1\<close>
  unfolding false_exp_def apply (rule val)
  by (rule type_falseI)

lemma unknown: \<open>PROP P (unknown[str]: imm\<langle>sz\<rangle>) (unknown[str]: imm\<langle>sz\<rangle>) sz\<close>
  unfolding unknown_constructor_exp_def 
  apply (rule val)
  by (rule type_unknownI)

lemmas word_syntaxs = word true false unknown

end

locale exp_storage_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

lemma storage: \<open>PROP P (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storageI)

lemma storage_addr: \<open>type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storage_addrI)

lemma unknown: \<open>PROP P (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
  unfolding unknown_constructor_exp_def 
  apply (rule val)
  by (rule type_unknownI)

lemmas storage_syntaxs = storage unknown storage_addr

end


locale load_multiple_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> prop\<close>
  assumes val: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num. type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
begin

sublocale storage: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' num sz\<^sub>m\<^sub>e\<^sub>m. PROP P (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storageI)

sublocale storage_addr: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' w sz\<^sub>m\<^sub>e\<^sub>m. type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storage_addrI)

sublocale unknown: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>str sz\<^sub>m\<^sub>e\<^sub>m. PROP P (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding unknown_constructor_exp_def 
  apply (rule val)
  by (rule type_unknownI)

lemmas syntaxs = storage.word_syntax unknown.word_syntax storage_addr.word_syntax

end

locale store_multiple_syntax =
  fixes P :: \<open>exp \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> prop\<close>
  assumes val: \<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num. type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P (Val v) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)\<close>
begin

sublocale storage: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' num sz\<^sub>m\<^sub>e\<^sub>m. PROP P (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storageI)

sublocale storage_addr: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>v v' w sz\<^sub>m\<^sub>e\<^sub>m. type w = imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> PROP P (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) (v[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding storage_constructor_exp_def
  apply (rule val)
  by (rule type_storage_addrI)

sublocale unknown: exp_val_word_sz_is_word_syntax
  where P = \<open>\<lambda>e _ _ sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. (\<And>str sz\<^sub>m\<^sub>e\<^sub>m. PROP P (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m e)\<close>
  apply (standard)
  unfolding unknown_constructor_exp_def 
  apply (rule val)
  by (rule type_unknownI)

lemmas syntaxs = storage.word_syntax unknown.word_syntax storage_addr.word_syntax

end



locale word_exp_val_syntax =
  fixes PW :: \<open>('a::word_constructor) \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes wordPW: \<open>\<And>num sz v. PROP PW (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) (Val v) v\<close>
begin

sublocale word: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (num \<Colon> sz) (num \<Colon> sz) (num \<Colon> sz) e v))\<close>
  by (standard, rule wordPW)

sublocale succ: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) (succ (num \<Colon> sz)) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) (succ (succ (num \<Colon> sz))) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ3: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) (succ (succ (succ (num \<Colon> sz)))) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ4: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (succ (succ (num \<Colon> sz))))) (succ (succ (succ (succ (num \<Colon> sz))))) (succ (succ (succ (succ (num \<Colon> sz)))))  e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ5: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (succ (succ (succ (num \<Colon> sz)))))) (succ (succ (succ (succ (succ (num \<Colon> sz)))))) (succ (succ (succ (succ (succ (num \<Colon> sz)))))) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ6: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

sublocale succ7: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (PW (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) e v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule wordPW)

lemmas syntaxs = word.syntaxs succ.syntaxs succ2.syntaxs succ3.syntaxs succ4.syntaxs succ5.syntaxs
                 succ6.syntaxs succ7.syntaxs

method intro_syntax = (
  word.intro_syntax | succ.intro_syntax | succ2.intro_syntax | succ3.intro_syntax | 
  succ4.intro_syntax | succ5.intro_syntax | succ6.intro_syntax | succ7.intro_syntax
)


end

locale exp2_storage_val_syntax =
  fixes P2 :: \<open>exp \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> prop\<close>
  assumes val2: \<open>\<And>v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. type v\<^sub>1 = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P2 (Val v\<^sub>1) (Val v\<^sub>2) v\<^sub>1 v\<^sub>2 sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
begin

sublocale val: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. type v' = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> PROP P2 (Val v') e v' v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  by (standard, rule val2)

sublocale storage: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'' sz. PROP P2 (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) e (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)\<close>
  unfolding storage_constructor_exp_def by (standard, rule val2, rule type_storageI)

sublocale unknown: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. PROP P2 (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) e (unknown[str]: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>) v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  unfolding unknown_constructor_exp_def by (standard, rule val2, rule type_unknownI)

lemmas storage_syntaxs2 = storage.syntaxs unknown.syntaxs val.syntaxs

end

locale exp2_val_syntax =
  fixes P2 :: \<open>exp \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> val \<Rightarrow> prop\<close>
  assumes val2: \<open>\<And>v\<^sub>1 v\<^sub>2. PROP P2 (Val v\<^sub>1) (Val v\<^sub>2) v\<^sub>1 v\<^sub>2\<close>
begin

sublocale val: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v'. PROP P2 (Val v') e v' v)\<close>
  by (standard, rule val2)

sublocale word: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP P2 (num \<Colon> sz) e (num \<Colon> sz) v)\<close>
  unfolding word_constructor_exp_def by (standard, rule val2)

sublocale true: exp_val_syntax
  where P = \<open>\<lambda>e v. PROP P2 true e true v\<close>
  unfolding true_exp_def by (standard, rule val2)

sublocale false: exp_val_syntax
  where P = \<open>\<lambda>e v. PROP P2 false e false v\<close>
  unfolding false_exp_def by (standard, rule val2)

sublocale storage: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>v' num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v'' sz. PROP P2 (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) e (v'[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v'', sz]) v)\<close>
  unfolding storage_constructor_exp_def by (standard, rule val2)

sublocale unknown: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>str t. PROP P2 (unknown[str]: t) e (unknown[str]: t) v)\<close>
  unfolding unknown_constructor_exp_def by (standard, rule val2)

sublocale xtract: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz sz\<^sub>1 sz\<^sub>2. PROP P2 (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) e (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) v)\<close>
  unfolding xtract.simps by (standard, rule word.val)

sublocale xtract2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz sz\<^sub>1 sz\<^sub>2 sz\<^sub>3 sz\<^sub>4. PROP P2 (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) e (ext (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) \<sim> hi : sz\<^sub>3 \<sim> lo : sz\<^sub>4) v)\<close> 
  unfolding xtract.simps by (standard, rule word.val)

sublocale succ: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (num \<Colon> sz)) e (succ (num \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ2: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (num \<Colon> sz))) e (succ (succ (num \<Colon> sz))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ3: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (num \<Colon> sz)))) e (succ (succ (succ (num \<Colon> sz)))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ4: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (succ (num \<Colon> sz))))) e (succ (succ (succ (succ (num \<Colon> sz))))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ5: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (succ (succ (num \<Colon> sz)))))) e (succ (succ (succ (succ (succ (num \<Colon> sz)))))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ6: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) e (succ (succ (succ (succ (succ (succ (num \<Colon> sz))))))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale succ7: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num sz. PROP (P2 (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) e (succ (succ (succ (succ (succ (succ (succ (num \<Colon> sz)))))))) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

sublocale bv_plus: exp_val_syntax
  where P = \<open>\<lambda>e v. (\<And>num\<^sub>1 num\<^sub>2 sz. PROP (P2 ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) e ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) v))\<close>
  apply standard unfolding succ.simps bv_plus.simps
  by (rule word.val)

lemmas syntaxs2 = word.syntaxs true.syntaxs false.syntaxs storage.syntaxs unknown.syntaxs val.syntaxs

end

end
