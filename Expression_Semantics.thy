theory Expression_Semantics
  imports Instruction_Syntax Typing
begin

fun 
  type :: \<open>val \<Rightarrow> Type\<close>
where
  \<open>type (Storage v w v' sz) = Mem (bits w) sz\<close> | 
  \<open>type (Immediate w) = Imm (bits w)\<close> | 
  \<open>type (Unknown str t) = t\<close>

lemma \<Gamma>_val_type:
  assumes \<open>\<Gamma> \<turnstile> v :: t\<close>
    shows \<open>type v = t\<close>
  using assms apply (induct v, simp_all)
  using typing_expression_val.elims(2) apply fastforce
  by (metis Type.exhaust \<Gamma>_val_imm_not_storage typing_val_storage)

lemma \<Gamma>_type_val:
  assumes \<open>type v = t\<close>
      and \<open>\<Gamma> is ok\<close> and \<open>t is ok\<close>
      and \<open>\<forall>mem sz\<^sub>m\<^sub>e\<^sub>m w v' sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r. v = (mem[w \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])
              \<longrightarrow> (\<Gamma> \<turnstile> v' :: (Imm sz\<^sub>m\<^sub>e\<^sub>m)) \<and> (\<Gamma> \<turnstile> mem :: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))\<close>
    shows \<open>\<Gamma> \<turnstile> v :: t\<close>
  using assms apply (cases v, auto)
  apply (case_tac x1, auto)
  by (case_tac x32, auto)



definition 
  succ :: \<open>word \<Rightarrow> word\<close>
where
  \<open>succ w\<^sub>1 = w\<^sub>1 +\<^sub>b\<^sub>v (1 \<Colon> (bits w\<^sub>1))\<close>

lemma SUCC: \<open>succ (num \<Colon> sz) = (num \<Colon> sz) +\<^sub>b\<^sub>v (1 \<Colon> sz)\<close>
  by (simp add: succ_def)

text \<open>Confirmation Report lemmas\<close>

fun
  load :: \<open>val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
      let 
        sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
        w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' :: word = succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
        v\<^sub>v\<^sub>a\<^sub>l :: val = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m en;
        v\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: val = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>v\<^sub>a\<^sub>l' en
      in
        case v\<^sub>v\<^sub>a\<^sub>l of Immediate w\<^sub>v\<^sub>a\<^sub>l \<Rightarrow> (
          case v\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t of Immediate w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<Rightarrow> (
            case en of
              be \<Rightarrow> Immediate (w\<^sub>v\<^sub>a\<^sub>l \<cdot> w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) |
              el \<Rightarrow> Immediate (w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<cdot> w\<^sub>v\<^sub>a\<^sub>l)
          ) | unknown[str]: _ \<Rightarrow> unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)
        ) | unknown[str]: _ \<Rightarrow> unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)
    else (
      if w\<^sub>m\<^sub>e\<^sub>m = w\<^sub>a\<^sub>d\<^sub>d\<^sub>r then v\<^sub>m\<^sub>e\<^sub>m 
      else load mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en
    )
  )\<close> |
  \<open>load (unknown[str]: _) _ sz\<^sub>v\<^sub>a\<^sub>l _ = unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l) \<close> |
  \<open>load (Immediate _) _ _ _ = undefined\<close>

lemma load_mem_simps: 
  assumes \<open>v = (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m])\<close> 
    shows \<open>load v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en = (
    if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
      let 
        sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
        w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' :: word = succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
        v\<^sub>v\<^sub>a\<^sub>l :: val = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m en;
        v\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: val = load (mem[w\<^sub>m\<^sub>e\<^sub>m \<leftarrow> v\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' sz\<^sub>v\<^sub>a\<^sub>l' en
      in
        case v\<^sub>v\<^sub>a\<^sub>l of Immediate w\<^sub>v\<^sub>a\<^sub>l \<Rightarrow> (
          case v\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t of Immediate w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<Rightarrow> (
            case en of
              be \<Rightarrow> Immediate (w\<^sub>v\<^sub>a\<^sub>l \<cdot> w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) |
              el \<Rightarrow> Immediate (w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<cdot> w\<^sub>v\<^sub>a\<^sub>l)
          ) | unknown[str]: _ \<Rightarrow> unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)
        ) | unknown[str]: _ \<Rightarrow> unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)
    else (
      if w\<^sub>m\<^sub>e\<^sub>m = w\<^sub>a\<^sub>d\<^sub>d\<^sub>r then v\<^sub>m\<^sub>e\<^sub>m 
      else load mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l en
    )
  )\<close>
  using assms by auto

lemma load: \<open>v' = load (v[w \<leftarrow> v', sz]) w sz en\<close>
  by auto

lemma load_neq:
  assumes \<open>v'' = load v w' sz\<^sub>v\<^sub>a\<^sub>l en\<close> and \<open>w \<noteq> w'\<close> and \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l\<close>
    shows \<open>v'' = load (Storage v w v' sz\<^sub>v\<^sub>a\<^sub>l) w' sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms by auto

lemma load_unk: \<open>(unknown[str]: (Imm sz)) = load (unknown[str]: t) w sz en\<close>
  by auto

lemma load_unk_base:
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>(unknown[str]: (Imm sz\<^sub>m\<^sub>e\<^sub>m)) = load v w sz\<^sub>m\<^sub>e\<^sub>m en\<close>
    shows \<open>(unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)) = load v w sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  apply (cases v)
  using assms(1) apply simp
  using assms(4) apply fastforce
  apply (frule_tac w\<^sub>a\<^sub>d\<^sub>d\<^sub>r=w and sz\<^sub>v\<^sub>a\<^sub>l=sz\<^sub>v\<^sub>a\<^sub>l and en=en in load_mem_simps)
  using assms apply (auto simp del: load.simps)
  apply auto[1]  
  by (metis val.simps(11))

lemma load_unk_rec:
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>(Immediate w') = load v w sz\<^sub>m\<^sub>e\<^sub>m en\<close>
      and \<open>(unknown[str]: (Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))) = load v (succ w) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en\<close>
    shows \<open>(unknown[str]: (Imm sz\<^sub>v\<^sub>a\<^sub>l)) = load v w sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  apply (cases v)
  using assms(1) apply fastforce
  using assms(5) apply fastforce
  apply (frule_tac w\<^sub>a\<^sub>d\<^sub>d\<^sub>r=w and sz\<^sub>v\<^sub>a\<^sub>l=sz\<^sub>v\<^sub>a\<^sub>l and en=en in load_mem_simps)
  using assms apply (auto simp del: load.simps)
  by (metis val.simps(10) val.simps(11))

lemma load_be:
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>Immediate w\<^sub>1 = load v w sz\<^sub>m\<^sub>e\<^sub>m be\<close>
      and \<open>Immediate w\<^sub>2 = load v (succ w) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be\<close>
      and \<open>w' = w\<^sub>1 \<cdot> w\<^sub>2\<close>
    shows \<open>Immediate w' = load v w sz\<^sub>v\<^sub>a\<^sub>l be\<close>
  apply (cases v)
  using assms(1) apply fastforce
  using assms(5) apply fastforce
  apply (frule_tac w\<^sub>a\<^sub>d\<^sub>d\<^sub>r=w and sz\<^sub>v\<^sub>a\<^sub>l=sz\<^sub>v\<^sub>a\<^sub>l and en=be in load_mem_simps)
  using assms apply (auto simp del: load.simps)
  by (metis Endian.simps(4) assms(6) val.simps(10))

lemma load_el:
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>Immediate w\<^sub>1 = load v w sz\<^sub>m\<^sub>e\<^sub>m el\<close>
      and \<open>Immediate w\<^sub>2 = load v (succ w) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el\<close>
      and \<open>w' = w\<^sub>2 \<cdot> w\<^sub>1\<close>
    shows \<open>Immediate w' = load v w sz\<^sub>v\<^sub>a\<^sub>l el\<close>
  apply (cases v)
  using assms(1) apply fastforce
  using assms(5) apply fastforce
  apply (frule_tac w\<^sub>a\<^sub>d\<^sub>d\<^sub>r=w and sz\<^sub>v\<^sub>a\<^sub>l=sz\<^sub>v\<^sub>a\<^sub>l and en=el in load_mem_simps)
  using assms apply (auto simp del: load.simps)
  by (metis Endian.simps(3) assms(6) val.simps(10))



subsubsection \<open>Store\<close>

fun
  store :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en = (
    case type mem of Mem _ sz\<^sub>m\<^sub>e\<^sub>m \<Rightarrow> (
      if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        let 
          sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m);
          w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' :: word = succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r 
        in 
          case v\<^sub>v\<^sub>a\<^sub>l of Immediate w\<^sub>v\<^sub>a\<^sub>l \<Rightarrow> (
            let 
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = (case en of 
                be \<Rightarrow> ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l' \<sim> lo : 0 |
                el \<Rightarrow> ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m);
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = (case en of 
                be \<Rightarrow> ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l' | 
                el \<Rightarrow> ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0); 
              mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m]
            in
              store mem' w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) sz\<^sub>v\<^sub>a\<^sub>l' en
        ) | Unknown str t \<Rightarrow> (
          let mem' :: val = mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m] in
            store mem' w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' (Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l')) sz\<^sub>v\<^sub>a\<^sub>l' en
        )
      else (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])
    )
  )\<close>

thm store.induct

fun
  store' :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> Endian \<Rightarrow> val\<close>
where
  \<open>store' (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r then undefined
      else if bits w\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate ((ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0))), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r ) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el
      else ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r then undefined
      else if bits w\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) \<sim> lo : 0)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be        
      else ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Unknown str (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r then undefined
      else if sz \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Unknown str (Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en        
      else ((unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m))[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz)), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> bits wR then undefined
      else if bits w\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) \<sim> lo : 0)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be
      else ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> bits wR then undefined
      else if bits w\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0)), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el
      else ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Unknown str (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en = (
      if bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> bits wR then undefined
      else if sz \<noteq> sz\<^sub>v\<^sub>a\<^sub>l then undefined
      else if sz\<^sub>m\<^sub>e\<^sub>m = 0 then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m then undefined
      else if sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
        store' ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Unknown str (Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en
      else ((memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m])[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz)), sz\<^sub>m\<^sub>e\<^sub>m])
  )\<close> |
  \<open>store' _ _ _ _ _ = undefined\<close>

thm store'.induct

(*\<Gamma> \<turnstile> mem :: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m*)

lemma store_inducts[consumes 1]:
  assumes \<open>v' = store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; 
              v\<^sub>v\<^sub>a\<^sub>l = Immediate w\<^sub>v\<^sub>a\<^sub>l; en = be; v' = (
            let 
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) \<sim> lo : 0;
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)
            in
              store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be)\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; 
              v\<^sub>v\<^sub>a\<^sub>l = Immediate w\<^sub>v\<^sub>a\<^sub>l; en = el; v' = (
            let 
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m;
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0
            in
              store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el)\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m str t. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; v\<^sub>v\<^sub>a\<^sub>l = unknown[str]: t; v' = (
            (store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: (Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en)
        )\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m a b c d. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; v\<^sub>v\<^sub>a\<^sub>l = (a[b \<leftarrow> c, d]); v' = undefined\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>v\<^sub>a\<^sub>l; v' = (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m > sz\<^sub>v\<^sub>a\<^sub>l; v' = undefined\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = 0; v' = undefined\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<And>sz. \<lbrakk>type mem = Imm sz; v' = undefined\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms(1) apply (cases \<open>type mem\<close>)
  subgoal 
    using assms(9) by auto
  apply auto
  apply (case_tac \<open>x22 = 0\<close>)
  apply (simp add: assms(8))
  apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l < x22\<close>)
  apply (simp add: assms(7))
  apply (case_tac \<open>sz\<^sub>v\<^sub>a\<^sub>l > x22\<close>)
  apply (auto simp del: store.simps)
  defer
  using assms(6) apply blast
  apply (simp_all only: Let_def)
  apply (cases v\<^sub>v\<^sub>a\<^sub>l)
  apply (auto simp del: store.simps)
  apply (cases en)
  apply (auto simp del: store.simps extract_word.simps)
  using assms(3) not_gr_zero diff_zero apply (metis extract_word.elims)
  using assms(2) apply (metis less_numeral_extra(3))
  using assms(4) apply blast
  using assms(5) by blast

thm store'.induct

lemma store'_inducts[consumes 1]:
  assumes \<open>v' = store' mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
             P ((unknown[vstr]: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el)\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
             P (unknown[vstr]: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be)\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. sz = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
             P ((unknown[vstr]: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: Imm sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) unknown[str]: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en) \<close>

      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = bits wR \<Longrightarrow> 
             P memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m][w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate( ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be
            \<Longrightarrow> P memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m] w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be)\<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = bits wR \<Longrightarrow> (
            P memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m][w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el) 
            \<Longrightarrow> P memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m] w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el) \<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. sz = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0 \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l 
             \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = bits wR \<Longrightarrow>
            P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m][w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: Imm sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en 
            \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m > 0 \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. sz = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m > 0 \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m > 0
            \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = bits wR \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. sz = sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m > 0
            \<Longrightarrow> bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = bits wR \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

      (* Invalid cases *)
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> bits wR
            \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m
            \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>vstr sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. sz\<^sub>m\<^sub>e\<^sub>m = 0
            \<Longrightarrow> P (unknown[vstr]: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>memR wR vR sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. sz\<^sub>m\<^sub>e\<^sub>m = 0
            \<Longrightarrow> P (memR[wR \<leftarrow> vR, sz\<^sub>m\<^sub>e\<^sub>m]) w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. sz \<noteq> sz\<^sub>v\<^sub>a\<^sub>l
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. bits w\<^sub>v\<^sub>a\<^sub>l \<noteq> sz\<^sub>v\<^sub>a\<^sub>l
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>v uv uw ux uy. P (Immediate v) uv uw ux uy)\<close>
      and \<open>(\<And>v vb uv uw ux uy. P (unknown[v]: (Imm vb)) uv uw ux uy)\<close>
      and \<open>(\<And>uu uv v va vb vc ux uy. P uu uv (v[va \<leftarrow> vb, vc]) ux uy)\<close>
      and \<open>(\<And>uu uv v vf vg vd ux uy. P uu uv (unknown[vd]: (Mem vf vg)) ux uy)\<close>
    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms(1) gr0I apply (induct rule: store'.induct)
  using assms(8-23) apply (auto simp del: store'.simps extract_word.simps)
  using assms(2) store'.simps(1) apply (metis not_less_iff_gr_or_eq)
  using assms(3) store'.simps(2) apply (metis not_less_iff_gr_or_eq)
  using assms(4) store'.simps(3) apply (metis not_less_iff_gr_or_eq)
  using assms(5) store'.simps(4) apply (metis (no_types, lifting) not_less_iff_gr_or_eq)
  using assms(6) store'.simps(5) apply (metis (no_types, lifting) not_less_iff_gr_or_eq)
  using assms(7) store'.simps(6) by (metis not_less_iff_gr_or_eq)


lemma store''_inducts[consumes 1]:
  assumes \<open>v' = store' mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be)\<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0, sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: Imm sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; type v\<^sub>v\<^sub>a\<^sub>l = Imm sz; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m > 0; bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

      (* Invalid cases *)
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type v\<^sub>v\<^sub>a\<^sub>l = Imm sz; sz \<noteq> sz\<^sub>v\<^sub>a\<^sub>l\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz uv uw ux uy. type mem = Imm sz \<Longrightarrow> P mem uv uw ux uy)\<close>
      and \<open>(\<And>uu uv v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m ux uy. type v\<^sub>v\<^sub>a\<^sub>l = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> P uu uv v\<^sub>v\<^sub>a\<^sub>l ux uy)\<close>
    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms type.simps apply (erule_tac store'_inducts)
  by metis+

lemma store'''_inducts[consumes 1]:
  assumes \<open>v' = store' mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) \<sim> lo : 0)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be)\<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate (ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: Imm sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; type v\<^sub>v\<^sub>a\<^sub>l = Imm sz; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m > 0; bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

      (* Invalid cases *)
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<noteq> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>v\<^sub>a\<^sub>l < sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = 0\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type v\<^sub>v\<^sub>a\<^sub>l = Imm sz; sz \<noteq> sz\<^sub>v\<^sub>a\<^sub>l\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>
      and \<open>(\<And>mem sz uv uw ux. type mem = Imm sz \<Longrightarrow> P mem uv uw ux en)\<close>
      and \<open>(\<And>uu uv v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m ux. type v\<^sub>v\<^sub>a\<^sub>l = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> P uu uv v\<^sub>v\<^sub>a\<^sub>l ux en)\<close>
    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms type.simps apply (erule_tac store''_inducts)


lemma store'_wf_inducts[consumes 4]:
  assumes \<open>v' = store' mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<Gamma> \<turnstile> mem :: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: Imm sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m, sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be)\<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; bits w\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0, sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r str sz sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>m\<^sub>e\<^sub>m < sz\<^sub>v\<^sub>a\<^sub>l;
             bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r;
             P mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (unknown[str]: Imm sz\<^sub>m\<^sub>e\<^sub>m), sz\<^sub>m\<^sub>e\<^sub>m] (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (unknown[str]: (Imm sz)) sz\<^sub>v\<^sub>a\<^sub>l en) \<close>

      and \<open>(\<And>mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; type v\<^sub>v\<^sub>a\<^sub>l = Imm sz; sz = sz\<^sub>v\<^sub>a\<^sub>l; sz\<^sub>v\<^sub>a\<^sub>l = sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m > 0; bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rbrakk>
            \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en)\<close>

    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms(2) apply (drule_tac \<Gamma>_val_type)
  using assms(2) apply (drule_tac typing_val_mem)
  using assms(3) apply (drule_tac typing_val_imm)

  using assms(1,5-9) apply (induct mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en rule: store''_inducts)
  apply (auto simp del: extract_word.simps)
  oops




lemma store_wf_inducts[consumes 4]:
  assumes \<open>v' = store mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<Gamma> \<turnstile> mem :: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: Imm sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>\<And>w\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; 
              v\<^sub>v\<^sub>a\<^sub>l = Immediate w\<^sub>v\<^sub>a\<^sub>l; en = be; v' = (
            let 
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) \<sim> lo : 0;
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m)
            in
              store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) be)\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l be\<close>
      and \<open>\<And>w\<^sub>v\<^sub>a\<^sub>l. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; 
              v\<^sub>v\<^sub>a\<^sub>l = Immediate w\<^sub>v\<^sub>a\<^sub>l; en = el; v' = (
            let 
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m;
              w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0
            in
              store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) el)\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>v\<^sub>a\<^sub>l el\<close>
      and \<open>\<And>str t. \<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m \<noteq> 0; sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m; v\<^sub>v\<^sub>a\<^sub>l = unknown[str]: t; v' = (
            (store (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> (Unknown str (Imm sz\<^sub>m\<^sub>e\<^sub>m)), sz\<^sub>m\<^sub>e\<^sub>m]) (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (unknown[str]: (Imm (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m))) (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) en)
        )\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<lbrakk>type mem = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m; sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>v\<^sub>a\<^sub>l; v' = (mem[w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v\<^sub>v\<^sub>a\<^sub>l, sz\<^sub>m\<^sub>e\<^sub>m])\<rbrakk> \<Longrightarrow> P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
    shows \<open>P mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms 
  apply (frule_tac \<Gamma>_val_imm_not_storage)
  apply (frule_tac \<Gamma>_val_mem_not_immediate)
  apply (frule_tac typing_val_implies_valid_t)
  apply (frule_tac t=\<open>Imm sz\<^sub>v\<^sub>a\<^sub>l\<close> in typing_val_implies_valid_t)
  apply (cases mem)
  apply presburger
  apply (erule store_inducts)
  apply (auto simp del: store.simps extract_word.simps)
  apply (frule_tac typing_val_storage)
  apply (erule store_inducts)
  apply (auto simp del: store.simps extract_word.simps)
  using assms(1) by blast+

(*
lemma \<open>\<Gamma> \<turnstile> v :: Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow>
       \<Gamma> \<turnstile> v' :: Imm sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow>
       bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Longrightarrow>
       0 < sz\<^sub>m\<^sub>e\<^sub>m \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m \<le> sz\<^sub>v\<^sub>a\<^sub>l \<Longrightarrow> 
*)
lemma XXXXXX:
  assumes \<open>v' = store' mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l en\<close>
      and \<open>\<Gamma> \<turnstile> mem :: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
      and \<open>\<Gamma> \<turnstile> v\<^sub>v\<^sub>a\<^sub>l :: (Imm sz\<^sub>v\<^sub>a\<^sub>l)\<close>
      and \<open>sz\<^sub>m\<^sub>e\<^sub>m dvd sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>bits w\<^sub>a\<^sub>d\<^sub>d\<^sub>r = sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<close>
    shows \<open>\<Gamma> \<turnstile> v' :: (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m)\<close>
  oops


lemma store: 
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l > 0\<close>
    shows \<open>v[w \<leftarrow> v', sz\<^sub>v\<^sub>a\<^sub>l] = store v w v' sz\<^sub>v\<^sub>a\<^sub>l en\<close>
  using assms by auto

lemma store_be: 
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l < sz\<close> and \<open>0 < sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>w\<^sub>1 = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz \<sim> lo : (sz - sz\<^sub>v\<^sub>a\<^sub>l)\<close>
      and \<open>w\<^sub>2 = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : (sz - sz\<^sub>v\<^sub>a\<^sub>l) \<sim> lo : 0\<close>
      and \<open>v' = store v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>1) sz\<^sub>v\<^sub>a\<^sub>l be\<close>
      and \<open>v'' = store v' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>2) (sz - sz\<^sub>v\<^sub>a\<^sub>l) be\<close>
    shows \<open>v'' = store v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz be\<close>
  using assms apply (simp del: extract_word.simps)
  by metis+

lemma store_el: 
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l\<close> and \<open>sz\<^sub>v\<^sub>a\<^sub>l < sz\<close> and \<open>0 < sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>w\<^sub>1 = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : 0\<close>
      and \<open>w\<^sub>2 = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l\<close>
      and \<open>v' = store v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>1) sz\<^sub>v\<^sub>a\<^sub>l el\<close>
      and \<open>v'' = store v' (succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (Immediate w\<^sub>2) (sz - sz\<^sub>v\<^sub>a\<^sub>l) el\<close>
    shows \<open>v'' = store v w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz el\<close>
  using assms apply (simp del: extract_word.simps)
  by metis+


subsubsection \<open>Expression evaluation\<close>

fun
  eval_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val\<close>
where
  \<open>eval_exp \<Delta> (Val v) = v\<close> |
  \<open>eval_exp \<Delta> (Var var) = (let (name, t) = var in if var \<in> dom \<Delta> then (the (\<Delta> var)) else (Unknown [] t))\<close> |
  \<open>eval_exp \<Delta> (UnOp unop e) = ( 
    case (eval_exp \<Delta> e) of
      Immediate w \<Rightarrow> Immediate ((operator_unop unop) w) |
      Unknown str t \<Rightarrow> Unknown str t
  )\<close> |
  \<open>eval_exp \<Delta> (BinOp e\<^sub>1 binop e\<^sub>2) = (
    let v\<^sub>1 = (eval_exp \<Delta> e\<^sub>1) in
    let v\<^sub>2 = (eval_exp \<Delta> e\<^sub>2) in
    case binop of
      AOp aop \<Rightarrow> (case v\<^sub>1 of
        Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
          Immediate w\<^sub>2 \<Rightarrow> Immediate (operator_aop aop w\<^sub>1 w\<^sub>2) |
          Unknown str t \<Rightarrow> Unknown str t) |
        Unknown str t \<Rightarrow> Unknown str t)
       |
      LOp lop \<Rightarrow> (case v\<^sub>1 of
        Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
          Immediate w\<^sub>2 \<Rightarrow> Immediate (operator_lop lop w\<^sub>1 w\<^sub>2) |
          Unknown str t \<Rightarrow> Unknown str (Imm 1)) |
        Unknown str t \<Rightarrow> Unknown str (Imm 1))
  )\<close> |
  \<open>eval_exp \<Delta> (Cast cast sz e) = (
    let v = eval_exp \<Delta> e in
    case v of
      Immediate w \<Rightarrow> (case cast of
        Low \<Rightarrow> Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0) |
        High \<Rightarrow> Immediate (ext w \<sim> hi : (bits w - 1) \<sim> lo : (bits w - sz)) |
        Signed \<Rightarrow> Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0) |
        Unsigned \<Rightarrow> Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)) |
      Unknown str t \<Rightarrow> Unknown str (Imm sz)
  )\<close> |
  \<open>eval_exp \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (eval_exp (\<Delta> (var \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in
    let v\<^sub>2 = eval_exp \<Delta> e\<^sub>2 in
    case v\<^sub>1 of
      Immediate w \<Rightarrow> (
        if w = true then v\<^sub>2
        else eval_exp \<Delta> e\<^sub>3) |
      Unknown str t \<Rightarrow> Unknown str (type v\<^sub>2)
  )\<close> |
  \<open>eval_exp \<Delta> (Extract sz\<^sub>1 sz\<^sub>2 e) = (
    case (eval_exp \<Delta> e) of
      Immediate w \<Rightarrow> Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) |
      Unknown str t \<Rightarrow> Unknown str (Imm ((sz\<^sub>1 - sz\<^sub>2) + 1))
  )\<close> |
  \<open>eval_exp \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (
    let v\<^sub>1 = (eval_exp \<Delta> e\<^sub>1) in
    let v\<^sub>2 = (eval_exp \<Delta> e\<^sub>2) in
    case v\<^sub>1 of
      Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
        Immediate w\<^sub>2 \<Rightarrow> Immediate (w\<^sub>1 \<cdot> w\<^sub>2) |
        Unknown str (Imm sz\<^sub>2) \<Rightarrow> case type v\<^sub>1 of
          Imm sz\<^sub>1 \<Rightarrow> Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))        
      ) |
      Unknown str (Imm sz\<^sub>1) \<Rightarrow> case type v\<^sub>2 of
        Imm sz\<^sub>2 \<Rightarrow> Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))
      
  )\<close> |
  \<open>eval_exp \<Delta> (Load e\<^sub>1 e\<^sub>2 ed sz\<^sub>v\<^sub>a\<^sub>l) = (
    let v\<^sub>2 = eval_exp \<Delta> e\<^sub>2 in
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in 
    case v\<^sub>1 of Storage v w v' sz\<^sub>m\<^sub>e\<^sub>m \<Rightarrow> (
      case v\<^sub>2 of Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow> (
        load v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>v\<^sub>a\<^sub>l ed
      ) | Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
    ) | Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
  )\<close> |
  \<open>eval_exp \<Delta> (Store e\<^sub>1 e\<^sub>2 ed sz\<^sub>v\<^sub>a\<^sub>l e\<^sub>3) = (
    let v\<^sub>3 = eval_exp \<Delta> e\<^sub>3 in
    let v\<^sub>2 = eval_exp \<Delta> e\<^sub>2 in 
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in
    let t = type v\<^sub>1 in
    case v\<^sub>2 of Immediate w\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Rightarrow> (
      case t of Mem _ sz\<^sub>m\<^sub>e\<^sub>m \<Rightarrow> (
        store v\<^sub>1 w\<^sub>a\<^sub>d\<^sub>d\<^sub>r v\<^sub>3 sz\<^sub>v\<^sub>a\<^sub>l ed)
    ) | Unknown str _ \<Rightarrow> Unknown str t
  )\<close>
(*
lemma let_substitute_Let_size_less: 
    \<open>size_class.size (Let var e\<^sub>1 e\<^sub>2) > size_class.size ([(eval_exp \<Delta> e\<^sub>1)\<sslash>var] e\<^sub>2)\<close>
  apply auto
  apply (induct e\<^sub>1, auto)
  apply (induct e\<^sub>2, auto)
  apply (metis add.commute add_less_mono add_mono_thms_linordered_field(1) less_Suc_eq)
  using less_Suc_eq let_substitute_val_size_eq by presburger+

termination eval_exp
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (auto simp add: wf_mlex mlex_prod_def)
  using let_substitute_Let_size_less by simp
*)

fun 
  step_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto> _\<close>)
where
  \<open>(_ \<turnstile> (Val v) \<leadsto> _) = False\<close> |
  \<open>(\<Delta> \<turnstile> e \<leadsto> e') = (
    e \<noteq> e' \<and>
    eval_exp \<Delta> e = eval_exp \<Delta> e'
  )\<close>
(*    size_class.size e \<ge> size_class.size e' \<and> *)


lemma STEP_NOT_EQ: \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e)\<close>
  by (induct e, auto)

lemma STEP_NOT_REDUCTION: 
  assumes \<open>eval_exp \<Delta> e \<noteq> eval_exp \<Delta> e'\<close>
    shows \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e')\<close>
  using assms by (induct e, auto)

lemma STEP_NOT_VAL: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<leadsto> e')\<close>
  by simp

lemma STEP_IMPLIES_NOT_VAL: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>e \<noteq> Val v\<close>
  using assms by auto

lemma STEP_NEXT: 
  assumes \<open>eval_exp \<Delta> e = eval_exp \<Delta> e'\<close>
      and \<open>e \<noteq> e'\<close> and \<open>\<forall>v. e \<noteq> Val v\<close>
      and \<open>size_class.size e \<ge> size_class.size e'\<close> 
    shows \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
  using assms by (induct e, auto)



lemma VAR_IN:
  assumes \<open>(var, v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (Var var) \<leadsto> (Val v)\<close>
  using assms by auto

lemma VAR_UNKNOWN:
  assumes \<open>(name, t) \<notin> dom \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (Var (name, t)) \<leadsto> (Val (Unknown [] t))\<close>
  using assms by auto

lemma LOAD_STEP_ADDR:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2')\<close>
    shows \<open>\<Delta> \<turnstile> (Load e\<^sub>1 e\<^sub>2 ed sz) \<leadsto> (Load e\<^sub>1 e\<^sub>2' ed sz)\<close>  
  using assms by (cases e\<^sub>2, auto)

lemma LOAD_STEP_MEM:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> (Load e\<^sub>1 (Val v\<^sub>2) ed sz) \<leadsto> (Load e\<^sub>1' (Val v\<^sub>2) ed sz)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma LOAD_BYTE: 
  assumes \<open>sz \<noteq> 0\<close> 
    shows \<open>\<Delta> \<turnstile> (Load (Val (Storage v w v' sz)) (Val (Immediate w)) ed sz) \<leadsto> (Val v')\<close>
  using assms by (cases ed, auto)

lemma LOAD_BYTE_FROM_NEXT:
  assumes \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close> and \<open>sz \<noteq> 0\<close> and \<open>type v = Mem (bits w\<^sub>1) sz\<close> (*wf can prove this*)
    shows \<open>\<Delta> \<turnstile> (Load (Val (Storage v w\<^sub>1 v' sz)) (Val (Immediate w\<^sub>2)) ed sz) \<leadsto> (Load (Val v) (Val (Immediate w\<^sub>2)) ed sz)\<close>
  using assms apply auto
  apply (cases ed, auto)
  by (cases v, auto)+

lemma LOAD_UN_MEM: \<open>\<Delta> \<turnstile> (Load (Val (Unknown str t)) (Val v) ed sz) \<leadsto> (Val (Unknown str (Imm sz)))\<close>
  by (auto simp add: Let_def)

lemma LOAD_UN_ADDR: \<open>\<Delta> \<turnstile> (Load (Val (Storage v w\<^sub>1 v' sz)) (Val (Unknown str t)) ed sz') \<leadsto> (Val (Unknown str (Imm sz')))\<close>
  by auto

lemma LOAD_WORD_BE:
  assumes \<open>sz' > sz\<close> and \<open>sz > 0\<close> and \<open>succ w = w'\<close> and \<open>type v = (Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz)\<close> 
    shows \<open>\<Delta> \<turnstile> (Load (Val v) (Val (Immediate w)) be sz') \<leadsto> (Concat (Load (Val v) (Val (Immediate w)) be sz) ((Load (Val v) (Val (Immediate w')) be (sz' - sz))))\<close> 
  apply (auto simp only: step_pred_exp.simps eval_exp.simps Let_def)
  apply (cases v)
  using assms(4) apply auto[1]
  subgoal
    using assms(1-2) by (simp del: load.simps)
  subgoal
    using assms(4) load_mem_simps apply (frule_tac w\<^sub>a\<^sub>d\<^sub>d\<^sub>r=w and sz\<^sub>v\<^sub>a\<^sub>l=sz and en=be in load_mem_simps)
  oops


lemma LOAD_WORD_EL:
  assumes \<open>sz' > sz\<close> and \<open>sz \<noteq> 0\<close> and \<open>succ w = w'\<close> and \<open>v = (Storage v' w'' v'' sz)\<close>
    shows \<open>\<Delta> \<turnstile> (Load (Val v) (Val (Immediate w)) el sz') \<leadsto> (Concat (Load (Val v) (Val (Immediate w')) el (sz' - sz)) ((Load (Val v) (Val (Immediate w)) el sz)))\<close> 
  oops

lemma STORE_STEP_VAL:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) \<leadsto> (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3')\<close> 
  using assms by (cases e\<^sub>3, auto)

lemma STORE_STEP_ADDR:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 e\<^sub>2 ed sz (Val v\<^sub>3)) \<leadsto> (Store e\<^sub>1 e\<^sub>2' ed sz (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>2, auto) 

lemma STORE_STEP_MEM:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 (Val v\<^sub>2) ed sz (Val v\<^sub>3)) \<leadsto> (Store e\<^sub>1' (Val v\<^sub>2) ed sz (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>1, auto) 

lemma STORE_WORD_BE:
  assumes \<open>sz > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>succ w = w'\<close> and \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> 
      and \<open>e\<^sub>1 = (Store (Val v) (Val (Immediate w)) be sz\<^sub>m\<^sub>e\<^sub>m (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) be sz (Val val)) \<leadsto> (Store e\<^sub>1 (Val (Immediate w')) be (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  apply (simp only: step_pred_exp.simps)
  apply (intro conjI)
  apply auto
  using assms(3, 4) 
  apply (simp add: Let_def del: store.simps)
  apply (cases val)
  apply (simp del: store.simps)
  apply (subgoal_tac \<open>\<And>x sz\<^sub>m\<^sub>e\<^sub>m'. type
                 (store v w
                   (Immediate
                     raw_val x1 \<Colon> Suc (bits x1 - Suc (bits x1 - sz\<^sub>m\<^sub>e\<^sub>m)))
                   sz\<^sub>m\<^sub>e\<^sub>m be) =
           Mem x sz\<^sub>m\<^sub>e\<^sub>m'\<close>)
  using Type.inject(2) apply presburger
  oops

lemma STORE_WORD_EL:
  assumes \<open>sz' > sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close> and \<open>succ w = w'\<close> and \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> 
      and \<open>e\<^sub>1 = (Store (Val v) (Val (Immediate w)) el sz\<^sub>m\<^sub>e\<^sub>m (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) el sz' (Val val)) \<leadsto> (Store e\<^sub>1 (Val (Immediate w')) el (sz' - sz\<^sub>m\<^sub>e\<^sub>m) (Cast High (sz' - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close>
  apply (simp only: step_pred_exp.simps)
  oops

lemma STORE_VAL:
  assumes \<open>type v = Mem sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m\<close> and \<open>sz\<^sub>m\<^sub>e\<^sub>m > 0\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) ed sz\<^sub>m\<^sub>e\<^sub>m (Val v')) \<leadsto> (Val (Storage v w v' sz\<^sub>m\<^sub>e\<^sub>m))\<close>
  using assms by (cases ed, auto)


lemma STORE_UN_ADDR:
  assumes \<open>type v = t\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Unknown str t')) ed sz' (Val v')) \<leadsto> (Val (Unknown str t))\<close>
  using assms by (cases t, auto)
 

lemma LET_STEP:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> (Let var e\<^sub>1' e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)

fun 
  capture_avoiding :: \<open>(Id \<times> Type) set \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>capture_avoiding \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (var \<notin> \<Delta> \<and> capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding (\<Delta> \<union> {var}) e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (UnOp _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (BinOp e\<^sub>1 _ e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Cast _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding \<Delta> (Extract _ _ e) = capture_avoiding \<Delta> e\<close> |
  \<open>capture_avoiding \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Load e\<^sub>1 e\<^sub>2 _ _) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2)\<close> |
  \<open>capture_avoiding \<Delta> (Store e\<^sub>1 e\<^sub>2 _ _ e\<^sub>3) = (capture_avoiding \<Delta> e\<^sub>1 \<and> capture_avoiding \<Delta> e\<^sub>2 \<and> capture_avoiding \<Delta> e\<^sub>3)\<close> |
  \<open>capture_avoiding _ _ = True\<close>

lemma let_substitute_v_Let_size_less: 
    \<open>size_class.size (Let var (Val v\<^sub>1) e\<^sub>2) > size_class.size ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  by (induct e\<^sub>2, auto)

lemma capture_avoiding_substitution_eval_eq:
  assumes \<open>capture_avoiding (dom (\<Delta>(var \<mapsto> v))) e\<close> 
    shows \<open>eval_exp (\<Delta>(var \<mapsto> v)) e = eval_exp \<Delta> ([v\<sslash>var]e)\<close> 
  using assms apply (induct e arbitrary: \<Delta>)
  apply auto
  apply (simp_all only: let_substitute_val.simps capture_avoiding.simps)
  by (metis dom_fun_upd fun_upd_twist option.distinct(1))

lemma LET: 
  assumes \<open>capture_avoiding (dom \<Delta>) (Let var (Val v\<^sub>1) e\<^sub>2)\<close>
    shows \<open>\<Delta> \<turnstile> (Let var (Val v\<^sub>1) e\<^sub>2) \<leadsto> ([v\<^sub>1\<sslash>var]e\<^sub>2)\<close>
  using assms apply auto
  apply (metis less_not_refl let_substitute_v_Let_size_less)
  using let_substitute_val_size_eq apply auto[1]
  using capture_avoiding_substitution_eval_eq by simp

lemma ITE_STEP_COND:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>1, auto)

lemma ITE_STEP_THEN:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>2, auto)

lemma ITE_STEP_ELSE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3')\<close>
  using assms apply (cases e\<^sub>3, auto)
  apply (metis STEP_NOT_REDUCTION assms)
  using eval_exp.simps by presburger+


lemma ITE_TRUE: \<open>\<Delta> \<turnstile> (Ite (Val (Immediate true)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>2)\<close>
  by auto

lemma ITE_FALSE: \<open>\<Delta> \<turnstile> (Ite (Val (Immediate false)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>3)\<close>
  by auto

lemma ITE_UNK:
  assumes \<open>type v\<^sub>2 = t'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite (Val (Unknown str t)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val (Unknown str t'))\<close>
  using assms by auto

lemma BOP_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val v\<^sub>1) bop e\<^sub>2) \<leadsto> (BinOp (Val v\<^sub>1) bop e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto)

lemma BOP_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp e\<^sub>1 bop e\<^sub>2) \<leadsto> (BinOp e\<^sub>1' bop e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma AOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (AOp aop) (Val (Unknown str t))) \<leadsto> (Val (Unknown str t))\<close>
  by auto

lemma AOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Unknown str t)) (AOp aop) (Val v)) \<leadsto> (Val (Unknown str t))\<close>
  by (cases v, auto)

lemma LOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp lop) (Val (Unknown str t))) \<leadsto> (Val (Unknown str (Imm 1)))\<close>
  by auto

lemma LOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Unknown str t)) (LOp lop) (Val v)) \<leadsto> (Val (Unknown str (Imm 1)))\<close>
  by auto

lemma PLUS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Plus) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma MINUS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Minus) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma TIMES: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Times) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma DIV: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Divide) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SDIV: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp SDivide) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma MOD: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Mod) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SMOD: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp SMod) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LSL: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp LShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <<\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LSR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp RShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 >>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma ASR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp ARShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 >>>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LAND: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp And) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 &\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LOR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Or) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 |\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma XOR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Xor) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 xor\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma EQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp Eq) (Val (Immediate w))) \<leadsto> (Val (Immediate (true)))\<close>
  by auto

lemma EQ_DIFF: 
  assumes \<open>w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = true\<close>
      and \<open>bits w\<^sub>1 = bits w\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Eq) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate false))\<close>
  using assms by auto 

lemma NEQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp Neq) (Val (Immediate w))) \<leadsto> (Val (Immediate false))\<close>
  by auto

lemma NEQ_DIFF: 
  assumes \<open>w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = true\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Neq) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate true))\<close>
  using assms by auto

lemma LESS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Lt) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LESS_EQ: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Le) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<le>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SIGNED_LESS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Slt) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SIGNED_LESS_EQ: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Sle) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<le>\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma UOP: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (UnOp uop e) \<leadsto> (UnOp uop e')\<close>
  using assms by (cases e, auto)

lemma UOP_UNK: \<open>\<Delta> \<turnstile> (UnOp uop (Val (Unknown str t))) \<leadsto> (Val (Unknown str t))\<close>
  by auto

lemma NOT: \<open>\<Delta> \<turnstile> (UnOp Not (Val (Immediate w))) \<leadsto> (Val (Immediate (~\<^sub>b\<^sub>v w)))\<close>
  by auto

lemma NEG: \<open>\<Delta> \<turnstile> (UnOp Neg (Val (Immediate w))) \<leadsto> (Val (Immediate (-\<^sub>b\<^sub>v w)))\<close>
  by auto

lemma CONCAT_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Concat e\<^sub>1 e\<^sub>2) \<leadsto> (Concat e\<^sub>1 e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto)

lemma CONCAT_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Concat e\<^sub>1 (Val v\<^sub>2)) \<leadsto> (Concat e\<^sub>1' (Val v\<^sub>2))\<close>
  using assms by (cases e\<^sub>1, auto)

lemma CONCAT_LHS_UN:
  assumes \<open>type v\<^sub>2 = Imm sz\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (Concat (Val (Unknown str (Imm sz\<^sub>1))) (Val v\<^sub>2)) \<leadsto> (Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))))\<close>
  using assms by auto

lemma CONCAT_RHS_UN:
  assumes \<open>bits w = sz\<^sub>1\<close>
    shows \<open>\<Delta> \<turnstile> (Concat (Val (Immediate w)) (Val (Unknown str (Imm sz\<^sub>2)))) \<leadsto> (Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))))\<close>
  using assms by auto 

lemma CONCAT: \<open>\<Delta> \<turnstile> (Concat (Val (Immediate w\<^sub>1)) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<cdot> w\<^sub>2)))\<close>
  by auto

lemma EXTRACT: \<open>\<Delta> \<turnstile> (Extract sz\<^sub>1 sz\<^sub>2 (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)))\<close>
  by auto

lemma CAST_REDUCE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto> (Cast cast sz e')\<close>
  using assms by (cases e, auto)

lemma CAST_UNK: \<open>\<Delta> \<turnstile> (Cast cast sz (Val (Unknown str t))) \<leadsto> (Val (Unknown str (Imm sz)))\<close>
  by auto

lemma CAST_LOW: \<open>\<Delta> \<turnstile> (Cast Low sz (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto

lemma CAST_HIGH: \<open>\<Delta> \<turnstile> (Cast High sz (Val (Immediate (num \<Colon> sz')))) \<leadsto> (Val (Immediate (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))))\<close>
  by auto

lemma CAST_SIGNED: \<open>\<Delta> \<turnstile> (Cast Signed sz (Val (Immediate w))) \<leadsto> (Val (Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto

lemma CAST_UNSIGNED: \<open>\<Delta> \<turnstile> (Cast Unsigned sz (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto


fun
  eval_exps_pred :: \<open>variables \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close>)
where
  \<open>(\<Delta> \<turnstile> e \<leadsto>* v) = (v = eval_exp \<Delta> e)\<close>

(* TODO if I can prove this we're good *)
lemma REDUCE: 
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* v\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* v\<close>
  using assms sorry



(* THERE is a lot that needs to be done *)


end
