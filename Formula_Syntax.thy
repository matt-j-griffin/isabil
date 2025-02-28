theory Formula_Syntax
  imports BIL_Syntax 
begin

(* TODO move to prelims *)
lemma in_graph_the_domI[intro]: 
  assumes \<open>a \<in> dom m\<close>
    shows \<open>(a, the (m a)) \<in> Map.graph m\<close>
  apply (rule in_graphI)
  using assms by fastforce

lemma in_graphI1[simp]: \<open>(a, b) \<in> Map.graph (m(a \<mapsto> b))\<close>
  apply (rule in_graphI) by simp

lemma in_graphI1':
  assumes \<open>val = val'\<close> shows \<open>(var, val) \<in> Map.graph (m(var \<mapsto> val'))\<close>
  unfolding assms by simp

lemma in_graphI2:
  assumes \<open>a \<noteq> c\<close> and \<open>(a, b) \<in> Map.graph m\<close> 
    shows \<open>(a, b) \<in> Map.graph (m(c \<mapsto> d))\<close>
  using assms unfolding Map.graph_def by simp

lemma in_graph_val_detD:
  assumes \<open>(a, b) \<in> Map.graph m\<close> and \<open>(a, c) \<in> Map.graph m\<close>
    shows \<open>b = c\<close>
  using assms unfolding Map.graph_def by simp

lemma in_graph_theD:
  assumes \<open>(a, b) \<in> Map.graph m\<close>
    shows \<open>the (m a) = b\<close>
  unfolding in_graphD[OF assms] by simp

lemma in_graph_domD:
  assumes \<open>(a, b) \<in> Map.graph m\<close>
    shows \<open>a \<in> dom m\<close>
  using in_graphD[OF assms] by (rule domI)

lemma in_graph_ranD:
  assumes \<open>(a, b) \<in> Map.graph m\<close>
    shows \<open>b \<in> ran m\<close>
  using in_graphD[OF assms] by (rule ranI) 

lemma in_graph_dropD:
  assumes \<open>(k\<^sub>1, v\<^sub>1) \<in> Map.graph (m(k\<^sub>2 \<mapsto> v\<^sub>2))\<close> \<open>k\<^sub>1 \<noteq> k\<^sub>2\<close>
  shows \<open>(k\<^sub>1, v\<^sub>1) \<in> Map.graph m\<close>
  using assms apply -
  apply (rule in_graphI)
  apply (drule in_graphD)
  by simp

(* - *)

lemma list_tl_neqI:
  assumes \<open>xs \<noteq> ys\<close>
    shows \<open>(x # xs) \<noteq> (x # ys)\<close>
  using assms by auto

lemma list_hd_neqI:
  assumes \<open>x \<noteq> y\<close>
    shows \<open>(x # xs) \<noteq> (y # ys)\<close>
  using assms by auto


(* Start *)

type_synonym variables = \<open>var \<rightharpoonup> val\<close>

abbreviation
  val_var_in_vars :: \<open>(var \<times> val) \<Rightarrow> variables \<Rightarrow> bool\<close> (infixl \<open>\<in>\<^sub>\<Delta>\<close> 160)
where
  \<open>(x \<in>\<^sub>\<Delta> \<Delta>) \<equiv> x \<in> Map.graph \<Delta>\<close>

(* LEGACY NAMES TODO - REMOVE *)
lemmas var_in_val_the_var = in_graph_the_domI
lemmas var_in_addI = in_graphI1
lemmas var_in_dropI = in_graphI2
lemmas var_in_deterministic = in_graph_val_detD
lemmas in_vars_the_simp = in_graph_theD
lemmas var_in_add_eqI = in_graphI1'

lemmas var_in_dom_\<Delta> = in_graph_domD

lemma graph_derestrictD:
  assumes rst: \<open>(k, v) \<in>\<^sub>\<Delta> (m |` A)\<close>
  shows \<open>(k, v) \<in>\<^sub>\<Delta> m\<close>
  using graph_restrictD(2)[OF rst] by (rule in_graphI)

lemma graph_derestrictI:
  assumes ins: \<open>k \<in> A\<close> and rst: \<open>(k, v) \<in>\<^sub>\<Delta> m\<close>
  shows \<open>(k, v) \<in>\<^sub>\<Delta> (m |` A)\<close>
  apply (rule in_graphI)
  using in_graphD[OF rst] ins by simp

lemma var_neq[simp]:\<open>(nm1 :\<^sub>t t1 \<noteq> nm2 :\<^sub>t t2) \<longleftrightarrow> (nm1 \<noteq> nm2 \<or> t1 \<noteq> t2)\<close>
  by auto 

lemmas var_expanded_in_dropI = var_in_dropI[where a = \<open>_ :\<^sub>t _\<close> and c = \<open>_ :\<^sub>t _\<close>, unfolded var_neq]

lemma var_expanded_in_name_dropI:
  assumes \<open>nme \<noteq> nme'\<close>
      and \<open>(nme :\<^sub>t typ, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(nme :\<^sub>t typ, val) \<in>\<^sub>\<Delta> \<Delta>(nme' :\<^sub>t typ \<mapsto> val')\<close>
  using assms by (intro var_expanded_in_dropI disjI1)

lemma var_expanded_in_type_dropI:
  assumes \<open>typ \<noteq> typ'\<close>
      and \<open>(nme :\<^sub>t typ, val) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(nme :\<^sub>t typ, val) \<in>\<^sub>\<Delta> \<Delta>(nme :\<^sub>t typ' \<mapsto> val')\<close>
  using assms by (intro var_expanded_in_dropI disjI2)


text \<open>Attempt to solve a proof of the form (var, val) \<in> \<Delta>\<close>

method solve_in_var uses add = (
    ((assumption | rule var_in_addI | (rule var_in_add_eqI, (simp (no_asm) only: add; fail)) | (rule var_in_dropI))+);
    (assumption | (unfold var_syntax_class.var_eq List.list.inject String.char.inject Type.inject, blast)[1])
)


named_theorems bil_var_simps \<open>Simplification rules for the solve_var_inI method.\<close>


method solve_string_neqI uses add = 
  (solves \<open>rule add list.simps(2,3) not_Cons_self not_Cons_self[symmetric]\<close>) |
  (rule list_tl_neqI, solve_string_neqI) |
  (rule list_hd_neqI, solves \<open>simp (no_asm) only: add bil_var_simps\<close>) |
  solves \<open>simp (no_asm) only: add bil_var_simps\<close>

method solve_var_inI uses add = (solves \<open>(
   solves \<open>rule add\<close> | 
   rule var_in_addI | 
  (rule var_expanded_in_name_dropI, solve_string_neqI add: add) |
  (rule var_expanded_in_type_dropI, solves \<open>simp (no_asm) only: add bil_var_simps\<close>) |
  (rule var_expanded_in_dropI, (
    (rule disjI1, solve_string_neqI add: add) | 
    (rule disjI2, solves \<open>simp (no_asm) only: add bil_var_simps\<close>)
  )) |
  (rule var_in_dropI, 
    solves \<open>simp (no_asm) only: add bil_var_simps\<close>))+\<close>)


end
