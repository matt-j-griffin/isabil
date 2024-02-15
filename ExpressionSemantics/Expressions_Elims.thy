
section \<open>Elimination rules for big step expressions\<close>

theory Expressions_Elims
  imports Expressions_Rules Expression_Elims
          
begin

text \<open>Better reduce rule that includes the assumption e3 \<noteq> e1\<close>

lemma step_exps_reduceE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and reflE: \<open>e\<^sub>3 = e\<^sub>1 \<Longrightarrow> P\<close>
    shows P
proof (cases \<open>e\<^sub>3 = e\<^sub>1\<close>)
  case True
  then show ?thesis by (rule reflE)
next
  case False
  show ?thesis 
    using assms(1) apply (rule ReduceE)
    subgoal for e\<^sub>2
      using False by (intro reduceE[of e\<^sub>2] conjI)
    using False by (elim notE)
qed

lemma step_exps_reduce_strictE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* e\<^sub>3\<close> and \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<leadsto>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (rule step_exps_reduceE)
  subgoal for e\<^sub>2
    using assms(2) by (intro reduceE[of e\<^sub>2] conjI)
  using assms(2) by (elim notE)


subsection \<open>Values\<close>

lemma step_exps_valE:
  assumes \<open>\<Delta> \<turnstile> (Val v) \<leadsto>* e\<close>
      and \<open>e = (Val v) \<Longrightarrow> P\<close>
    shows P
  apply (rule step_exps_reduceE[OF assms(1) _ assms(2)])
  using step_exp_not_val by blast

interpretation step_exps_valE: exp_syntax \<open>\<lambda>e. (\<And>\<Delta> e' P. \<Delta> \<turnstile> e \<leadsto>* e' \<Longrightarrow> (e' = e \<Longrightarrow> P) \<Longrightarrow> P)\<close>
  by (standard, rule step_exps_valE)

subsection \<open>Variables\<close>

(*
Var var
*)

subsection \<open>Load\<close>
(*
Load exp exp Endian nat	 (\<open>_[_, _]:u_\<close>)
*)

subsection \<open>Store\<close>
(*
Store exp exp Endian nat exp (\<open>_ with [_, _]:u_ \<leftarrow> _\<close>) (*TODO: u?*)
*)

subsection \<open>BinOp\<close>
(*
BinOp exp BinOp exp
*)

subsection \<open>UnOp\<close>
(*
UnOp UnOp exp
*)

subsection \<open>Cast\<close>
(*
Cast Cast nat exp  (\<open>_:_[_]\<close>)
*)

subsection \<open>Let\<close>
(*
Let var exp exp
*)

subsection \<open>Ite\<close>
(*
Ite exp exp exp (\<open>ite _ _ _\<close>)
*)

subsection \<open>Extract\<close>
(*
Extract nat nat exp (\<open>extract:_:_[_]\<close>)
*)

subsection \<open>Concat\<close>
(*
Concat exp exp
*)

end
