theory Simp_Variables
  imports 
    HOL.Fun 
    HOL.Map 
begin

text \<open>
  A program's variable state may contain duplicate variables from move statements, to prevent
  the variable state from becoming too large we employ a simp procedure .
      
  We cant use fun_upd as it invokes the simplifier.      
\<close>

lemma map_upd_all_eq: \<open>(z \<noteq> x \<Longrightarrow> f z = f' z) \<Longrightarrow> (f(x \<mapsto> y)) z = (f'(x \<mapsto> y)) z\<close>
  by simp

lemma map_upd_all_neq_left: \<open>z \<noteq> x \<Longrightarrow> f z = f' z \<Longrightarrow> (f(x \<mapsto> y)) z = f' z\<close>
  by simp

ML \<open>
  fun gen_fun_upd NONE _ _ _ = NONE
    | gen_fun_upd (SOME f) T x y = SOME (Const (\<^const_name>\<open>fun_upd\<close>, T) $ f $ x $ y)

  fun find_double (Const (\<^const_name>\<open>fun_upd\<close>,T) $ f $ x $ y) =
    let
      fun find (Const (\<^const_name>\<open>fun_upd\<close>,T) $ g $ v $ w) =
            if v aconv x then SOME g else gen_fun_upd (find g) T v w
        | find _ = NONE
    in (gen_fun_upd (find f) T x y) end
    | find_double _ = NONE

  fun fun_upd_to_left ctxt ct =
    let
      val t = Thm.term_of ct
    in
      (case find_double t of
        (NONE) => NONE
      | (SOME rhs) =>
          SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs))
            (fn _ =>
               resolve_tac ctxt [eq_reflection] 1 THEN
               resolve_tac ctxt [ext] 1 THEN
               (REPEAT (((resolve_tac ctxt @{thms map_upd_all_neq_left} 1) THEN (assume_tac ctxt 1)) ORELSE (resolve_tac ctxt @{thms map_upd_all_eq} 1))) THEN
               blast_tac ctxt 1              
            )
         )
      )
    end
\<close>

simproc_setup fun_upd_to_left (\<open>f(v \<mapsto> w, x \<mapsto> y)\<close>) = \<open>K fun_upd_to_left\<close>

text \<open>Remove this method from the simpset to prevent it interfering\<close>

declare [[simproc del: fun_upd_to_left]]

ML \<open>

fun simp_variable goal_target ctxt = SIMPLE_METHOD (goal_target (
  (simp_tac (empty_simpset ctxt addsimprocs [\<^simproc>\<open>fun_upd_to_left\<close>]))));

val method_setup =
  Method.setup \<^binding>\<open>simp_variables\<close>
    (Scan.succeed (simp_variable HEADGOAL))
    "simplification" #>
  Method.setup \<^binding>\<open>simp_all_variables\<close>
    (Scan.succeed (simp_variable ALLGOALS))
    "simplification (all goals)";

val _ =
  Theory.setup method_setup;
\<close>

lemma \<open>[x \<mapsto> y, z \<mapsto> w, x \<mapsto> v] = [z \<mapsto> w, x \<mapsto> v]\<close>
  apply simp_variables
  ..

end
