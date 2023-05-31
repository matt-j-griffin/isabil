theory Simp_Variables
  imports 
    HOL.Fun 
    HOL.Map 
    "HOL-Eisbach.Eisbach"
begin

lemma map_upd_all_eq: "(z \<noteq> x \<Longrightarrow> f z = f' z) \<Longrightarrow> (f(x \<mapsto> y)) z = (f'(x \<mapsto> y)) z"
  by simp

lemma map_upd_all_neq_left: "z \<noteq> x \<Longrightarrow> f z = f' z \<Longrightarrow> (f(x \<mapsto> y)) z = f' z"
  by simp

simproc_setup fun_upd_to_left ("f(v \<mapsto> w, x \<mapsto> y)") = \<open>fn _ =>
  let
    fun gen_fun_upd NONE T _ _ = NONE
      | gen_fun_upd (SOME f) T x y = SOME (Const (\<^const_name>\<open>fun_upd\<close>, T) $ f $ x $ y)
    fun dest_fun_T1 (Type (_, T :: Ts)) = T
    fun find_double (t as Const (\<^const_name>\<open>fun_upd\<close>,T) $ f $ x $ y) =
      let
        fun find (Const (\<^const_name>\<open>fun_upd\<close>,T) $ g $ v $ w) =
              if v aconv x then SOME g else gen_fun_upd (find g) T v w
          | find t = NONE
      in (dest_fun_T1 T, gen_fun_upd (find f) T x y) end

    fun proc ctxt ct =
      let
        val t = Thm.term_of ct
      in
        (case find_double t of
          (T, NONE) => NONE
        | (T, SOME rhs) =>
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
  in proc end
\<close>

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

end