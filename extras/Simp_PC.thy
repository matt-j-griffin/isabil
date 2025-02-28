theory Simp_PC
  imports IsaBIL.Instruction_Syntax
begin

text \<open>
  A program's variable state may contain duplicate variables from move statements, to prevent
  the variable state from becoming too large we employ a simp procedure .
      
  We cant use fun_upd as it invokes the simplifier.      
\<close>

simproc_setup simp_pc (\<open>(\<Delta>, pc, mem)\<close>) = \<open>fn _ =>
  let
    fun gen_fun_upd NONE T _ _ = NONE
      | gen_fun_upd (SOME f) T x y = SOME (Const (\<^const_name>\<open>fun_upd\<close>, T) $ f $ x $ y)
    fun dest_fun_T1 (Type (_, T :: Ts)) = T
    fun find_double (t as Const (\<^const_name>\<open>Product_Type.Pair\<close>,_) $ _ $ (Const (\<^const_name>\<open>Product_Type.Pair\<close>,_) $ z $ _)) =
      let
        val _ = Pretty.writeln (Pretty.str "pc: ")
        val _ = Pretty.writeln (Syntax.pretty_term @{context} z)


       (* fun find (Const (\<^const_name>\<open>Product_Type.prod\<close>,T) $ g $ v $ w) =
              if v aconv x then SOME g else gen_fun_upd (find g) T v w
          | find t = NONE
      in (dest_fun_T1 T, gen_fun_upd (find f) T x y)*)
      in (NONE) end

    fun proc ctxt ct =
      let
        val t = Thm.term_of ct
        val _ = Pretty.writeln (Syntax.pretty_term @{context} t)
      in
        (case find_double t of
          (NONE) => NONE
        | (SOME rhs) =>
            SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs))
              (fn _ =>
                 simp_tac ctxt 1
              )
           )
        )
      end
  in proc end
\<close>

text \<open>Remove this method from the simpset to prevent it interfering\<close>

declare [[simproc del: simp_pc]]

ML \<open>

fun simp_variable goal_target ctxt = SIMPLE_METHOD (goal_target (
  (simp_tac (empty_simpset ctxt addsimprocs [\<^simproc>\<open>simp_pc\<close>]))));

val method_setup =
  Method.setup \<^binding>\<open>simp_pc\<close>
    (Scan.succeed (simp_variable HEADGOAL))
    "simplification" #>
  Method.setup \<^binding>\<open>simp_all_pc\<close>
    (Scan.succeed (simp_variable ALLGOALS))
    "simplification (all goals)";

val _ =
  Theory.setup method_setup;
\<close>

end
