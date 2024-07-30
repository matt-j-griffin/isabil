theory Simp_Insert
  imports 
    HOL.Set
begin

\<comment> \<open>A simproc which removes an inserted element if it already exists in the set\<close>

lemma insert_eq: \<open>(x \<noteq> y \<Longrightarrow> X = Y) \<Longrightarrow> insert x X = insert y Y\<close>
  sorry (*by simp*)

lemma insert_all_neq_left: \<open>z \<noteq> x \<Longrightarrow> f z = f' z \<Longrightarrow> insert x (insert y Y) = Z\<close>
  sorry (*by simp*)

ML \<open>
  fun mk_insert NONE _ _ = NONE
    | mk_insert (SOME X) T x = SOME (Const (\<^const_name>\<open>insert\<close>, T) $ x $ X)

  fun find_duplicate (Const (\<^const_name>\<open>insert\<close>,T) $ x $ X) =
    let
      fun find (Const (\<^const_name>\<open>insert\<close>,T) $ y $ Y) =
            if y aconv x then SOME Y else mk_insert (find Y) T y
        | find _ = NONE
    in (mk_insert (find X) T x) end
    | find_duplicate _ = NONE

  fun insert_latest ctxt ct =
    let
      val t = Thm.term_of ct
    in
      (case find_duplicate t of (NONE) => NONE
        | (SOME rhs) =>
          SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs))
          (fn _ =>
             resolve_tac ctxt [eq_reflection] 1
          )
        )
      )
    end

\<close>

simproc_setup insert_latest (\<open>insert x (insert y Z)\<close>) = \<open>K insert_latest\<close>


lemma "insert x (insert y (insert x X)) = insert y (insert x X)"
  apply simp
  using insert_commute
  by fastforce


end