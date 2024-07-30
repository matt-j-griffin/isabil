
theory Simp_Word
  imports 
    "../Instruction_Syntax" Simp_Variables
begin

text \<open>
  Some bitvector operations can be simplified
\<close>
lemma bv_minus_geI: 
  assumes \<open>a \<ge> b\<close> and \<open>(a - b \<Colon> sz) = X\<close> shows \<open>(a \<Colon> sz) -\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_minus.simps(1) by auto

lemma bv_minus_ltI: 
  assumes \<open>a < b\<close> and \<open>(2 ^ sz + a - b \<Colon> sz) = X\<close> shows \<open>(a \<Colon> sz) -\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_minus.simps(1) by auto



lemma bv_plus_lessI: 
  assumes \<open>a + b < 2 ^ sz\<close> and \<open>(a + b \<Colon> sz) = X\<close> shows \<open>(a \<Colon> sz) +\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_plus.simps(1) by auto

lemma bv_plus_less: 
  assumes \<open>a + b < 2 ^ sz\<close> shows \<open>(a \<Colon> sz) +\<^sub>b\<^sub>v (b \<Colon> sz) = (a + b \<Colon> sz)\<close>
  using assms bv_plus_lessI by auto
(*
lemma bv_plus_rollI: 
  assumes \<open>a + b = 2 ^ sz\<close> and \<open>(0 \<Colon> sz) = X\<close> shows \<open>(a \<Colon> sz) +\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_plus.simps(1) by auto

lemma bv_plus_roll: 
  assumes \<open>a + b = 2 ^ sz\<close> shows \<open>(a \<Colon> sz) +\<^sub>b\<^sub>v (b \<Colon> sz) = (0 \<Colon> sz)\<close>
  using assms bv_plus_rollI by auto

lemma bv_plus0I:
  assumes \<open>num < 2 ^ sz\<close> and \<open>(num \<Colon> sz) = X\<close>
    shows \<open>(num \<Colon> sz) +\<^sub>b\<^sub>v (0 \<Colon> sz) = X\<close> and \<open>(0 \<Colon> sz) +\<^sub>b\<^sub>v (num \<Colon> sz) = X\<close>
  using assms apply (metis add.right_neutral bv_plus_less)
  by (metis assms(1) assms(2) bv_plus_less plus_nat.add_0)

lemma bv_plus0:
  assumes \<open>num < 2 ^ sz\<close>
    shows \<open>(num \<Colon> sz) +\<^sub>b\<^sub>v (0 \<Colon> sz) = (num \<Colon> sz)\<close> and \<open>(0 \<Colon> sz) +\<^sub>b\<^sub>v (num \<Colon> sz) = (num \<Colon> sz)\<close>
  using assms bv_plus0I by blast+

lemma bv_plus_commute_lessI: 
  assumes \<open>a + b < 2 ^ sz\<close> and \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v (a + b \<Colon> sz) = X\<close> 
    shows \<open>((x \<Colon> sz) +\<^sub>b\<^sub>v (a \<Colon> sz)) +\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_plus.simps(1) apply auto
  by presburger
*)
lemma bv_plus_commute_lessI2: 
  assumes \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v ((a + b) mod 2 ^ sz \<Colon> sz) = X\<close> 
    shows \<open>((x \<Colon> sz) +\<^sub>b\<^sub>v (a \<Colon> sz)) +\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_plus.simps(1) apply auto
  by (metis group_cancel.add1 mod_add_left_eq mod_add_right_eq)

(*
lemma bv_plus_commute_less: 
  assumes \<open>a + b < 2 ^ sz\<close>
    shows \<open>((x \<Colon> sz) +\<^sub>b\<^sub>v (a \<Colon> sz)) +\<^sub>b\<^sub>v (b \<Colon> sz) = (x \<Colon> sz) +\<^sub>b\<^sub>v (a + b \<Colon> sz)\<close>
  using assms bv_plus_commute_lessI[where X = \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v (a + b \<Colon> sz)\<close>] by auto

lemma bv_plus_commute_rollI: 
  assumes \<open>a + b = 2 ^ sz\<close> and \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v (0 \<Colon> sz) = X\<close> 
    shows \<open>((x \<Colon> sz) +\<^sub>b\<^sub>v (a \<Colon> sz)) +\<^sub>b\<^sub>v (b \<Colon> sz) = X\<close>
  using assms unfolding bv_plus.simps(1) apply auto
  unfolding mod_simps
  by (metis group_cancel.add1 mod_add_self2 mod_less)

lemma bv_plus_commute_roll:
  assumes \<open>a + b = 2 ^ sz\<close>
    shows \<open>((x \<Colon> sz) +\<^sub>b\<^sub>v (a \<Colon> sz)) +\<^sub>b\<^sub>v (b \<Colon> sz) = (x \<Colon> sz) +\<^sub>b\<^sub>v (0 \<Colon> sz)\<close>
  using assms bv_plus_commute_rollI[where X = \<open>(x \<Colon> sz) +\<^sub>b\<^sub>v (0 \<Colon> sz)\<close>] by auto
*)
lemma bv_plus_inject: \<open>x = z \<Longrightarrow> y = w \<Longrightarrow> (x \<Colon> sz) +\<^sub>b\<^sub>v (y \<Colon> sz) = (z \<Colon> sz) +\<^sub>b\<^sub>v (w \<Colon> sz)\<close>
  by auto

lemma bv_minus_inject: \<open>x = z \<Longrightarrow> y = w \<Longrightarrow> (x \<Colon> sz) -\<^sub>b\<^sub>v (y \<Colon> sz) = (z \<Colon> sz) -\<^sub>b\<^sub>v (w \<Colon> sz)\<close>
  by auto

lemma modulo_nat_multiI: "k = x div y \<Longrightarrow> X = x - k * y \<Longrightarrow> x mod (y::nat) = X"
  unfolding modulo_nat_def by auto

ML \<open>
  fun mk_true  T = Const (\<^const_name>\<open>true\<close>, T)
  fun mk_false T = Const (\<^const_name>\<open>false\<close>,T)

  (* Surprised this does not exist *)
  fun map_option F (SOME a) = SOME (F a)
    | map_option _ NONE = NONE

  fun func_typs (Type (@{type_name "fun"}, [T1, T2])) = (T1, T2)
    | func_typs _ = error "Not a function type";

  (* duplicate ?*)
  fun power (_ , 0) = 1
    | power (base : int, exponent : int) =
        if exponent < 0 then error "Exponent must be non-negative."
        else base * power (base, exponent - 1)

  (* Bitwise AND for arbitrary precision integers *)
  fun bitwise_and (x: int, y: int): int =
    let
      fun loop (0, _, _) = 0
        | loop (_, 0, _) = 0
        | loop (x, y, bit) =
            let
              val x_bit = x mod 2
              val y_bit = y mod 2
              val rest = loop (x div 2, y div 2, bit * 2)
            in
              if x_bit = 1 andalso y_bit = 1 then bit + rest
              else rest
            end
    in
      loop (x, y, 1)
    end;

  (* Bitwise OR for arbitrary precision integers *)
  fun bitwise_or (x: int, y: int): int =
    let
      fun loop (0, 0, _) = 0
        | loop (x, 0, bit) = x * bit
        | loop (0, y, bit) = y * bit
        | loop (x, y, bit) =
            let
              val x_bit = x mod 2
              val y_bit = y mod 2
              val rest = loop (x div 2, y div 2, bit * 2)
            in
              if x_bit = 1 orelse y_bit = 1 then bit + rest
              else rest
            end
    in
      loop (x, y, 1)
    end;

  fun find_commute_bv_plus_new (Const (\<^const_name>\<open>bv_plus\<close>,Tp)
                      $ (Const (\<^const_name>\<open>bv_plus\<close>,_)
                        $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnumo $ _)
                        $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum1 $ _))
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ sz)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val (_,numsz) = HOLogic.dest_number sz
        val sum = num1 + num2
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))

        val wr = Const (\<^const_name>\<open>bv_plus\<close>,Tp)
                  $ (Const (\<^const_name>\<open>word_constructor\<close>, Tw) $ tnumo $ sz)
                  $ (Const (\<^const_name>\<open>word_constructor\<close>, Tw)
                    $ HOLogic.mk_number HOLogic.natT remainder
                    $ sz)
      in (SOME (wr, quotient)) end) ()

    handle TERM _ =>
      NONE)
    | find_commute_bv_plus_new _ = error ("Did not match pattern ((nat\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)) +\<^sub>b\<^sub>v (nat\<^sub>3 \<Colon> sz)")

  val modulo_nat_multiI = @{thm modulo_nat_multiI}
  fun thm_for ctxt x = Thm.instantiate (TVars.empty, Vars.make1 ((("k", 0), HOLogic.natT), Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.natT x))) modulo_nat_multiI;

  fun simp_bv (Const (\<^const_name>\<open>bv_lt\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ _)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val T = snd (func_typs (snd (func_typs Tw)))

      in if (num1 < num2) then SOME (mk_true T, 0) else SOME (mk_false T, 0) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_eq\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ _)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val T = snd (func_typs (snd (func_typs Tw)))

      in if (num1 = num2) then SOME (mk_true T, 0) else SOME (mk_false T, 0) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_minus\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val (_,numsz) = HOLogic.dest_number sz
        val sum = (num1 - num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT remainder
                  $ sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lsl\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val (_,numsz) = HOLogic.dest_number sz
        val sum = num1 * power (2, num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT remainder
                  $ sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lsr\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val sum = (num1 div power (2, num2))
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT sum
                  $ sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_plus\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val (_,numsz) = HOLogic.dest_number sz
        val sum = (num1 + num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT remainder
                  $ sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_land\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val result = bitwise_and (num1, num2)
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT result
                  $ sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lor\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val (_,num1) = HOLogic.dest_number tnum1
        val (_,num2) = HOLogic.dest_number tnum2
        val result = bitwise_or (num1, num2)
        val wr = Const (\<^const_name>\<open>word_constructor\<close>,Tw)
                  $ HOLogic.mk_number HOLogic.natT result
                  $ sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv typ = error ("Did not match simproc pattern: " ^ Pretty.string_of (Syntax.pretty_term @{context} typ))

  fun mod_tac ctxt quotient = 
    HEADGOAL (resolve_tac ctxt [thm_for ctxt quotient]) THEN
    HEADGOAL (Lin_Arith.simple_tac ctxt) THEN
    HEADGOAL (Lin_Arith.simple_tac ctxt)

  fun simproc_bv proof ctxt ct =
    let 
      val t = Thm.term_of ct;
    in
      (case simp_bv t of
        (NONE) => NONE
      | (SOME (rhs, quotient)) =>
          SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs)) (K (proof quotient)))
      )
    end

  fun simp_bv_less ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN
      HEADGOAL (resolve_tac ctxt @{thms bv_lt_false bv_lt_true}) THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt)
    ) ctxt

  fun simp_bv_plus ctxt = simproc_bv (fn quotient =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms bv_plus.simps word_inject power_numeral Num.pow.simps Num.sqr.simps} THEN
      Method.intros_tac ctxt [conjI, thm_for ctxt quotient, refl] [] THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt) THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt)
    ) ctxt

  fun simp_bv_minus ctxt = simproc_bv (fn quotient =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN ((
        HEADGOAL (resolve_tac ctxt [@{thm bv_minus_geI}]) THEN
        HEADGOAL (Lin_Arith.simple_tac ctxt)
      ) ORELSE (
        HEADGOAL (resolve_tac ctxt [@{thm bv_minus_ltI}]) THEN
        HEADGOAL (Lin_Arith.simple_tac ctxt))) THEN
      unfold_tac ctxt @{thms word_inject power_numeral Num.pow.simps Num.sqr.simps} THEN
      Method.intros_tac ctxt [conjI, thm_for ctxt quotient, refl] [] THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt) THEN TRY (
      HEADGOAL (Lin_Arith.simple_tac ctxt))
    ) ctxt

  fun simp_bv_eq ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN (
        HEADGOAL (resolve_tac ctxt [@{thm bv_eq}]) ORELSE (
        HEADGOAL (resolve_tac ctxt [@{thm bv_not_eq}]) THEN
        HEADGOAL (resolve_tac ctxt [@{thm word_not_sz_neqI}]) THEN
        HEADGOAL (Lin_Arith.simple_tac ctxt)
        )
      )
    ) ctxt

  fun simp_bv_lsl ctxt = simproc_bv (fn quotient =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms bv_lsl.simps word_inject power_numeral Num.pow.simps Num.sqr.simps} THEN
      Method.intros_tac ctxt [conjI, thm_for ctxt quotient, refl] [] THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt) THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt)
    ) ctxt

  fun simp_bv_lsr ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms bv_lsr.simps word_inject power_numeral Num.pow.simps Num.sqr.simps div_0} THEN
      Method.intros_tac ctxt [conjI, refl] [] THEN
      TRY (HEADGOAL (Lin_Arith.simple_tac ctxt))
    ) ctxt

  fun simp_bv_land ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms bv_land.simps word_inject and_numerals numeral_One and_zero_eq zero_and_eq} THEN
      Method.intros_tac ctxt [conjI, refl] [] THEN
      TRY (HEADGOAL (Lin_Arith.simple_tac ctxt))
    ) ctxt

  fun simp_bv_lor ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms bv_lor.simps word_inject or_numerals numeral_One or.left_neutral or.right_neutral} THEN
      Method.intros_tac ctxt [conjI, refl] [] THEN
      TRY (HEADGOAL (Lin_Arith.simple_tac ctxt))
    ) ctxt
\<close>

simproc_setup simp_bv_plus  (\<open>(nat\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_plus\<close>
simproc_setup simp_bv_minus (\<open>(nat\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_minus\<close>
simproc_setup simp_bv_less  (\<open>(nat\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_less\<close>
simproc_setup simp_bv_eq    (\<open>(nat\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_eq\<close>
simproc_setup simp_bv_lsl   (\<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) <<\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2)\<close>) = \<open>K simp_bv_lsl\<close>
simproc_setup simp_bv_lsr   (\<open>(nat\<^sub>1 \<Colon> sz\<^sub>1) >>\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz\<^sub>2)\<close>) = \<open>K simp_bv_lsr\<close>
simproc_setup simp_bv_land  (\<open>(nat\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_lor\<close>
simproc_setup simp_bv_lor   (\<open>(nat\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_land\<close>


simproc_setup simp_bv_plus_commute2 (\<open>((nat\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)) +\<^sub>b\<^sub>v (nat\<^sub>3 \<Colon> sz)\<close>) = \<open>fn _ =>
  let
    fun proc ctxt ct =
      let 
        val t = Thm.term_of ct;
      in
        (case find_commute_bv_plus_new t of
          (NONE) => NONE
        | (SOME (rhs, quotient)) =>
            SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs))
              (fn _ =>
                 HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
                 HEADGOAL (resolve_tac ctxt [@{thm bv_plus_commute_lessI2}]) THEN 
                 HEADGOAL (resolve_tac ctxt [@{thm bv_plus_inject}]) THEN 
                 HEADGOAL (blast_tac ctxt) THEN
                 unfold_tac ctxt @{thms power_numeral Num.pow.simps Num.sqr.simps} THEN
                 mod_tac ctxt quotient
              )
           )
        )
      end
  in proc end
\<close>


text \<open>Remove this method from the simpset to prevent it interfering\<close>

ML \<open>
fun simp_word goal_target ctxt = (
  SIMPLE_METHOD (
    Local_Defs.unfold_tac ctxt @{thms lor_true lor_false bv_eq bv_leq_same} THEN
    goal_target (asm_simp_tac ((empty_simpset ctxt) 
      addsimprocs [\<^simproc>\<open>simp_bv_plus\<close>, \<^simproc>\<open>simp_bv_minus\<close>, \<^simproc>\<open>simp_bv_plus_commute2\<close>,
                   \<^simproc>\<open>simp_bv_less\<close>, \<^simproc>\<open>simp_bv_eq\<close>, \<^simproc>\<open>simp_bv_lor\<close>,
                   \<^simproc>\<open>simp_bv_land\<close>, \<^simproc>\<open>simp_bv_lsl\<close>, \<^simproc>\<open>simp_bv_lsr\<close>])
    ) THEN
    Local_Defs.unfold_tac ctxt @{thms lor_true lor_false bv_eq bv_leq_same}
  )
)

val method_setup =
  Method.setup \<^binding>\<open>simp_words\<close>
    (Scan.succeed (simp_word HEADGOAL))
    "simplification" #>
  Method.setup \<^binding>\<open>simp_all_words\<close>
    (Scan.succeed (simp_word ALLGOALS))
    "simplification (all goals)";

val _ = 
  Theory.setup method_setup;
\<close>

(*
lemma "(stack \<Colon> 64) +\<^sub>b\<^sub>v (0 \<Colon> 64) = (stack \<Colon> 64)"
  apply simp_words
  ..
*)

lemma "(4 \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64) = (6 \<Colon> 64)"
  apply simp_words
  ..

lemma "(18446744073709551600 \<Colon> 64) +\<^sub>b\<^sub>v (16 \<Colon> 64) = (0 \<Colon> 64)"
  apply simp_words
  ..

lemma "((stack \<Colon> 64) +\<^sub>b\<^sub>v (18446744073709551600 \<Colon> 64)) +\<^sub>b\<^sub>v (16 \<Colon> 64) = (stack \<Colon> 64) +\<^sub>b\<^sub>v (0 \<Colon> 64)"
  apply simp_words
  ..

lemma "stack < 18446744073709551616 ==> ((stack \<Colon> 64) +\<^sub>b\<^sub>v (18446744073709551600 \<Colon> 64)) +\<^sub>b\<^sub>v (16 \<Colon> 64) = (stack \<Colon> 64) +\<^sub>b\<^sub>v (0 \<Colon> 64)"
  apply simp_words
  ..

lemma "((w \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64)) +\<^sub>b\<^sub>v (2 \<Colon> 64) = (w \<Colon> 64) +\<^sub>b\<^sub>v (6 \<Colon> 64)"
  apply simp_words
  ..

lemma \<open>(66818 \<Colon> 64) +\<^sub>b\<^sub>v (18446744073709550376 \<Colon> 64) = (65578 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(4 \<Colon> 64) -\<^sub>b\<^sub>v (4 \<Colon> 64) = (0 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(4 \<Colon> 64) -\<^sub>b\<^sub>v (6 \<Colon> 64) = (18446744073709551614 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(4 \<Colon> 64) -\<^sub>b\<^sub>v (2 \<Colon> 64) = (2 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>((x \<Colon> 64) +\<^sub>b\<^sub>v (66818 \<Colon> 64)) +\<^sub>b\<^sub>v (18446744073709550376 \<Colon> 64) = (x \<Colon> 64) +\<^sub>b\<^sub>v (65578 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(10 \<Colon> 64) =\<^sub>b\<^sub>v (10 \<Colon> 64) = true\<close>
  apply simp_words
  ..

lemma \<open>(42 \<Colon> 64) =\<^sub>b\<^sub>v (10 \<Colon> 64) = false\<close>
  apply simp_words
  ..

lemma \<open>(10 \<Colon> 64) <\<^sub>b\<^sub>v (42 \<Colon> 64) = true\<close>
  apply simp_words
  ..

lemma \<open>(42 \<Colon> 64) <\<^sub>b\<^sub>v (10 \<Colon> 64) = false\<close>
  apply simp_words
  ..

lemma \<open>(42 \<Colon> 64) \<le>\<^sub>b\<^sub>v (10 \<Colon> 64) = false\<close>
  apply simp_words
  ..

lemma \<open>(8 \<Colon> 64) <<\<^sub>b\<^sub>v (8 \<Colon> 64) = (2048 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(8 \<Colon> 64) >>\<^sub>b\<^sub>v (2 \<Colon> 64) = (2 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(0 \<Colon> 64) >>\<^sub>b\<^sub>v (24 \<Colon> 64) = (0 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(8 \<Colon> 64) &\<^sub>b\<^sub>v (2 \<Colon> 64) = (0 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(0 \<Colon> 64) &\<^sub>b\<^sub>v (65280 \<Colon> 64) = (0 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(8 \<Colon> 64) |\<^sub>b\<^sub>v (2 \<Colon> 64) = (10 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(0 \<Colon> 64) |\<^sub>b\<^sub>v (65280 \<Colon> 64) = (65280 \<Colon> 64)\<close>
  apply simp_words
  ..


end
