
theory Simp_Word
  imports 
    IsaBIL.Instruction_Syntax 
    Simp_Variables
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

lemma take_bit_numeral_of_Suc_0[simp]: \<open>take_bit (numeral x) (Suc 0) = 1\<close>
  by simp

lemma take_bit_numeral_Numeral1[simp]: \<open>take_bit (numeral n) Numeral1 = 1\<close>
  by simp_all

lemma drop_bit_numeral_Numeral1[simp]: \<open>drop_bit (numeral n) Numeral1 = 0\<close>
  by simp

lemma of_bool_bit_numeral[simp]:
  \<open>of_bool (bit (numeral (num.Bit1 b) ) 0) = 1\<close>
  \<open>of_bool (bit (numeral (num.Bit0 b) ) 0) = 0\<close>
  by simp_all

lemmas simp_words_xtract = xtract.simps word_inject 
   arith_simps  
   diff_zero id_apply 
   take_bit_0 take_bit_of_0 take_bit_numeral_bit0 take_bit_numeral_bit1 take_bit_Suc_bit0
   take_bit_Suc_bit1
   take_bit_numeral_of_Suc_0 take_bit_Suc_from_most take_bit_numeral_Numeral1 

   power_numeral Num.pow.simps One_nat_def diff_numeral_Suc
   pred_numeral_simps   Suc_numeral BitM_plus_one 
   mult_Suc add_Suc_right   power_0
   cancel_comm_monoid_add_class.diff_cancel of_bool_bit_numeral 

   drop_bit_0 drop_bit_of_0 drop_bit_numeral_bit0 drop_bit_numeral_bit1 drop_bit_Suc_bit0 
   drop_bit_Suc_bit1 drop_bit_of_Suc_0 drop_bit_numeral_Numeral1


lemmas simp_words_lsr = bv_lsr.simps word_inject power_numeral Num.pow.simps Num.sqr.simps 
   div_0 arith_simps power_Suc power_0 One_nat_def mult_Suc_right 

lemmas simp_words_xor = bv_xor.simps word_inject xor_nat_numerals xor_numerals numeral_One
            Suc_numeral One_nat_def plus_nat.add_Suc mult_Suc_right
            arith_simps xor.right_neutral xor.left_neutral xor_self_eq
ML \<open>
fun dest_nat (Const ("Groups.zero_class.zero", _)) = 0
  | dest_nat (Const ("Groups.one_class.one", _)) = 1
  | dest_nat (Const ("Nat.Suc", _) $ t) = (dest_nat t) + 1
  | dest_nat (Const ("Num.numeral_class.numeral", Type ("fun", _)) $ t) =
      HOLogic.dest_numeral t
  | dest_nat (Const ("Groups.uminus_class.uminus", Type ("fun", _)) $ t) =
       ~ (dest_nat t)
  | dest_nat t = raise TERM ("dest_number", [t]);

  fun mk_word T tnum tsz = (Const (\<^const_name>\<open>word_constructor\<close>,T) $ tnum $ tsz)

  fun mk_true T = mk_word T HOLogic.Suc_zero HOLogic.Suc_zero
  fun mk_false T = mk_word T HOLogic.zero HOLogic.Suc_zero


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

  fun int_bitwise_op (bop: (word * word) -> word, a: int, b: int) : int =
    let
        val wa = Word.fromInt a
        val wb = Word.fromInt b
        val wx = bop (wa, wb)
    in
        Word.toInt wx
    end;

  fun bitwise_xor (a: int, b: int) : int = int_bitwise_op (Word.xorb, a, b)

  fun word_extract (w: word, start: word, length: word): word =
    let
      val mask = Word.<<(Word.fromInt 1, length) - Word.fromInt 1
      val shifted = Word.>>(w, start)
    in
      Word.andb (shifted, mask)
    end;

  fun bitwise_extract (w: int, start: int, length: int): int = Word.toInt (
    word_extract (Word.fromInt w, Word.fromInt start, Word.fromInt length))

  fun find_commute_bv_plus_new (Const (\<^const_name>\<open>bv_plus\<close>,Tp)
                      $ (Const (\<^const_name>\<open>bv_plus\<close>,_)
                        $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnumo $ _)
                        $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum1 $ _))
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ sz)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val numsz = dest_nat sz
        val sum = num1 + num2
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))

        val wr = Const (\<^const_name>\<open>bv_plus\<close>,Tp)
                  $ (mk_word Tw tnumo sz)
                  $ (mk_word Tw (HOLogic.mk_number HOLogic.natT remainder) sz)
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
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
      in if (num1 < num2) then SOME (mk_true Tw, 0) else SOME (mk_false Tw, 0) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_eq\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ _)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
      in if (num1 = num2) then SOME (mk_true Tw, 0) else SOME (mk_false Tw, 0) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_minus\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val numsz = dest_nat sz
        val sum = (num1 - num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT remainder) sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lsl\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val numsz = dest_nat sz
        val sum = num1 * power (2, num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT remainder) sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lsr\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val sum = (num1 div power (2, num2))
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT sum) sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_plus\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val numsz = dest_nat sz
        val sum = (num1 + num2)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT remainder) sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_land\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val result = bitwise_and (num1, num2)
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT result) sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>succ\<close>,_) 
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum $ sz)) =
    ((fn () =>
      let
        val num = dest_nat tnum
        val numsz = dest_nat sz
        val sum = (num + 1)
        val remainder = sum mod (power (2, numsz))
        val quotient = sum div (power (2, numsz))
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT remainder) sz
      in (SOME (wr, quotient)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_lor\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val result = bitwise_or (num1, num2)
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT result) sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>bv_xor\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum1 $ sz)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,_) $ tnum2 $ _)) =
    ((fn () =>
      let
        val num1 = dest_nat tnum1
        val num2 = dest_nat tnum2
        val result = bitwise_xor (num1, num2)
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT result) sz
      in (SOME (wr, 0)) end) ()
    handle TERM _ =>
      NONE)
    | simp_bv (Const (\<^const_name>\<open>xtract\<close>,_)
                      $ (Const (\<^const_name>\<open>word_constructor\<close>,Tw) $ tnum $ _)
                      $ tszhi $ tszlo) =
    ((fn () =>
      let
        val num = dest_nat tnum
        val szhi = dest_nat tszhi
        val szlo = dest_nat tszlo
        val result = bitwise_extract (num, szlo, szhi + 1)
        val wr = mk_word Tw (HOLogic.mk_number HOLogic.natT result) 
                            (HOLogic.mk_number HOLogic.natT (szhi - szlo + 1))
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
      unfold_tac ctxt @{thms bv_lsl.simps word_inject power_numeral Num.pow.simps Num.sqr.simps Num.mult_num_simps} THEN
      Method.intros_tac ctxt [conjI, thm_for ctxt quotient, refl] [] THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt) THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt)
    ) ctxt

  fun simp_bv_lsr ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms simp_words_lsr} THEN
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

  fun simp_bv_succ ctxt = simproc_bv (fn quotient =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms succ.simps bv_plus.simps word_inject power_numeral Num.pow.simps Num.sqr.simps} THEN
      Method.intros_tac ctxt [conjI, thm_for ctxt quotient, refl] [] THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt) THEN
      HEADGOAL (Lin_Arith.simple_tac ctxt)
    ) ctxt

  fun simp_bv_xor ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms simp_words_xor} THEN
      Method.intros_tac ctxt [conjI, refl] [] THEN
      TRY (HEADGOAL (Lin_Arith.simple_tac ctxt))
    ) ctxt

  fun simp_bv_xtract ctxt = simproc_bv (fn _ =>
      HEADGOAL (resolve_tac ctxt [eq_reflection]) THEN 
      unfold_tac ctxt @{thms simp_words_xtract} THEN
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
(*simproc_setup simp_succ     (\<open>succ (num \<Colon> sz)\<close>) = \<open>K simp_bv_succ\<close>*)
simproc_setup simp_bv_xor   (\<open>(nat\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (nat\<^sub>2 \<Colon> sz)\<close>) = \<open>K simp_bv_xor\<close>
simproc_setup simp_bv_xtract   (\<open>ext num \<Colon> sz \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<close>) = \<open>K simp_bv_xtract\<close>

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

lemma bv_neg_1_bit_simps: \<open>~\<^sub>b\<^sub>v (1 \<Colon> 1) = (0 \<Colon> 1)\<close> \<open>~\<^sub>b\<^sub>v (0 \<Colon> 1) = (1 \<Colon> 1)\<close>
  by auto

lemmas simp_word = minus0 times0 divide0 land0 land_true lor0 lor_true xor0 xor_eq mod0 
                   lsl0 lsr0 asr0 concat0 bv_negation_true_false bv_negation_false_true 
                   lt0 lt_same extracts_0 bv_eq bv_leq_same bv_neg_1_bit_simps (*extract0*)

ML \<open>
fun simp_word goal_target ctxt = (
  SIMPLE_METHOD (
    Local_Defs.unfold_tac ctxt @{thms simp_word} THEN
    goal_target (asm_simp_tac ((empty_simpset ctxt) 
      addsimprocs [\<^simproc>\<open>simp_bv_plus\<close>, \<^simproc>\<open>simp_bv_minus\<close>, \<^simproc>\<open>simp_bv_plus_commute2\<close>,
                   \<^simproc>\<open>simp_bv_less\<close>, \<^simproc>\<open>simp_bv_eq\<close>, \<^simproc>\<open>simp_bv_lor\<close>,
                   \<^simproc>\<open>simp_bv_land\<close>, \<^simproc>\<open>simp_bv_lsl\<close>, \<^simproc>\<open>simp_bv_lsr\<close>,
                   \<^simproc>\<open>simp_bv_xor\<close>, \<^simproc>\<open>simp_bv_xtract\<close> ])
    ) THEN
    Local_Defs.unfold_tac ctxt @{thms simp_word}
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

lemma \<open>(300 \<Colon> 64) <<\<^sub>b\<^sub>v (9 \<Colon> 64) = (153600 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(300 \<Colon> 64) >>\<^sub>b\<^sub>v (55 \<Colon> 64) = 0 \<Colon> 64\<close>
  apply simp_words
  ..

lemma \<open>(100 \<Colon> 64) +\<^sub>b\<^sub>v (Suc 0 \<Colon> 64) = (101 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(47 \<Colon> 64) xor\<^sub>b\<^sub>v (765 \<Colon> 64) = (722 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(ext 0 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = 0 \<Colon> 64\<close>
  apply simp_words
  ..

lemma \<open>(ext 12342353624567534874568 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = 1481839255844843464 \<Colon> 64\<close>
  apply simp_words
  ..


lemma 
    \<open>(ext 1 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = (1 \<Colon> 64)\<close> 
    \<open>(ext 0 \<Colon> 64 \<sim> hi : 0 \<sim> lo : 0) = (0 \<Colon> 1)\<close> 
    \<open>(ext 0 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 63) = (0 \<Colon> 1)\<close>
  apply (simp_words, standard)
  apply (simp_words, standard)
  apply (simp_words, standard)
  done

lemma \<open>(614 \<Colon> 64) >>\<^sub>b\<^sub>v (Suc 0 \<Colon> 64) = (307 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>ext 853 \<Colon> 64 \<sim> hi : 0 \<sim> lo : 0 = 1 \<Colon> 1\<close>
  apply simp_words
  ..

lemma \<open>~\<^sub>b\<^sub>v ext (((((((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64)) >>\<^sub>b\<^sub>v (4 \<Colon> 64)) xor\<^sub>b\<^sub>v ((44 \<Colon> 64)
                         +\<^sub>b\<^sub>v (721 \<Colon> 64))) >>\<^sub>b\<^sub>v (2 \<Colon> 64)) xor\<^sub>b\<^sub>v (((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64)) >>\<^sub>b\<^sub>v
                         (4 \<Colon> 64)) xor\<^sub>b\<^sub>v ((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64))) >>\<^sub>b\<^sub>v (Suc 0 \<Colon> 64)) xor\<^sub>b\<^sub>v
                         (((((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64)) >>\<^sub>b\<^sub>v (4 \<Colon> 64)) xor\<^sub>b\<^sub>v ((44 \<Colon> 64) +\<^sub>b\<^sub>v
                        (721 \<Colon> 64))) >>\<^sub>b\<^sub>v (2 \<Colon> 64)) xor\<^sub>b\<^sub>v (((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64)) >>\<^sub>b\<^sub>v
                       (4 \<Colon> 64)) xor\<^sub>b\<^sub>v ((44 \<Colon> 64) +\<^sub>b\<^sub>v (721 \<Colon> 64)) \<sim> hi : 0 \<sim> lo : 0 = (0 \<Colon> 1)\<close>
  apply simp_words
  ..  

lemma \<open>(16 \<Colon> 64) =\<^sub>b\<^sub>v (16 \<Colon> 64) = true\<close>
  apply simp_words
  ..

lemma \<open>(0 \<Colon> 64) xor\<^sub>b\<^sub>v (1 \<Colon> 64) = (1 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(1 \<Colon> 64) xor\<^sub>b\<^sub>v (0 \<Colon> 64) = 1 \<Colon> 64\<close>
  apply simp_words
  ..

lemma \<open>(1 \<Colon> 64) xor\<^sub>b\<^sub>v (1 \<Colon> 64) = (0 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(1 \<Colon> 64) xor\<^sub>b\<^sub>v (1 \<Colon> 64) = 0 \<Colon> 64\<close>
  apply simp_words
  ..

lemma \<open>(1 \<Colon> 64) xor\<^sub>b\<^sub>v (1 \<Colon> 64) = 0 \<Colon> 64\<close>
  apply simp_words
  ..

lemma \<open>(ext 100 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 0) = (100 \<Colon> 64)\<close>
  apply simp_words
  ..

lemma \<open>(ext 200 \<Colon> 64 \<sim> hi : 63 \<sim> lo : 63) = (0 \<Colon> 1)\<close>
  apply simp_words
  ..

lemma \<open>(712 \<Colon> 64) xor\<^sub>b\<^sub>v (512 \<Colon> 64) = 200 \<Colon> 64\<close>
  apply simp_words
  ..


(*@{thms and_numerals numeral_One and_zero_eq zero_and_eq}*)
(*
lemma \<open>succ (315242 \<Colon> 64) = 315243 \<Colon> 64\<close>
  apply simp_words
  ..  
*)

end
