theory Bitvector_Syntax
  imports Main
begin

datatype word = Word (raw_val: nat) (bits: nat) (\<open>(_ \<Colon> _)\<close>)

fun 
  roll_word :: \<open>word \<Rightarrow> word\<close>
where
  \<open>roll_word w = Word ((raw_val w) mod 2 ^ (bits w)) (bits w)\<close>

text \<open>Print words in hex.\<close>

(* mostly clagged from Num.thy 
typed_print_translation  \<open>
let
  fun dest_num (Const (@{const_syntax Num.Bit0}, _) $ n) = 2 * dest_num n
    | dest_num (Const (@{const_syntax Num.Bit1}, _) $ n) = 2 * dest_num n + 1
    | dest_num (Const (@{const_syntax Num.One}, _)) = 1;

  fun dest_bin_hex_str tm =
  let
    val num = dest_num tm;
    val pre = if num < 10 then "" else "0x"
  in
    pre ^ (Int.fmt StringCvt.HEX num)
  end;

  fun num_tr' sign ctxt T [n] =
    let
      val k = dest_bin_hex_str n;
      val t' = Syntax.const @{syntax_const "_Numeral"} $
        Syntax.free (sign ^ k);
    in
      case T of
        Type (@{type_name fun}, [_, T' as Type("Word.word",_)]) =>
          if not (Config.get ctxt show_types) andalso can Term.dest_Type T'
          then t'
          else Syntax.const @{syntax_const "_constrain"} $ t' $
                            Syntax_Phases.term_of_typ ctxt T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax numeral}, num_tr' "")] end
\<close>*)

fun
  wf_word :: \<open>word \<Rightarrow> bool\<close>
where
  \<open>wf_word (Word val sz) = (val < (2 ^ sz))\<close>

fun
  nat :: \<open>word \<Rightarrow> nat\<close>
where
  \<open>nat (Word val sz) = val mod (2 ^ sz)\<close>

abbreviation
  true :: word
where 
  \<open>true \<equiv> (1 \<Colon> 1)\<close>

abbreviation 
  false :: word
where 
  \<open>false \<equiv> (0 \<Colon> 1)\<close>

fun
  bool_word :: \<open>bool \<Rightarrow> word\<close>
where
  \<open>bool_word b = (if b then true else false)\<close>

fun 
  add :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>+\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun
  minus :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>-\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 - raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun
  uminus :: \<open>word \<Rightarrow> word\<close>  (\<open>-\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>-\<^sub>b\<^sub>v w = (roll_word w)\<close> (*TODO*)

fun 
  times :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>*\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 * raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun 
  divide :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>div\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 div raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun 
  sdivide :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>div\<^sub>s\<^sub>b\<^sub>v\<close> 56) (* TODO*)
where
  \<open>w\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 div raw_val w\<^sub>2) (bits w\<^sub>1)) 
    else undefined
  )\<close>

fun 
  mod\<^sub>b\<^sub>v :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>%\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 mod raw_val w\<^sub>2) (bits w\<^sub>1)) 
    else undefined
  )\<close>

fun 
  smod :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>%\<^sub>s\<^sub>b\<^sub>v\<close> 56) (* TODO *)
where
  \<open>w\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 mod raw_val w\<^sub>2) (bits w\<^sub>1)) 
    else undefined
  )\<close>

fun 
  lsl :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><<\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 <<\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun
  lsr :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>>>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 >>\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun
  asr :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>>>>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 >>>\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun 
  land :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>&\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 &\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun 
  lor :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>|\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 |\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun 
  xor :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>xor\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 xor\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

fun
  eq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>=\<^sub>b\<^sub>v\<close> 56) 
where
  \<open>w\<^sub>1 =\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 = raw_val w\<^sub>2)
    else undefined
  )\<close>

fun
  neq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<noteq>\<^sub>b\<^sub>v\<close> 56) 
where
  \<open>w\<^sub>1 \<noteq>\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 \<noteq> raw_val w\<^sub>2)
    else undefined
  )\<close>

fun
  leq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<le>\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 \<le>\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 \<le> raw_val w\<^sub>2)
    else undefined
  )\<close>

fun
  sleq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<le>\<^sub>s\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 \<le>\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 \<le> raw_val w\<^sub>2)
    else undefined
  )\<close>

fun
  le :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>b\<^sub>v\<close> 55)
where
  \<open>w\<^sub>1 <\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 = raw_val w\<^sub>2)
    else undefined
  )\<close>

fun
  sle :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>s\<^sub>b\<^sub>v\<close> 55)
where
  \<open>w\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then bool_word (raw_val w\<^sub>1 = raw_val w\<^sub>2)
    else undefined
  )\<close>

fun 
  negation :: \<open>word \<Rightarrow> word\<close> (\<open>~\<^sub>b\<^sub>v _\<close>)
where
  \<open>~\<^sub>b\<^sub>v w = w\<close>

fun 
  concat :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<cdot>\<close> 55)
where
  \<open>w\<^sub>1 \<cdot> w\<^sub>2 = roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1 + bits w\<^sub>2))\<close>
(* TODO it is not a w\<^sub>1 + w\<^sub>2 operation *)

fun 
  extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>ext _ \<sim> hi : _ \<sim> lo : _\<close>)
where
  \<open>(ext w \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = Word (raw_val w) (Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w))\<close>

lemma "bits (ext (v \<Colon> 32) \<sim> hi : 32 - 16 - 1 \<sim> lo : 0) = 16"
  by auto


fun 
  s_extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>exts _ \<sim> hi : _ \<sim> lo : _\<close>)
where
  \<open>(exts w \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w) = Word (raw_val w) (Suc (sz\<^sub>h\<^sub>i - sz\<^sub>l\<^sub>o\<^sub>w))\<close>
(* TODO ^^*)

(*
fun
  less_than_word :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = ((num\<^sub>1 + num\<^sub>2) \<Colon> 1)\<close> 

fun
  s_less_than_word :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>s\<^sub>b\<^sub>v\<close> 55)
where
  \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = ((num\<^sub>1 + num\<^sub>2) \<Colon> 1)\<close> 


fun
  bv_negation :: \<open>word \<Rightarrow> word\<close> (\<open>~\<^sub>b\<^sub>v _\<close>)
where
  \<open>~\<^sub>b\<^sub>v (num \<Colon> sz) = (num \<Colon> sz)\<close> 

fun
  concat_word :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<cdot>\<close> 55)
where
  \<open>(num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2) = ((num\<^sub>1 + num\<^sub>2) \<Colon> sz\<^sub>1 + sz\<^sub>2)\<close> 

fun
  extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>ext _ \<sim> hi : _ \<sim> lo : _\<close>)   
where
  \<open>(ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = w\<close>

fun
  s_extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>exts _ \<sim> hi : _ \<sim> lo : _\<close>)   
where
  \<open>(exts w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) = w\<close>
*)


text \<open>Abbreviations\<close>
(*
abbreviation 
  bv_add :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>+\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 \<equiv> w\<^sub>1 + w\<^sub>2\<close>

abbreviation 
  bv_minus :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>-\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2 \<equiv> w\<^sub>1 - w\<^sub>2\<close>

abbreviation       
  bv_uminus :: \<open>word \<Rightarrow> word\<close>  (\<open>-\<^sub>b\<^sub>v _\<close> [81] 80)
where
  \<open>-\<^sub>b\<^sub>v w \<equiv> - w\<close>

abbreviation 
  bv_times :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>*\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2 \<equiv> w\<^sub>1 * w\<^sub>2\<close>

abbreviation 
  bv_divide :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>div\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2 \<equiv> w\<^sub>1 div w\<^sub>2\<close>

abbreviation 
  bv_mod\<^sub>b\<^sub>v :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>%\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2 \<equiv> w\<^sub>1 mod w\<^sub>2\<close>
*)
end
