theory Bitvector_Syntax
  imports Main
begin

datatype word = Word (raw_val: nat) (bits: nat) (\<open>(_ \<Colon> _)\<close>)

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
  roll_word :: \<open>word \<Rightarrow> word\<close>
where
  \<open>roll_word w = Word ((raw_val w) mod 2 ^ (bits w)) (bits w)\<close>

fun
  eq_word :: \<open>word \<Rightarrow> word \<Rightarrow> bool\<close>
where
  \<open>eq_word w\<^sub>1 w\<^sub>2 = (((raw_val w\<^sub>1) mod (bits w\<^sub>1)) = ((raw_val w\<^sub>2) mod (bits w\<^sub>2)))\<close>


fun 
  add :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>+\<^sub>b\<^sub>v\<close> 56)
where
  \<open>w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2 = (
    if bits w\<^sub>1 = bits w\<^sub>2 then roll_word (Word (raw_val w\<^sub>1 + raw_val w\<^sub>2) (bits w\<^sub>1))
    else undefined
  )\<close>

consts minus :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>-\<^sub>b\<^sub>v\<close> 56)
consts uminus :: \<open>word \<Rightarrow> word\<close>  (\<open>-\<^sub>b\<^sub>v _\<close> [81] 80)
consts times :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>*\<^sub>b\<^sub>v\<close> 56)
consts divide :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>div\<^sub>b\<^sub>v\<close> 56)
consts sdivide :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>div\<^sub>s\<^sub>b\<^sub>v\<close> 56)
consts mod\<^sub>b\<^sub>v :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>%\<^sub>b\<^sub>v\<close> 56)
consts smod :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>%\<^sub>s\<^sub>b\<^sub>v\<close> 56)
consts lsl :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><<\<^sub>b\<^sub>v\<close> 56)
consts lsr :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>>>\<^sub>b\<^sub>v\<close> 56)
consts asr :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>>>>\<^sub>b\<^sub>v\<close> 56)
consts land :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>&\<^sub>b\<^sub>v\<close> 56)
consts lor :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>|\<^sub>b\<^sub>v\<close> 56)
consts xor :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>xor\<^sub>b\<^sub>v\<close> 56)
abbreviation 
  eq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>=\<^sub>b\<^sub>v\<close> 56) 
where 
  \<open>w\<^sub>1 =\<^sub>b\<^sub>v w\<^sub>2 \<equiv> (if (eq_word w\<^sub>1 w\<^sub>2) then true else false)\<close>
abbreviation neq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<noteq>\<^sub>b\<^sub>v\<close> 56) where "w1 \<noteq>\<^sub>b\<^sub>v w2 \<equiv> (if w1 = w2 then false else true)"
consts leq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<le>\<^sub>b\<^sub>v\<close> 56)
consts sleq :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<le>\<^sub>s\<^sub>b\<^sub>v\<close> 56)
consts le :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>b\<^sub>v\<close> 55)
consts sle :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open><\<^sub>s\<^sub>b\<^sub>v\<close> 55)
consts negation :: \<open>word \<Rightarrow> word\<close> (\<open>~\<^sub>b\<^sub>v _\<close>)
consts concat :: \<open>word \<Rightarrow> word \<Rightarrow> word\<close> (infixr \<open>\<cdot>\<close> 55)
consts extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>ext _ \<sim> hi : _ \<sim> lo : _\<close>)   
consts s_extract_word :: \<open>word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word\<close> (\<open>exts _ \<sim> hi : _ \<sim> lo : _\<close>)

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
