theory Syntax
  imports Prelims
begin

class bool_syntax =
    fixes true :: 'a and false :: 'a
  assumes true_neq_false[simp]: \<open>true \<noteq> false\<close>
begin

lemma bool_syntax_exhaust:
  obtains 
    (True) \<open>b = true\<close>
  | (False) \<open>b = false\<close>
  | (NotBool) \<open>b \<noteq> false \<and> b \<noteq> true\<close>
  by force

end

lemma not_true_eq_false[simp]: \<open>\<not> false = true\<close>
  using true_neq_false by metis

class bil_ops = plus + minus + modulo + times + divide + uminus + bool_syntax +
    fixes lsr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>>>\<close> 65)
      and lsl :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open><<\<close> 65)
      and asr :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>>>>\<close> 64)
      and land :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>&&\<close> 65)
      and lor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>||\<close> 65)
      and xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>xor\<close> 65)
      and sdivide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>sdiv\<close> 56)
      and smod :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>smod\<close> 56)
      and negation :: \<open>'a \<Rightarrow> 'a\<close>
      and lt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>lt\<close> 65)
      and lteq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>lteq\<close> 65)
      and slt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>slt\<close> 65)
      and slteq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>slteq\<close> 65)

abbreviation (input)
  gteq  (infix \<open>gteq\<close> 50)
  where \<open>x gteq y \<equiv> y lteq x\<close>

abbreviation (input)
  gt  (infix \<open>gt\<close> 50)
  where \<open>x gt y \<equiv> y lt x\<close>

abbreviation (input)
  sgteq  (infix \<open>sgteq\<close> 50)
  where \<open>x sgteq y \<equiv> y slteq x\<close>

abbreviation (input)
  sgt  (infix \<open>sgt\<close> 50)
  where \<open>x sgt y \<equiv> y slt x\<close>

abbreviation (input)
  mod_percent (infix \<open>%\<close> 50)
  where \<open>x % y \<equiv> x mod y\<close>


end