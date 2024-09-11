theory Syntax
  imports "Prelims/Prelims"
           "/home/griff/Isabelle2024/src/HOL/ex/Sketch_and_Explore" (*TODO remove*)
begin
(*
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
*)
class bil_ops = plus + minus + modulo + times + divide + uminus + (*bool_syntax +*)
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
      and le :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>le\<close> 65)
      and slt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>slt\<close> 65)
      and sle :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>sle\<close> 65)
  assumes inject[simp]: 
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. e\<^sub>1 + e\<^sub>2 = e\<^sub>3 + e\<^sub>4 \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close> 
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. e\<^sub>1 - e\<^sub>2 = e\<^sub>3 - e\<^sub>4 \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close> 
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. e\<^sub>1 mod e\<^sub>2 = e\<^sub>3 mod e\<^sub>4 \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close> 
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 >> e\<^sub>2 = e\<^sub>3 >> e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>   
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 << e\<^sub>2 = e\<^sub>3 << e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 >>> e\<^sub>2 = e\<^sub>3 >>> e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close> 
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 && e\<^sub>2 = e\<^sub>3 && e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 || e\<^sub>2 = e\<^sub>3 || e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>   
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 xor e\<^sub>2 = e\<^sub>3 xor e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 sdiv e\<^sub>2 = e\<^sub>3 sdiv e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>   
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 smod e\<^sub>2 = e\<^sub>3 smod e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 lt e\<^sub>2 = e\<^sub>3 lt e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>   
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 le e\<^sub>2 = e\<^sub>3 le e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 slt e\<^sub>2 = e\<^sub>3 slt e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>   
      \<open>\<And>e\<^sub>3 e\<^sub>4 e\<^sub>1 e\<^sub>2. (e\<^sub>1 sle e\<^sub>2 = e\<^sub>3 sle e\<^sub>4) \<longleftrightarrow> (e\<^sub>1 = e\<^sub>3 \<and> e\<^sub>2 = e\<^sub>4)\<close>

abbreviation (input)
  ge  (infix \<open>ge\<close> 50)
  where \<open>x ge y \<equiv> y le x\<close>

abbreviation (input)
  gt  (infix \<open>gt\<close> 50)
  where \<open>x gt y \<equiv> y lt x\<close>

abbreviation (input)
  sge  (infix \<open>sge\<close> 50)
  where \<open>x sge y \<equiv> y sle x\<close>

abbreviation (input)
  sgt  (infix \<open>sgt\<close> 50)
  where \<open>x sgt y \<equiv> y slt x\<close>

abbreviation (input)
  mod_percent (infix \<open>%\<close> 50)
  where \<open>x % y \<equiv> x mod y\<close>


end