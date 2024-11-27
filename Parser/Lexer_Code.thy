theory Lexer_Code
  imports Lexer
      "HOL-Library.Code_Abstract_Char"
      "HOL-Library.Code_Target_Numeral"
      (*"HOL-Library.Code_Binary_Nat"*)
begin

(* For debugging *)


definition
  CNode  :: \<open>String.literal \<Rightarrow> AST list \<Rightarrow> AST\<close> 
where 
  \<open>CNode str ast = Node (String.explode str) ast\<close>

code_printing
  constant "rev" \<rightharpoonup> (SML) "rev"
(*  | constant "tl" \<rightharpoonup> (SML) "tl"  THROWS EXCEPTION EMPTY *)

definition
  lexer :: \<open>String.literal \<Rightarrow> AST\<close>
where
  \<open>lexer str = Lexer.lexer (String.explode str)\<close>

(* 
  In order to make our lexer use string literals we need:
   - trim literal
   - takeWhile literal
   - dropWhile literal
   - butlast literal
   - split_not_within literal
*)

lemma [code]:
  \<open>if_hd_eq c' P Q (c # cs) = (if c = c' then P (c # cs) else Q (c # cs))\<close>
  \<open>if_hd_eq c P Q [] = Q []\<close>
  by auto

lemma explode_comp_implode[simp]: \<open>literal.explode \<circ> String.implode = map String.ascii_of\<close>
  unfolding comp_def by auto

lemma f_explode_comp_implode: \<open>f \<circ> literal.explode \<circ> String.implode = f \<circ> map String.ascii_of\<close>
  unfolding comp_def by auto

lemma ascii_of_trim[simp]: "map String.ascii_of (trim (map String.ascii_of xs)) = trim (map String.ascii_of xs)"
  apply auto
  by (smt (verit, ccfv_threshold) String.implode_explode_eq dropWhile_map implode.rep_eq rev_map)

lemma ascii_of_explode_trim[simp]: "map String.ascii_of (trim (literal.explode lit)) = trim (literal.explode lit)"
  using ascii_of_trim 
  by (metis String.implode_explode_eq implode.rep_eq)

lemma ascii_of_insert_hd: \<open>map (map String.ascii_of) (insert_hd x xs) = (insert_hd (String.ascii_of x) (map (map String.ascii_of) xs))\<close>
  by (cases xs, auto) 

lemma map_ascii_of_split_not_within_int: \<open>map (map String.ascii_of) (split_not_within_int (map String.ascii_of xs) i) =
    split_not_within_int (map String.ascii_of xs) i\<close>
proof (induct xs arbitrary: i)
  case (Cons a xs)
  show ?case 
    apply simp
    apply (cases \<open>a = CHR ''(''\<close>)
    apply simp
    unfolding ascii_of_insert_hd
    using Cons apply simp
    apply (cases \<open>a = CHR '')''\<close>)
    apply simp
    unfolding ascii_of_insert_hd
    using Cons apply simp
    apply (cases \<open>a = CHR '',''\<close>)
    apply (cases \<open>i = 0\<close>)
    apply simp
    using Cons apply simp
    apply simp
    unfolding ascii_of_insert_hd
    using Cons apply simp
    by (smt (z3) ascii_of_ascii_of ascii_of_insert_hd list.inject list.simps(8) list.simps(9) local.Cons split_not_within_int.elims)
qed auto   

lemma map_ascii_of_split_not_within: \<open>map (map String.ascii_of) (split_not_within (map String.ascii_of xs)) =
    split_not_within (map String.ascii_of xs)\<close>
  unfolding split_not_within.simps by (rule map_ascii_of_split_not_within_int)

lemma ascii_of_if_hd_eq: \<open>map String.ascii_of (if_hd_eq x f g xs) = (if_hd_eq x (map String.ascii_of o f) (map String.ascii_of o g) xs)\<close>
proof (induct xs)
  case (Cons x' xs)
  show ?case 
    by (cases \<open>x = x'\<close>, simp_all)
qed simp



lemma XXXXXX:
    shows \<open>if_hd_eq c f g (trim (literal.explode xs)) =
           if_hd_eq c (f o map String.ascii_of) (g \<circ> map String.ascii_of) (trim (literal.explode xs))\<close>
  using ascii_of_explode_trim[symmetric]
  using comp_apply if_hd_eq.elims if_hd_eq.simps(3) list.inject
  by (smt (verit) )

lemma if_hd_eq_comp_eq:
  \<open>if_hd_eq x (f o g) (f \<circ> h) xs = f (if_hd_eq x g h xs)\<close>
proof (cases xs)
  case (Cons x' xs)
  thus ?thesis by (cases \<open>x = x'\<close>, simp_all)
qed simp

lemma if_hd_eq_inject: 
  assumes \<open>x = x'\<close> \<open>f = f'\<close> \<open>g = g'\<close> \<open>xs = xs'\<close>
    shows \<open>if_hd_eq x f g xs = if_hd_eq x' f' g' xs'\<close>
  unfolding assms ..

lemma split_not_withinI:
  assumes \<open>x = map String.ascii_of x'\<close> \<open>y = map String.ascii_of y'\<close>
      and \<open>x' = y'\<close>
    shows \<open>split_not_within x = map (map String.ascii_of) (split_not_within y)\<close>
  using map_ascii_of_split_not_within[symmetric, of y'] unfolding assms .

lemma dropWhile_map_comp: \<open>dropWhile f \<circ> map g = map g \<circ> dropWhile (f o g)\<close>
  unfolding comp_def dropWhile_map ..

lemma map_comp_empty[simp]: \<open>map f \<circ> (\<lambda>_. []) = (\<lambda>_. [])\<close> \<open>(\<lambda>_. []) \<circ> map f = (\<lambda>_. [])\<close>
  by fastforce+

lemma [code]: \<open>lexer lit = (
    let
      str = String.explode lit;
      tstr = trim str;
      name = if_hd_eq CHR 0x22 id (takeWhile (isnt_lbracket \<circ> String.ascii_of)) tstr;
      bargstr = if_hd_eq CHR 0x22 (\<lambda>_. []) (dropWhile (isnt_lbracket \<circ> String.ascii_of)) tstr;
      argstr = butlast (tl bargstr)
    in
      CNode (String.implode name) (map (lexer o String.implode) (split_not_within argstr)))\<close>
unfolding Let_def CNode_def lexer_def Lexer.lexer.simps[where str = \<open>literal.explode lit\<close>]
   AST.inject String.explode_implode_eq 
sketch (intro conjI)
proof (intro conjI)
  have ascii_of_takeWhile_lbracket:  \<open>map String.ascii_of \<circ> (takeWhile (isnt_lbracket \<circ> String.ascii_of)) =
        takeWhile isnt_lbracket \<circ> (map String.ascii_of)\<close>
    using takeWhile_map[where f = String.ascii_of and P = isnt_lbracket,symmetric] by fastforce
  show "if_hd_eq CHR 0x22 id (takeWhile isnt_lbracket) (trim (literal.explode lit)) = map String.ascii_of (if_hd_eq CHR 0x22 id (takeWhile (isnt_lbracket \<circ> String.ascii_of)) (trim (literal.explode lit)))"
    unfolding ascii_of_if_hd_eq
    unfolding ascii_of_takeWhile_lbracket
    apply (subst XXXXXX)
    unfolding id_o o_id ..
next
  have ascii_of2: \<open>isnt_lbracket \<circ> String.ascii_of = isnt_lbracket \<circ> String.ascii_of \<circ> String.ascii_of\<close>
    by fastforce
  have ascii_of_empty: \<open>(\<lambda>_. []) \<circ> map String.ascii_of = map String.ascii_of \<circ> (\<lambda>_. [])\<close>
    by fastforce
  show "map Lexer.lexer (split_not_within (butlast (tl (if_hd_eq CHR 0x22 (\<lambda>_. []) (dropWhile isnt_lbracket) (trim (literal.explode lit)))))) =
        map ((\<lambda>str. Lexer.lexer (literal.explode str)) \<circ> String.implode) (split_not_within (butlast (tl (if_hd_eq CHR 0x22 (\<lambda>_. []) (dropWhile (isnt_lbracket \<circ> String.ascii_of)) (trim (literal.explode lit))))))"
    unfolding comp_def[symmetric] f_explode_comp_implode map_map[symmetric]
    apply (rule arg_cong[where f = \<open>map Lexer.lexer\<close>])
    (*apply (rule split_not_withinI)*)
    apply (subst XXXXXX)
    unfolding dropWhile_map_comp ascii_of_empty if_hd_eq_comp_eq map_butlast[symmetric] 
              map_tl[symmetric]
    apply (subst map_ascii_of_split_not_within[symmetric])
    apply (rule arg_cong[where f = \<open>map (map String.ascii_of)\<close>])
    apply (rule arg_cong[where f = split_not_within])
    unfolding map_butlast apply (rule arg_cong[where f = butlast])
    unfolding map_tl apply (rule arg_cong[where f = tl])
    unfolding if_hd_eq_comp_eq[symmetric, where f = \<open>map String.ascii_of\<close>]
    apply (subst XXXXXX[where g = \<open>dropWhile (isnt_lbracket \<circ> String.ascii_of)\<close>])
    apply (rule if_hd_eq_inject)
    unfolding map_comp_empty 
    apply standard
    apply standard
    apply (metis ascii_of2 dropWhile_map_comp)
    ..
qed

code_datatype CNode

export_code lexer in SML
  module_name AstLexer file_prefix "ast-lexer"


end
