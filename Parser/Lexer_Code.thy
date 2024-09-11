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
  constant "map" \<rightharpoonup> (SML) "map"
  | constant "rev" \<rightharpoonup> (SML) "rev"
(*  | constant "tl" \<rightharpoonup> (SML) "tl"  THROWS EXCEPTION EMPTY *)

definition
  lexer :: \<open>String.literal \<Rightarrow> AST\<close>
where
  \<open>lexer str = Lexer.lexer (String.explode str)\<close>

ML "String.substring"
(* 
  In order to make our lexer use string literals we need:
   - trim literal
   - takeWhile literal
   - dropWhile literal
   - butlast literal
   - split_not_within literal
*)

(*
lemma [code]: \<open>lexer lit = (
    let
      str = String.explode lit;
      tstr = trim str;
      name = takeWhile isnt_lbracket tstr;
      bargstr = dropWhile isnt_lbracket tstr;
      argstr = butlast (tl bargstr)
    in
      CNode (String.implode name) (map (lexer o String.implode) (split_not_within argstr)))\<close>
  unfolding Let_def CNode_def lexer_def Lexer.lexer.simps[where str = \<open>map String.ascii_of (literal.explode lit)\<close>]
   AST.inject String.explode_implode_eq apply (intro conjI)
  apply auto
  find_theorems String.explode String.implode
  apply (intro AST.inject)


code_datatype CNode
*)
export_code lexer in SML
  module_name AstLexer file_prefix "ast-lexer"


end
