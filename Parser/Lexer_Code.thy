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


(*code_datatype CNode*)

export_code lexer in SML
  module_name AstLexer file_prefix "ast-lexer"


end
