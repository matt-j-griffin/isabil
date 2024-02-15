theory ADT_Lexer_Code
  imports ADT_Lexer
begin

text \<open>Code Generation for ADT_Lexer\<close>

definition \<open>parse_ast str = parse_string (String.explode str)\<close> 

lemma [code]: \<open>parse_en (Node en ast) = (
  if en = ''LittleEndian'' then
    case ast of [] \<Rightarrow> Value el
    | x # xs \<Rightarrow> Error ''Expecting no arguments for type "LittleEndian", got many.''
  else if en = ''BigEndian'' then
    case ast of [] \<Rightarrow> Value be
    | x # xs \<Rightarrow> Error ''Expecting no arguments for type "BigEndian", got many.''
  else Error (List.append ''Expecting either BigEndian or LittleEndian but received: '' en)
  )\<close>
  by (cases ast, simp_all split: if_splits)

lemma [code]: \<open>parse_typ (Node typ ast) = (
  if typ = ''Imm'' then
    if (length ast = 1) then map_result_value Imm (parse_nat (ast ! 0))
    else Error ''Expecting 1 argument for type "Imm", got many.''
  else if typ = ''Mem'' then
    if (length ast = 2) then  map_result_value2 Mem (parse_nat (ast ! 0)) (parse_nat (ast ! 1))
    else Error ''Expecting 2 arguments for type "Mem", got many.''
  else Error (List.append ''Expecting either Imm or Mem but received: '' typ)
  )\<close>
  apply (split if_splits, safe)
  subgoal by (cases ast rule: length1_cases, auto)
  subgoal by (cases ast rule: length2_cases, auto)
  .

definition 
  CVar :: \<open>String.literal \<Rightarrow> Type \<Rightarrow> var\<close> 
where
  \<open>CVar str t = Var (String.explode str)  t\<close>

lemma [code]: \<open>parse_var (Node var ast) = (
  if var = ''Var'' then
    if (length ast = 2) then map_result_value2 CVar (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1))
    else Error ''Expecting 2 arguments for type "Var", got many.''
  else Error (List.append ''Expecting "Var" but received: '' var)
  )\<close>
  unfolding CVar_def apply (split if_splits, safe)
  subgoal 
    apply (cases ast rule: length2_cases, auto)
    subgoal for str t
      apply (cases str rule: parse_str.cases, auto)
      by (cases \<open>parse_typ t\<close>, auto)
    .
  by auto

code_datatype CVar 


definition
  CUnknown :: \<open>String.literal \<Rightarrow> Type \<Rightarrow> val\<close> 
where
  \<open>CUnknown str t = Unknown (String.explode str)  t\<close>

lemma [code]: \<open>parse_exp (Node e ast) = (
  if e = ''Var'' then map_result_value EVar (parse_var (Node ''Var'' ast))
  else if e = ''Store'' then
    if (length ast = 5) then map_result_value5 Store (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 3)) (parse_nat (ast ! 4)) (parse_exp (ast ! 2))
    else Error ''Expecting 5 arguments for type "Store", got many.''
  else if e = ''Load'' then
    if (length ast = 4) then map_result_value4 Load (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 2)) (parse_nat (ast ! 3))
    else Error ''Expecting 4 arguments for type "Load", got many.''
  else if e = ''Let'' then
    if (length ast = 3) then map_result_value3 Let (parse_var (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error ''Expecting 3 arguments for type "Let", got many.''
  else if e = ''Ite'' then
    if (length ast = 3) then map_result_value3 Ite (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error ''Expecting 3 arguments for type "Ite", got many.''
  else if e = ''Extract'' then
    if (length ast = 3) then map_result_value3 Extract (parse_nat (ast ! 0)) (parse_nat (ast ! 1)) (parse_exp (ast ! 2))
    else Error ''Expecting 3 arguments for type "Extract", got many.''
  else if e = ''Int'' then
    if (length ast = 2) then map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat (ast ! 0)) (parse_nat (ast ! 1))))
    else Error ''Expecting 2 arguments for type "Int", got many.''
  else if e = ''Unknown'' then
    if (length ast = 2) then map_result_value Val (map_result_value2 CUnknown (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1)))
    else Error ''Expecting 2 arguments for type "Unknown", got many.''
  else if e = ''SLE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Sle) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "SLE", got many.''
  else if e = ''SLT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Slt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "SLT", got many.''
  else if e = ''MINUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Minus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "MINUS", got many.''
  else if e = ''TIMES'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Times) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "TIMES", got many.''
  else if e = ''DIVIDE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Divide) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "DIVIDE", got many.''
  else if e = ''XOR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Xor) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "XOR", got many.''
  else if e = ''OR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Or) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "OR", got many.''
  else if e = ''AND'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp And) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "AND", got many.''
  else if e = ''LT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Lt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "LT", got many.''
  else if e = ''LE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Le) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "LE", got many.''
  else if e = ''NEQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Neq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "NEQ", got many.''
  else if e = ''PLUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Plus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "PLUS", got many.''
  else if e = ''EQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "EQ", got many.''
  else if e = ''RSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp RShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "RSHIFT", got many.''
  else if e = ''ARSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp ARShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "ARSHIFT", got many.''
  else if e = ''LSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp LShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "LSHIFT", got many.''
  else if e = ''LOW'' then
    if (length ast = 2) then map_result_value2 (Cast Low) (parse_nat (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "LOW", got many.''
  else if e = ''HIGH'' then
    if (length ast = 2) then map_result_value2 (Cast High) (parse_nat (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "HIGH", got many.''
  else if e = ''UNSIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Unsigned) (parse_nat (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "UNSIGNED", got many.''
  else if e = ''SIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Signed) (parse_nat (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "SIGNED", got many.''
  else if e = ''Concat'' then
    if (length ast = 2) then map_result_value2 Concat (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error ''Expecting 2 arguments for type "Concat", got many.''
  else if e = ''NOT'' then
    if (length ast = 1) then map_result_value (UnOp Not) (parse_exp (ast ! 0))
    else Error ''Expecting 1 argument for type "NOT", got many.''
  else if e = ''NEG'' then
    if (length ast = 1) then map_result_value (UnOp Neg) (parse_exp (ast ! 0))
    else Error ''Expecting 1 argument for type "NEG", got many.''
  else Error (List.append ''Expecting either "Store", "Load", "Var", "Let",
           "Int", "Unknown", "NOT", "NEG", "SLE", "SLT", "MINUS", "TIMES", "DIVIDE", "XOR", "OR",
           "AND", "LT", "LE", "NEQ", "PLUS", "EQ", "RSHIFT", "ARSHIFT", "LSHIFT", "LOW", "HIGH",
           "UNSIGNED", "SIGNED", "Ite", "Concat", "Extract" but received: '' e)
  )\<close>
  apply (split if_splits, safe)
  subgoal by simp
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(2) by (cases ast rule: length5_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(3) by (cases ast rule: length4_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(4) by (cases ast rule: length3_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(5) apply clarify by (cases ast rule: length3_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(6) apply clarify by (cases ast rule: length3_cases, simp_all)
 
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(7) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(8) apply clarify 
    unfolding CUnknown_def 
    apply (cases ast rule: length2_cases, simp_all)
    subgoal for str t
      apply (cases str rule: parse_str.cases, auto)
      by (cases \<open>parse_typ t\<close>, auto)
    .
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(9) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(10) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(11) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(12) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(13) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(14) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(15) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(16) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(17) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(18) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(19) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(20) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(21) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(22) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(23) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(24) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(25) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(26) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(27) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(28) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(29) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(30) apply clarify by (cases ast rule: length1_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(31) apply clarify by (cases ast rule: length1_cases, simp_all)  
  by simp
  
code_datatype CUnknown Immediate Storage


definition
  CSpecial :: \<open>String.literal \<Rightarrow> stmt\<close> 
where
  \<open>CSpecial str = Special (String.explode str) \<close>


lemma [code]: \<open>parse_stmt (Node stmt ast) = (
    if stmt = ''Move'' then
      if (length ast = 2) then map_result_value2 Move (parse_var (ast ! 0)) (parse_exp (ast ! 1))
      else Error ''Expecting 2 arguments for type "Move", got many.''
    else if stmt = ''Jmp'' then
      if (length ast = 1) then map_result_value Jmp (parse_exp (ast ! 0))
      else Error ''Expecting 1 argument for type "Jmp", got many.''
    else if stmt = ''CpuExn'' then
      if (length ast = 1) then map_result_value CpuExn (parse_int (ast ! 0))
      else Error ''Expecting 1 argument for type "CpuExn", got many.''
    else if stmt = ''Special'' then
      if (length ast = 1) then map_result_value CSpecial (map_result_value String.implode (parse_str (ast ! 0)))
      else Error ''Expecting 1 argument for type "Special", got many.''
    else if stmt = ''While'' then
      if (length ast = 2) then map_result_value2 While (parse_exp (ast ! 0)) (parse_bil (ast ! 1))
      else Error ''Expecting 2 arguments for type "While", got many.''
    else if stmt = ''If'' then
      if (length ast = 3) then map_result_value3 If (parse_exp (ast ! 0)) (parse_bil (ast ! 1)) (parse_bil (ast ! 2))
      else Error ''Expecting 3 arguments for type "If", got many.''
    else
       Error (List.append ''Expecting either "Move", "Jmp", "CpuExn", "Special", "While", "If" but received: '' stmt)
)\<close>
  unfolding CSpecial_def
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(1) apply clarify by (cases ast rule: length2_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(2) apply clarify by (cases ast rule: length1_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(3) apply clarify by (cases ast rule: length1_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(4) apply clarify apply (cases ast rule: length1_cases, simp_all)
    subgoal for str
      by (cases str rule: parse_str.cases, auto)
    .
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(5) apply clarify by (cases ast rule: length2_cases, simp_all)
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(6) apply clarify by (cases ast rule: length3_cases, simp_all)
  by simp

code_datatype CSpecial CpuExn While Move Jmp stmt.If

export_code parse_ast in SML
  module_name AstParser file_prefix "ast-parser"

text \<open>Reflect the AST parser into the current Isabelle/HOL session\<close>

(* A lot of optimisation work remains here. The conversion functions are a code smell that need 
   to be resolved *)

code_reflect AstParser
  datatypes BinOp = AOp | LOp
        and Endian = BigEndian | LittleEndian 
        and Cast = Low | High | Signed | Unsigned 
        and LOp = Eq | Neq | Lt | Le | Slt | Sle
        and AOp = Plus | Minus | Times | Divide | SDivide | Mod | SMod | And | Or | Xor | LShift | RShift | ARShift
        and UnOp = Neg | Not 
        and exp = UnOp | BinOp | Store | Load | Concat | Extract | Val | EVar | Cast | Let | Ite
        and stmt = Move | While | If | Jmp | CpuExn | CSpecial
        and Type = Imm | Mem
        and val = Immediate | CUnknown | Storage
        and word = Word
        and var = CVar
        and result = Value | Error
  functions parse_ast integer_of_int integer_of_nat nat_of_integer int_of_integer integer_of_char

ML_file \<open>isabil2.ml\<close>

end
