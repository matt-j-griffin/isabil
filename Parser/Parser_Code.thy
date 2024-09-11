theory Parser_Code
  imports Parser 
    Lexer_Code 
begin

text \<open>Code Generation for ADT Parser\<close>

lemma implode_Nil[simp]: \<open>String.implode [] = STR ''''\<close>
  by (metis String.implode_explode_eq zero_literal.rep_eq)

lemma cons_literal_abs_eq:
  assumes \<open>eq_onp (\<lambda>cs. \<forall>c\<in>set cs. \<not> digit7 c) xs xs\<close>
      and \<open>eq_onp (\<lambda>cs. \<forall>c\<in>set cs. \<not> digit7 c) [x] [x]\<close>
    shows "literal.Abs_literal (x # xs) = literal.Abs_literal [x] + literal.Abs_literal xs"
  using assms by (simp add: plus_literal.abs_eq)

lemma implode_append:  "String.implode (xs @ ys) = String.implode xs + String.implode ys"
  by (metis implode.rep_eq literal.explode_inverse map_append plus_literal.rep_eq)

lemma implode_Cons: "String.implode (x # xs) = literal.Abs_literal [String.ascii_of x] + String.implode xs"
  using implode_append append_Cons append_Nil
  by (metis Cons_eq_map_conv implode.abs_eq list.simps(8))

lemma implode_Char_Cons: "String.implode ((Char c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4 c\<^sub>5 c\<^sub>6 c\<^sub>7 False) # str) = String.Literal c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4 c\<^sub>5 c\<^sub>6 c\<^sub>7 (String.implode str)"
  by (metis Literal.rep_eq String.implode_explode_eq implode_Cons)

lemma Literal_inject:
  assumes \<open>x1 = y1\<close> \<open>x2 = y2\<close> \<open>x3 = y3\<close> \<open>x4 = y4\<close> \<open>x5 = y5\<close> \<open>x6 = y6\<close> \<open>x7 = y7\<close> \<open>xs = ys\<close>
    shows \<open>String.Literal x1 x2 x3 x4 x5 x6 x7 xs = String.Literal y1 y2 y3 y4 y5 y6 y7 ys\<close>
  using assms by auto

lemma Literal_plus: \<open>String.Literal x1 x2 x3 x4 x5 x6 x7 (str1 + str2) = String.Literal x1 x2 x3 x4 x5 x6 x7 str1 + str2\<close>
  by (metis Literal.rep_eq append_Cons literal.explode_inject plus_literal.rep_eq)

definition of_string_radix_error_to_string where
  \<open>of_string_radix_error_to_string \<equiv> String.implode o AST_Prelims.of_string_radix_error_to_string\<close>

(* TODO remove String.implode on char *)
lemma [code]:
  \<open>of_string_radix_error_to_string EmptyString = STR ''Cannot convert empty string''\<close>
  \<open>of_string_radix_error_to_string (InvalidRadix z) = STR ''The provided radix was too large (max 32)''\<close>
  \<open>of_string_radix_error_to_string (InvalidCodepoint c z) = STR ''Codepoint out of range for radix: '' + String.implode [c]\<close>
  unfolding of_string_radix_error_to_string_def apply auto
  unfolding implode_Char_Cons implode_Nil apply presburger+
  unfolding implode_Cons apply auto
  sorry

definition 
  join :: \<open>String.literal list \<Rightarrow> String.literal\<close>
where 
  \<open>join lst \<equiv> String.implode (Parser.join (map String.explode lst))\<close>

lemma [code]:
  \<open>join [] = STR ''''\<close>
  \<open>join (s # ss) = s + STR '', '' + join ss\<close>
  unfolding join_def apply auto
  unfolding implode_append String.implode_explode_eq
  using Literal_plus add.assoc add_0 implode_Char_Cons 
  by (metis (no_types, lifting))

definition \<open>CParseArgumentError = ParseArgumentError o String.explode\<close>
definition \<open>CParseTagInvalid strs str = ParseTagInvalid (map String.explode strs) (String.explode str)\<close>
definition \<open>CStringMustBeQuoted \<equiv> StringMustBeQuoted o String.explode\<close>
definition \<open>CTagExistsError \<equiv> TagExistsError o String.explode\<close>
definition \<open>CInvalidAdtInsn \<equiv> InvalidAdtInsn o (map String.explode)\<close>
definition \<open>CInvalidAdtFunction \<equiv> InvalidAdtFunction o (map String.explode)\<close>

definition
  parse_error_to_string :: \<open>ParseError \<Rightarrow> String.literal\<close>
  where
  \<open>parse_error_to_string \<equiv> String.implode o Parser.parse_error_to_string\<close>

lemma [code]:
  \<open>parse_error_to_string (ParseNatError en) = of_string_radix_error_to_string en\<close>
  \<open>parse_error_to_string (ParseIntError ei) = of_string_radix_error_to_string ei\<close>
  \<open>parse_error_to_string (CParseArgumentError str expected actual) = STR ''Expecting X arguments for "'' + str + STR ''", got: Y''\<close>
  \<open>parse_error_to_string (CStringMustBeQuoted str) = STR ''Expecting string wrapped in quotes, received: '' + str\<close>
  \<open>parse_error_to_string (CParseTagInvalid strs str) = STR ''Expecting one of ['' + (join strs) + STR ''], but received: '' + str\<close>
  \<open>parse_error_to_string (CTagExistsError str) = STR ''Expecting empty string before brackets, received: '' + str\<close>
  \<open>parse_error_to_string (CInvalidAdtInsn strs) = STR ''Expecting adt insn translation to contain two or three lines: ['' + (join strs) + STR '']''\<close>
  \<open>parse_error_to_string (CInvalidAdtFunction strs) = STR ''Expecting adt function to contain at least two lines: ['' + (join strs) + STR '']''\<close>
  unfolding parse_error_to_string_def CParseArgumentError_def CStringMustBeQuoted_def of_string_radix_error_to_string_def
            CParseTagInvalid_def CTagExistsError_def CInvalidAdtInsn_def CInvalidAdtFunction_def 
  apply auto
  unfolding implode_Nil implode_Char_Cons implode_append String.implode_explode_eq Literal_plus[symmetric]
  apply auto
  unfolding Parser_Code.join_def[symmetric]
  apply auto
  by (simp add: \<open>\<And>x7 x6 x5 x4 x3 x2 x1 str2 str1. String.Literal x1 x2 x3 x4 x5 x6 x7 str1 + str2 = String.Literal x1 x2 x3 x4 x5 x6 x7 (str1 + str2)\<close> add.assoc)

find_theorems String.Literal Char
definition \<open>parse_ast str = parse_adt_program (map String.explode str)\<close> 

text \<open>parse_en\<close>

lemma [code]: \<open>parse_en (Node en ast) = (
  if en = ''LittleEndian'' then
    case ast of [] \<Rightarrow> Value el
    | x # xs \<Rightarrow> Error (ParseArgumentError (''LittleEndian'') 0 (length (x # xs)))
  else if en = ''BigEndian'' then
    case ast of [] \<Rightarrow> Value be
    | x # xs \<Rightarrow> Error (ParseArgumentError (''BigEndian'') 0 (length (x # xs)))
  else Error (ParseTagInvalid [''BigEndian'', ''LittleEndian''] en)
  )\<close>
  by (cases ast, simp_all split: if_splits)

lemma [code]: \<open>parse_typ (Node typ ast) = (
  if typ = ''Imm'' then
    if (length ast = 1) then map_result_value Imm (parse_nat_dec (ast ! 0))
    else Error (ParseArgumentError ''Imm'' 1 (length ast))
  else if typ = ''Mem'' then
    if (length ast = 2) then  map_result_value2 Mem (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1))
    else Error (ParseArgumentError ''Mem'' 2 (length ast))
  else Error (ParseTagInvalid [''Imm'', ''Mem''] typ)
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
    else Error (ParseArgumentError ''Var'' 2 (length ast))
  else Error (ParseTagInvalid [''Var''] var)
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
    if (length ast = 5) then map_result_value5 Store (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 3)) (parse_nat_dec (ast ! 4)) (parse_exp (ast ! 2))
    else Error (ParseArgumentError ''Store'' 5 (length ast))
  else if e = ''Load'' then
    if (length ast = 4) then map_result_value4 Load (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 2)) (parse_nat_dec (ast ! 3))
    else Error (ParseArgumentError ''Load'' 4 (length ast))
  else if e = ''Let'' then
    if (length ast = 3) then map_result_value3 Let (parse_var (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error (ParseArgumentError ''Let'' 3 (length ast))
  else if e = ''Ite'' then
    if (length ast = 3) then map_result_value3 Ite (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error (ParseArgumentError ''Ite'' 3 (length ast))
  else if e = ''Extract'' then
    if (length ast = 3) then map_result_value3 Extract (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1)) (parse_exp (ast ! 2))
    else Error (ParseArgumentError ''Extract'' 3 (length ast))
  else if e = ''Int'' then
    if (length ast = 2) then map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1))))
    else Error (ParseArgumentError ''Int'' 2 (length ast))
  else if e = ''Unknown'' then
    if (length ast = 2) then map_result_value Val (map_result_value2 CUnknown (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1)))
    else Error (ParseArgumentError ''Unknown'' 2 (length ast))
  else if e = ''SLE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Sle) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''SLE'' 2 (length ast))
  else if e = ''SLT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Slt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''SLT'' 2 (length ast))
  else if e = ''MINUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Minus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''MINUS'' 2 (length ast))
  else if e = ''TIMES'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Times) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''TIMES'' 2 (length ast))
  else if e = ''DIVIDE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Divide) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''DIVIDE'' 2 (length ast))
  else if e = ''XOR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Xor) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''XOR'' 2 (length ast))
  else if e = ''OR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Or) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''OR'' 2 (length ast))
  else if e = ''AND'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp And) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''AND'' 2 (length ast))
  else if e = ''LT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Lt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''LT'' 2 (length ast))
  else if e = ''LE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Le) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''LE'' 2 (length ast))
  else if e = ''NEQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Neq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''NEQ'' 2 (length ast))
  else if e = ''PLUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Plus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''PLUS'' 2 (length ast))
  else if e = ''MOD'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Mod) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''MOD'' 2 (length ast))
  else if e = ''SMOD'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp SMod) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''SMOD'' 2 (length ast))
  else if e = ''EQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''EQ'' 2 (length ast))
  else if e = ''RSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp RShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''RSHIFT'' 2 (length ast))
  else if e = ''ARSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp ARShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''ARSHIFT'' 2 (length ast))
  else if e = ''LSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp LShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''LSHIFT'' 2 (length ast))
  else if e = ''LOW'' then
    if (length ast = 2) then map_result_value2 (Cast Low) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''LOW'' 2 (length ast))
  else if e = ''HIGH'' then
    if (length ast = 2) then map_result_value2 (Cast High) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''HIGH'' 2 (length ast))
  else if e = ''UNSIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Unsigned) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''UNSIGNED'' 2 (length ast))
  else if e = ''SIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Signed) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''SIGNED'' 2 (length ast))
  else if e = ''Concat'' then
    if (length ast = 2) then map_result_value2 Concat (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (ParseArgumentError ''Concat'' 2 (length ast))
  else if e = ''NOT'' then
    if (length ast = 1) then map_result_value (UnOp Not) (parse_exp (ast ! 0))
    else Error (ParseArgumentError ''NOT'' 1 (length ast))
  else if e = ''NEG'' then
    if (length ast = 1) then map_result_value (UnOp Neg) (parse_exp (ast ! 0))
    else Error (ParseArgumentError ''NEG'' 1 (length ast))
  else Error (ParseTagInvalid [''Store'', ''Load'', ''Var'', ''Let'',
           ''Int'', ''Unknown'', ''NOT'', ''NEG'', ''SLE'', ''SLT'', ''MINUS'', ''TIMES'', ''DIVIDE'', ''XOR'', ''OR'',
           ''AND'', ''LT'', ''LE'', ''NEQ'', ''PLUS'', ''MOD'', ''SMOD'', ''EQ'', ''RSHIFT'', ''ARSHIFT'', ''LSHIFT'', ''LOW'', ''HIGH'',
           ''UNSIGNED'', ''SIGNED'', ''Ite'', ''Concat'', ''Extract''] e)
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
  subgoal premises p using p(30) apply clarify by (cases ast rule: length2_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(31) apply clarify by (cases ast rule: length2_cases, simp_all)  

  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(32) apply clarify by (cases ast rule: length1_cases, simp_all)
  
  apply (split if_splits, intro conjI impI)
  subgoal premises p using p(33) apply clarify by (cases ast rule: length1_cases, simp_all)
  by simp
  
code_datatype CUnknown Immediate Storage


definition
  CSpecial :: \<open>String.literal \<Rightarrow> stmt\<close> 
where
  \<open>CSpecial str = Special (String.explode str) \<close>


lemma [code]: \<open>parse_stmt (Node stmt ast) = (
    if stmt = ''Move'' then
      if (length ast = 2) then map_result_value2 Move (parse_var (ast ! 0)) (parse_exp (ast ! 1))
      else Error (ParseArgumentError ''Move'' 2 (length ast))
    else if stmt = ''Jmp'' then
      if (length ast = 1) then map_result_value Jmp (parse_exp (ast ! 0))
      else Error (ParseArgumentError ''Jmp'' 1 (length ast))
    else if stmt = ''CpuExn'' then
      if (length ast = 1) then map_result_value CpuExn (parse_int (ast ! 0))
      else Error (ParseArgumentError ''CpuExn'' 1 (length ast))
    else if stmt = ''Special'' then
      if (length ast = 1) then map_result_value CSpecial (map_result_value String.implode (parse_str (ast ! 0)))
      else Error (ParseArgumentError ''Special'' 1 (length ast))
    else if stmt = ''While'' then
      if (length ast = 2) then map_result_value2 While (parse_exp (ast ! 0)) (parse_bil (ast ! 1))
      else Error (ParseArgumentError ''While'' 2 (length ast))
    else if stmt = ''If'' then
      if (length ast = 3) then map_result_value3 If (parse_exp (ast ! 0)) (parse_bil (ast ! 1)) (parse_bil (ast ! 2))
      else Error (ParseArgumentError ''If'' 3 (length ast))
    else
       Error (ParseTagInvalid [''Move'', ''Jmp'', ''CpuExn'', ''Special'', ''While'', ''If''] stmt)
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

definition 
  is_sub_in_list :: \<open>String.literal list \<Rightarrow> AdtFunction \<Rightarrow> bool\<close>
where
  \<open>is_sub_in_list lst = Parser.is_sub_in_list (map String.explode lst)\<close>

lemma code_is_sub_in_list[code]: \<open>is_sub_in_list lst (AdtFunction adr name ast) = (name \<in> set (map String.explode lst))\<close>
  unfolding Parser_Code.is_sub_in_list_def by simp

definition 
  filter_subroutines_section :: \<open>String.literal list \<Rightarrow> AdtSection \<Rightarrow> AdtSection\<close>
where
  \<open>filter_subroutines_section str = Parser.filter_subroutines_section (map String.explode str)\<close>

lemma code_filter_subroutines_section[code]: \<open>filter_subroutines_section lst (AdtSection name ast) = (AdtSection name (filter (is_sub_in_list lst) ast))\<close>
  unfolding Parser_Code.filter_subroutines_section_def apply simp
  using is_sub_in_list_def by presburger

definition 
  filter_subroutines :: \<open>String.literal list \<Rightarrow> AdtSection list \<Rightarrow> AdtSection list\<close>
where
  \<open>filter_subroutines str = Parser.filter_subroutines (map String.explode str)\<close>

lemma code_filter_subroutines[code]: \<open>filter_subroutines lst ast = map (filter_subroutines_section lst) ast\<close>
  unfolding Parser_Code.filter_subroutines_def
  using filter_subroutines.simps filter_subroutines_section_def by presburger


export_code parse_ast get_symbol_table get_original_insn get_prog_addrs get_insns filter_subroutines in SML
  module_name AstParser file_prefix "ast-parser"

text \<open>Reflect the AST parser into the current Isabelle/HOL session\<close>

(* A lot of optimisation work remains here. The conversion functions are a code smell that need 
   to be resolved *)

code_reflect AstParser
  datatypes BinOp = AOp | LOp
        and Endian = BigEndian | LittleEndian 
        and Cast = Low | High | Signed | Unsigned 
        and LOp = Eq | Neq | Lt | Le | Slt | Sle
        and AOp = Plus | Minus | Times | Divide | SDivide | Mod | SMod | And | Or | Xor | LShift | 
                  RShift | ARShift
        and UnOp = Neg | Not 
        and exp = UnOp | BinOp | Store | Load | Concat | Extract | Val | EVar | Cast | Let | Ite
        and stmt = Move | While | If | Jmp | CpuExn | CSpecial
        and Type = Imm | Mem
        and val = Immediate | CUnknown | Storage
        and word = Word
        and var = CVar
        and result = Value | Error
        and ParseError = ParseNatError | ParseIntError | ParseArgumentError | StringMustBeQuoted |
                         ParseTagInvalid | TagExistsError | InvalidAdtInsn | InvalidAdtFunction
        and OfStringRadixError = EmptyString | InvalidRadix | InvalidCodepoint
        and insn_ext = insn_ext
  functions parse_ast integer_of_int integer_of_nat nat_of_integer int_of_integer integer_of_char
            get_original_insn get_symbol_table get_prog_addrs get_insns String.implode
            filter_subroutines get_subroutine_addrs join


end
