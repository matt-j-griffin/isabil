theory Parser_Code
  imports Parser 
    Lexer_Code 
begin

text \<open>Code Generation for ADT Parser\<close>

lemma implode_Nil[simp]: \<open>String.implode [] = STR ''''\<close>
  by (metis String.implode_explode_eq zero_literal.rep_eq)

lemma explode_Nil[simp]: \<open>literal.explode STR '''' = ''''\<close>
  using zero_literal.rep_eq by blast

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

lemma Literal_plus_empty:
  \<open>String.Literal a1 a2 a3 a4 a5 a6 a7 str = String.Literal a1 a2 a3 a4 a5 a6 a7 (STR '''') + str\<close>
  unfolding Literal_plus[symmetric] by auto

lemma [code]:
  \<open>of_string_radix_error_to_string EmptyString = STR ''Cannot convert empty string''\<close>
  \<open>of_string_radix_error_to_string (InvalidRadix z) = STR ''The provided radix was too large (max 32)''\<close>
  \<open>of_string_radix_error_to_string (InvalidCodepoint c z) = STR ''Codepoint out of range for radix: '' + String.implode [c]\<close>
  unfolding of_string_radix_error_to_string_def apply auto
  unfolding implode_Char_Cons implode_Nil apply presburger+
  unfolding Literal_plus_empty[where str = \<open>String.implode [c]\<close>] Literal_plus ..

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
definition \<open>CInvalidAdtSection \<equiv> InvalidAdtSection o (map String.explode)\<close>

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
  \<open>parse_error_to_string (CInvalidAdtSection strs) = STR ''Expecting adt section to contain at least two lines: ['' + (join strs) + STR '']''\<close>
  unfolding parse_error_to_string_def CParseArgumentError_def CStringMustBeQuoted_def of_string_radix_error_to_string_def
            CParseTagInvalid_def CTagExistsError_def CInvalidAdtInsn_def CInvalidAdtFunction_def CInvalidAdtSection_def
  apply auto
  unfolding implode_Nil implode_Char_Cons implode_append String.implode_explode_eq Literal_plus[symmetric]
  apply auto
  unfolding Parser_Code.join_def[symmetric]
  apply auto
  unfolding Literal_plus_empty[where str = str] Literal_plus add.assoc ..

lemma [code]:
  \<open>parse_int (CNode str []) = map_result_error ParseIntError (int_of_string (String.explode str))\<close> 
  \<open>parse_int (CNode str (x # xs)) = Error (CParseArgumentError (STR ''int: '' + str) 0 (length (x # xs)))\<close>
  unfolding CNode_def CParseArgumentError_def apply auto
  using Literal.rep_eq Literal_plus Literal_plus_empty by metis

lemma [code]:
  \<open>parse_nat_radix radix (CNode str []) = map_result_error ParseNatError (nat_of_string_radix radix (String.explode str))\<close>
  \<open>parse_nat_radix radix (CNode str (x # xs)) = Error (CParseArgumentError (STR ''nat: '' + str) 0 (length (x # xs)))\<close>
  unfolding CParseArgumentError_def CNode_def apply auto
  using Literal.rep_eq Literal_plus Literal_plus_empty by metis

text \<open>parse_en\<close>

lemma explode_to_implodeI[intro!]:
  assumes ascii_of: \<open>map String.ascii_of str = str\<close> and implode: \<open>lit = String.implode str\<close>
    shows \<open>str = literal.explode lit\<close>
  unfolding implode implode.rep_eq ascii_of ..

lemma parser_string_simps[simp]:
  \<open>literal.explode STR ''LittleEndian'' = ''LittleEndian''\<close>
  \<open>literal.explode STR ''BigEndian'' = ''BigEndian''\<close>
  \<open>literal.explode STR ''Imm'' = ''Imm''\<close>
  \<open>literal.explode STR ''Mem'' = ''Mem''\<close>
  \<open>literal.explode STR ''Var'' = ''Var''\<close>
  \<open>literal.explode STR ''Move'' = ''Move''\<close>
  \<open>literal.explode STR ''Jmp'' = ''Jmp''\<close>
  \<open>literal.explode STR ''Special'' = ''Special''\<close>
  \<open>literal.explode STR ''While'' = ''While''\<close>
  \<open>literal.explode STR ''If'' = ''If''\<close>
  \<open>literal.explode STR ''CpuExn'' = ''CpuExn''\<close>
  \<open>literal.explode STR ''Var'' = ''Var''\<close>
  \<open>literal.explode STR ''Store'' = ''Store''\<close>
  \<open>literal.explode STR ''Load'' = ''Load''\<close>
  \<open>literal.explode STR ''Let'' = ''Let''\<close>
  \<open>literal.explode STR ''Ite'' = ''Ite''\<close>
  \<open>literal.explode STR ''Extract'' = ''Extract''\<close>
  \<open>literal.explode STR ''Int'' = ''Int''\<close>
  \<open>literal.explode STR ''Unknown'' = ''Unknown''\<close>
  \<open>literal.explode STR ''SLE'' = ''SLE''\<close>
  \<open>literal.explode STR ''SLT'' = ''SLT''\<close>
  \<open>literal.explode STR ''MINUS'' = ''MINUS''\<close>
  \<open>literal.explode STR ''TIMES'' = ''TIMES''\<close>
  \<open>literal.explode STR ''DIVIDE'' = ''DIVIDE''\<close>
  \<open>literal.explode STR ''XOR'' = ''XOR''\<close>
  \<open>literal.explode STR ''OR'' = ''OR''\<close>
  \<open>literal.explode STR ''AND'' = ''AND''\<close>
  \<open>literal.explode STR ''LT'' = ''LT''\<close>
  \<open>literal.explode STR ''LE'' = ''LE''\<close>
  \<open>literal.explode STR ''NEQ'' = ''NEQ''\<close>
  \<open>literal.explode STR ''PLUS'' = ''PLUS''\<close>
  \<open>literal.explode STR ''MOD'' = ''MOD''\<close>
  \<open>literal.explode STR ''SMOD'' = ''SMOD''\<close>
  \<open>literal.explode STR ''EQ'' = ''EQ''\<close>
  \<open>literal.explode STR ''RSHIFT'' = ''RSHIFT''\<close>
  \<open>literal.explode STR ''ARSHIFT'' = ''ARSHIFT''\<close>
  \<open>literal.explode STR ''LSHIFT'' = ''LSHIFT''\<close>
  \<open>literal.explode STR ''LOW'' = ''LOW''\<close>
  \<open>literal.explode STR ''HIGH'' = ''HIGH''\<close>
  \<open>literal.explode STR ''UNSIGNED'' = ''UNSIGNED''\<close>
  \<open>literal.explode STR ''SIGNED'' = ''SIGNED''\<close>
  \<open>literal.explode STR ''Concat'' = ''Concat''\<close>
  \<open>literal.explode STR ''NOT'' = ''NOT''\<close>
  \<open>literal.explode STR ''NEG'' = ''NEG''\<close>
  by (rule explode_to_implodeI[symmetric], unfold implode_Char_Cons implode_Nil, simp_all)+


lemma [code]: \<open>parse_en (CNode en ast) = (
  if en = STR ''LittleEndian'' then
    case ast of [] \<Rightarrow> Value el
    | x # xs \<Rightarrow> Error (CParseArgumentError (STR ''LittleEndian'') 0 (length (x # xs)))
  else if en = STR ''BigEndian'' then
    case ast of [] \<Rightarrow> Value be
    | x # xs \<Rightarrow> Error (CParseArgumentError (STR ''BigEndian'') 0 (length (x # xs)))
  else Error (CParseTagInvalid [STR ''BigEndian'', STR ''LittleEndian''] en)
  )\<close>

unfolding CParseArgumentError_def CParseTagInvalid_def CNode_def
sketch (split if_splits , intro conjI impI , defer_tac) +
proof (split if_splits , intro conjI impI , defer_tac) +
  assume "en \<noteq> STR ''LittleEndian''" "en \<noteq> STR ''BigEndian''"
  hence en_explode: \<open>literal.explode en \<noteq> ''LittleEndian''\<close> "literal.explode en \<noteq> ''BigEndian''"
    by (metis literal.explode_inject parser_string_simps)+
  thus "parse_en (Node (literal.explode en) ast) = Error (ParseTagInvalid (map literal.explode [STR ''BigEndian'', STR ''LittleEndian'']) (literal.explode en))"
    by (cases ast, auto)
next
  assume en: "en = STR ''LittleEndian''"
  show "parse_en (Node (literal.explode en) ast) = (case ast of [] \<Rightarrow> Value el | x # xs \<Rightarrow> Error ((ParseArgumentError \<circ> literal.explode) STR ''LittleEndian'' 0 (length (x # xs))))"
    unfolding en parser_string_simps by (cases ast, auto)
next
  assume en: "en = STR ''BigEndian''"
  show "parse_en (Node (literal.explode en) ast) = (case ast of [] \<Rightarrow> Value be | x # xs \<Rightarrow> Error ((ParseArgumentError \<circ> literal.explode) STR ''BigEndian'' 0 (length (x # xs))))"
    unfolding en parser_string_simps by (cases ast, auto)
qed


lemma [code]: \<open>parse_typ (CNode typ ast) = (
  if typ = STR ''Imm'' then
    if (length ast = 1) then map_result_value Imm (parse_nat_dec (ast ! 0))
    else Error (CParseArgumentError (STR ''Imm'') 1 (length ast))
  else if typ = STR ''Mem'' then
    if (length ast = 2) then  map_result_value2 Mem (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1))
    else Error (CParseArgumentError (STR ''Mem'') 2 (length ast))
  else Error (CParseTagInvalid [STR ''Imm'', STR ''Mem''] typ)
  )\<close>
unfolding CParseArgumentError_def CParseTagInvalid_def CNode_def
proof (split if_splits , intro conjI impI , defer_tac) +
  assume "typ \<noteq> STR ''Imm''"
    and "typ \<noteq> STR ''Mem''"
  hence typ_explode: \<open>literal.explode typ \<noteq> ''Imm''\<close> "literal.explode typ \<noteq> ''Mem''"
    by (metis literal.explode_inject parser_string_simps)+
  thus "parse_typ (Node (literal.explode typ) ast) = Error (ParseTagInvalid (map literal.explode [STR ''Imm'', STR ''Mem'']) (literal.explode typ))"
    by (cases ast, auto)
next                             
  assume type: "typ = STR ''Imm''"
  show "parse_typ (Node (literal.explode typ) ast) = (if length ast = 1 then map_result_value Imm (parse_nat_dec (ast ! 0)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Imm'' 1 (length ast)))"
    unfolding type parser_string_simps by (cases ast rule: length1_cases, auto)
next
  assume type: "typ = STR ''Mem''"
  show "parse_typ (Node (literal.explode typ) ast) = (if length ast = 2 then map_result_value2 Mem (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Mem'' 2 (length ast)))"
    unfolding type parser_string_simps by (cases ast rule: length2_cases, auto)
qed

definition 
  CVar :: \<open>String.literal \<Rightarrow> Type \<Rightarrow> var\<close> 
where
  \<open>CVar str t = Var (String.explode str)  t\<close>

lemma ascii_of2[simp]: \<open>String.ascii_of \<circ> String.ascii_of = String.ascii_of\<close>
  unfolding comp_def by simp

lemma [code]: \<open>parse_var (CNode var ast) = (
  if var = STR ''Var'' then
    if (length ast = 2) then map_result_value2 CVar (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1))
    else Error (CParseArgumentError (STR ''Var'') 2 (length ast))
  else Error (CParseTagInvalid [STR ''Var''] var)
  )\<close>
unfolding CVar_def CParseArgumentError_def CParseTagInvalid_def CNode_def 
sketch (split if_splits , intro conjI impI , defer_tac) +
proof (split if_splits , intro conjI impI , defer_tac) +
  assume "var \<noteq> STR ''Var''"
  hence var_explode: \<open>literal.explode var \<noteq> ''Var''\<close>
    by (metis literal.explode_inject parser_string_simps)+
  thus "parse_var (Node (literal.explode var) ast) = Error (ParseTagInvalid (map literal.explode [STR ''Var'']) (literal.explode var))"
    by simp
next
  assume var: "var = STR ''Var''"
  show "parse_var (Node (literal.explode var) ast) = (if length ast = 2 then map_result_value2 (\<lambda>str. Var (literal.explode str)) (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Var'' 2 (length ast)))"
  unfolding var parser_string_simps
  proof (cases ast rule: length2_cases, auto)
    fix str t :: AST
    show "map_result_value2 Var (parse_str str) (parse_typ t) = map_result_value2 (\<lambda>str. Var (literal.explode str)) (map_result_value String.implode (parse_str str)) (parse_typ t)"
      by (cases str rule: parse_str.cases, auto)
  qed
qed

code_datatype CVar

definition
  CUnknown :: \<open>String.literal \<Rightarrow> Type \<Rightarrow> val\<close> 
where
  \<open>CUnknown str t = Unknown (String.explode str)  t\<close>

lemma map_result_value2_map_result_value[simp]: 
    "map_result_value2 F (map_result_value G x) y = map_result_value2 (F \<circ> G) x y"
  by (cases x, auto)

lemma [code]: \<open>parse_exp (CNode e ast) = (
  if e = STR ''Var'' then map_result_value EVar (parse_var (CNode STR ''Var'' ast))
  else if e = STR ''Store'' then
    if (length ast = 5) then map_result_value5 Store (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 3)) (parse_nat_dec (ast ! 4)) (parse_exp (ast ! 2))
    else Error (CParseArgumentError STR ''Store'' 5 (length ast))
  else if e = STR ''Load'' then
    if (length ast = 4) then map_result_value4 Load (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 2)) (parse_nat_dec (ast ! 3))
    else Error (CParseArgumentError STR ''Load'' 4 (length ast))
  else if e = STR ''Let'' then
    if (length ast = 3) then map_result_value3 Let (parse_var (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error (CParseArgumentError STR ''Let'' 3 (length ast))
  else if e = STR ''Ite'' then
    if (length ast = 3) then map_result_value3 Ite (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2))
    else Error (CParseArgumentError STR ''Ite'' 3 (length ast))
  else if e = STR ''Extract'' then
    if (length ast = 3) then map_result_value3 Extract (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1)) (parse_exp (ast ! 2))
    else Error (CParseArgumentError STR ''Extract'' 3 (length ast))
  else if e = STR ''Int'' then
    if (length ast = 2) then map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1))))
    else Error (CParseArgumentError STR ''Int'' 2 (length ast))
  else if e = STR ''Unknown'' then
    if (length ast = 2) then map_result_value Val (map_result_value2 CUnknown (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1)))
    else Error (CParseArgumentError STR ''Unknown'' 2 (length ast))
  else if e = STR ''SLE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Sle) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''SLE'' 2 (length ast))
  else if e = STR ''SLT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Slt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''SLT'' 2 (length ast))
  else if e = STR ''MINUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Minus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''MINUS'' 2 (length ast))
  else if e = STR ''TIMES'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Times) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''TIMES'' 2 (length ast))
  else if e = STR ''DIVIDE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Divide) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''DIVIDE'' 2 (length ast))
  else if e = STR ''XOR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Xor) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''XOR'' 2 (length ast))
  else if e = STR ''OR'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Or) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''OR'' 2 (length ast))
  else if e = STR ''AND'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp And) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''AND'' 2 (length ast))
  else if e = STR ''LT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Lt) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''LT'' 2 (length ast))
  else if e = STR ''LE'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Le) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''LE'' 2 (length ast))
  else if e = STR ''NEQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Neq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''NEQ'' 2 (length ast))
  else if e = STR ''PLUS'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Plus) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''PLUS'' 2 (length ast))
  else if e = STR ''MOD'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Mod) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''MOD'' 2 (length ast))
  else if e = STR ''SMOD'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp SMod) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''SMOD'' 2 (length ast))
  else if e = STR ''EQ'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''EQ'' 2 (length ast))
  else if e = STR ''RSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp RShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''RSHIFT'' 2 (length ast))
  else if e = STR ''ARSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp ARShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''ARSHIFT'' 2 (length ast))
  else if e = STR ''LSHIFT'' then
    if (length ast = 2) then map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp LShift) e\<^sub>2) (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''LSHIFT'' 2 (length ast))
  else if e = STR ''LOW'' then
    if (length ast = 2) then map_result_value2 (Cast Low) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''LOW'' 2 (length ast))
  else if e = STR ''HIGH'' then
    if (length ast = 2) then map_result_value2 (Cast High) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''HIGH'' 2 (length ast))
  else if e = STR ''UNSIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Unsigned) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''UNSIGNED'' 2 (length ast))
  else if e = STR ''SIGNED'' then
    if (length ast = 2) then map_result_value2 (Cast Signed) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''SIGNED'' 2 (length ast))
  else if e = STR ''Concat'' then
    if (length ast = 2) then map_result_value2 Concat (parse_exp (ast ! 0)) (parse_exp (ast ! 1))
    else Error (CParseArgumentError STR ''Concat'' 2 (length ast))
  else if e = STR ''NOT'' then
    if (length ast = 1) then map_result_value (UnOp Not) (parse_exp (ast ! 0))
    else Error (CParseArgumentError STR ''NOT'' 1 (length ast))
  else if e = STR ''NEG'' then
    if (length ast = 1) then map_result_value (UnOp Neg) (parse_exp (ast ! 0))
    else Error (CParseArgumentError STR ''NEG'' 1 (length ast))
  else Error (CParseTagInvalid [STR ''Store'', STR ''Load'', STR ''Var'', STR ''Let'',
           STR ''Int'', STR ''Unknown'', STR ''NOT'', STR ''NEG'', STR ''SLE'', STR ''SLT'', STR ''MINUS'', STR ''TIMES'', STR ''DIVIDE'', STR ''XOR'', STR ''OR'',
           STR ''AND'', STR ''LT'', STR ''LE'', STR ''NEQ'', STR ''PLUS'', STR ''MOD'', STR ''SMOD'', STR ''EQ'', STR ''RSHIFT'', STR ''ARSHIFT'', STR ''LSHIFT'', STR ''LOW'', STR ''HIGH'',
           STR ''UNSIGNED'', STR ''SIGNED'', STR ''Ite'', STR ''Concat'', STR ''Extract''] e)
  )\<close>
unfolding CParseArgumentError_def CParseTagInvalid_def CUnknown_def CNode_def
sketch (split if_splits , intro conjI impI, defer_tac) +
proof (split if_splits , intro conjI impI , defer_tac) +
  assume "e \<noteq> STR ''Var''" "e \<noteq> STR ''Store''" "e \<noteq> STR ''Load''" "e \<noteq> STR ''Let''" 
         "e \<noteq> STR ''Ite''" "e \<noteq> STR ''Extract''" "e \<noteq> STR ''Int''" "e \<noteq> STR ''Unknown''"
         "e \<noteq> STR ''SLE''" "e \<noteq> STR ''SLT''" "e \<noteq> STR ''MINUS''" "e \<noteq> STR ''TIMES''"
         "e \<noteq> STR ''DIVIDE''" "e \<noteq> STR ''XOR''" "e \<noteq> STR ''OR''" "e \<noteq> STR ''AND''" 
         "e \<noteq> STR ''LT''" "e \<noteq> STR ''LE''" "e \<noteq> STR ''NEQ''" "e \<noteq> STR ''PLUS''" "e \<noteq> STR ''MOD''" 
         "e \<noteq> STR ''SMOD''" "e \<noteq> STR ''EQ''" "e \<noteq> STR ''RSHIFT''" "e \<noteq> STR ''ARSHIFT''" 
         "e \<noteq> STR ''LSHIFT''" "e \<noteq> STR ''LOW''" "e \<noteq> STR ''HIGH''"  "e \<noteq> STR ''UNSIGNED''" 
         "e \<noteq> STR ''SIGNED''" "e \<noteq> STR ''Concat''" "e \<noteq> STR ''NOT''" "e \<noteq> STR ''NEG''"
  hence e_explode: "literal.explode e \<noteq> ''Var''" "literal.explode e \<noteq> ''Store''" "literal.explode e \<noteq> ''Load''" "literal.explode e \<noteq> ''Let''" 
         "literal.explode e \<noteq> ''Ite''" "literal.explode e \<noteq> ''Extract''" "literal.explode e \<noteq> ''Int''" "literal.explode e \<noteq> ''Unknown''"
         "literal.explode e \<noteq> ''SLE''" "literal.explode e \<noteq> ''SLT''" "literal.explode e \<noteq> ''MINUS''" "literal.explode e \<noteq> ''TIMES''"
         "literal.explode e \<noteq> ''DIVIDE''" "literal.explode e \<noteq> ''XOR''" "literal.explode e \<noteq> ''OR''" "literal.explode e \<noteq> ''AND''" 
         "literal.explode e \<noteq> ''LT''" "literal.explode e \<noteq> ''LE''" "literal.explode e \<noteq> ''NEQ''" "literal.explode e \<noteq> ''PLUS''" "literal.explode e \<noteq> ''MOD''" 
         "literal.explode e \<noteq> ''SMOD''" "literal.explode e \<noteq> ''EQ''" "literal.explode e \<noteq> ''RSHIFT''" "literal.explode e \<noteq> ''ARSHIFT''" 
         "literal.explode e \<noteq> ''LSHIFT''" "literal.explode e \<noteq> ''LOW''" "literal.explode e \<noteq> ''HIGH''"  "literal.explode e \<noteq> ''UNSIGNED''" 
         "literal.explode e \<noteq> ''SIGNED''" "literal.explode e \<noteq> ''Concat''" "literal.explode e \<noteq> ''NOT''" "literal.explode e \<noteq> ''NEG''"
    by (metis literal.explode_inject parser_string_simps)+
  thus "parse_exp (Node (literal.explode e) ast) = Error (ParseTagInvalid (map literal.explode [STR ''Store'', STR ''Load'', STR ''Var'', STR ''Let'', STR ''Int'', STR ''Unknown'', STR ''NOT'', STR ''NEG'', STR ''SLE'', STR ''SLT'', STR ''MINUS'', STR ''TIMES'', STR ''DIVIDE'', STR ''XOR'', STR ''OR'', STR ''AND'', STR ''LT'', STR ''LE'', STR ''NEQ'', STR ''PLUS'', STR ''MOD'', STR ''SMOD'', STR ''EQ'', STR ''RSHIFT'', STR ''ARSHIFT'', STR ''LSHIFT'', STR ''LOW'', STR ''HIGH'', STR ''UNSIGNED'', STR ''SIGNED'', STR ''Ite'', STR ''Concat'', STR ''Extract'']) (literal.explode e))"
    by simp
next
  assume e: "e = STR ''Var''"
  thus "parse_exp (Node (literal.explode e) ast) = map_result_value EVar (parse_var (Node (literal.explode STR ''Var'') ast))"
    by (cases ast rule: length2_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Store''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 5 then map_result_value5 Store (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 3)) (parse_nat_dec (ast ! 4)) (parse_exp (ast ! 2)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Store'' 5 (length ast)))"
    by (cases ast rule: length5_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Load''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 4 then map_result_value4 Load (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_en (ast ! 2)) (parse_nat_dec (ast ! 3)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Load'' 4 (length ast)))"
    by (cases ast rule: length4_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Let''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 3 then map_result_value3 exp.Let (parse_var (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Let'' 3 (length ast)))"
    by (cases ast rule: length3_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Ite''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 3 then map_result_value3 Ite (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) (parse_exp (ast ! 2)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Ite'' 3 (length ast)))"
    apply (cases ast rule: length3_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Extract''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 3 then map_result_value3 Extract (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1)) (parse_exp (ast ! 2)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Extract'' 3 (length ast)))"
    apply (cases ast rule: length3_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Int''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat_dec (ast ! 0)) (parse_nat_dec (ast ! 1)))) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Int'' 2 (length ast)))"
    by (cases ast rule: length2_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Unknown''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value Val (map_result_value2 (\<lambda>str. Unknown (literal.explode str)) (map_result_value String.implode (parse_str (ast ! 0))) (parse_typ (ast ! 1))) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Unknown'' 2 (length ast)))"
  proof (cases ast rule: length2_cases , simp_all add: implode_Char_Cons explode_to_implodeI)
    fix str t :: AST
    show "map_result_value Val (map_result_value2 Unknown (parse_str str) (parse_typ t)) = map_result_value Val (map_result_value2 ((\<lambda>str. Unknown (literal.explode str)) \<circ> String.implode) (parse_str str) (parse_typ t))"
      unfolding comp_def apply simp
      by (cases str rule: parse_str.cases, auto)
  qed
next
  assume "e = STR ''SLE''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Sle)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''SLE'' 2 (length ast)))"
    by (cases ast rule: length2_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''SLT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Slt)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''SLT'' 2 (length ast)))"
    by (cases ast rule: length2_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''MINUS''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Minus)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''MINUS'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''TIMES''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Times)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''TIMES'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)

next
  assume "e = STR ''DIVIDE''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Divide)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''DIVIDE'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''XOR''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Xor)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''XOR'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''OR''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Or)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''OR'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''AND''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp And)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''AND'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''LT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Lt)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''LT'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''LE''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Le)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''LE'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''NEQ''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Neq)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''NEQ'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''PLUS''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Plus)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''PLUS'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''MOD''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp Mod)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''MOD'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''SMOD''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp SMod)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''SMOD'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''EQ''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (LOp Eq)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''EQ'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''RSHIFT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp RShift)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''RSHIFT'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''ARSHIFT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp ARShift)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''ARSHIFT'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''LSHIFT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<lambda>e\<^sub>1. BinOp e\<^sub>1 (AOp LShift)) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''LSHIFT'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''LOW''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (Cast low) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''LOW'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''HIGH''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (Cast high) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''HIGH'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''UNSIGNED''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (Cast pad) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''UNSIGNED'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''SIGNED''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (Cast extend) (parse_nat_dec (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''SIGNED'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''Concat''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 2 then map_result_value2 (\<copyright>) (parse_exp (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Concat'' 2 (length ast)))"
    apply (cases ast rule: length2_cases, clarify)
    unfolding parse_exp.simps by (simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''NOT''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 1 then map_result_value (UnOp UnOp.Not) (parse_exp (ast ! 0)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''NOT'' 1 (length ast)))"
    by (cases ast rule: length1_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
next
  assume "e = STR ''NEG''"
  thus "parse_exp (Node (literal.explode e) ast) = (if length ast = 1 then map_result_value (UnOp Neg) (parse_exp (ast ! 0)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''NEG'' 1 (length ast)))"
    by (cases ast rule: length1_cases, simp_all add: implode_Char_Cons explode_to_implodeI)
qed 
  
code_datatype CUnknown Immediate Storage

definition
  CSpecial :: \<open>String.literal \<Rightarrow> stmt\<close> 
where
  \<open>CSpecial str = Special (String.explode str) \<close>

lemma [code]: \<open>parse_stmt (CNode stmt ast) = (
    if stmt = STR ''Move'' then
      if (length ast = 2) then map_result_value2 Move (parse_var (ast ! 0)) (parse_exp (ast ! 1))
      else Error (CParseArgumentError STR ''Move'' 2 (length ast))
    else if stmt = STR ''Jmp'' then
      if (length ast = 1) then map_result_value Jmp (parse_exp (ast ! 0))
      else Error (CParseArgumentError STR ''Jmp'' 1 (length ast))
    else if stmt = STR ''CpuExn'' then
      if (length ast = 1) then map_result_value CpuExn (parse_int (ast ! 0))
      else Error (CParseArgumentError STR ''CpuExn'' 1 (length ast))
    else if stmt = STR ''Special'' then
      if (length ast = 1) then map_result_value CSpecial (map_result_value String.implode (parse_str (ast ! 0)))
      else Error (CParseArgumentError STR ''Special'' 1 (length ast))
    else if stmt = STR ''While'' then
      if (length ast = 2) then map_result_value2 While (parse_exp (ast ! 0)) (parse_bil (ast ! 1))
      else Error (CParseArgumentError STR ''While'' 2 (length ast))
    else if stmt = STR ''If'' then
      if (length ast = 3) then map_result_value3 If (parse_exp (ast ! 0)) (parse_bil (ast ! 1)) (parse_bil (ast ! 2))
      else Error (CParseArgumentError STR ''If'' 3 (length ast))
    else
       Error (CParseTagInvalid [STR ''Move'', STR ''Jmp'', STR ''CpuExn'', STR ''Special'', 
                                STR ''While'', STR ''If''] stmt)
)\<close>
unfolding CParseArgumentError_def CSpecial_def CNode_def CParseTagInvalid_def
sketch (split if_splits , intro conjI impI , defer_tac) +
proof (split if_splits , intro conjI impI , defer_tac) +
  assume "stmt \<noteq> STR ''Move''" "stmt \<noteq> STR ''Jmp''" "stmt \<noteq> STR ''CpuExn''" "stmt \<noteq> STR ''Special''"
         "stmt \<noteq> STR ''While''" "stmt \<noteq> STR ''If''"
  hence stmt_explode: "String.explode stmt \<noteq> ''Move''" "String.explode stmt \<noteq> ''Jmp''" 
        "String.explode stmt \<noteq> ''CpuExn''" "String.explode stmt \<noteq> ''Special''"
        "String.explode stmt \<noteq> ''While''" "String.explode stmt \<noteq> ''If''"
    by (metis literal.explode_inject parser_string_simps)+
  thus "parse_stmt (Node (literal.explode stmt) ast) = Error (ParseTagInvalid
       (map literal.explode [STR ''Move'', STR ''Jmp'', STR ''CpuExn'', STR ''Special'', STR ''While'', STR ''If'']) (literal.explode stmt))"
    by (cases ast, auto)
next
  assume stmt: "stmt = STR ''Move''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 2 then map_result_value2 (:=) (parse_var (ast ! 0)) (parse_exp (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Move'' 2 (length ast)))"
    unfolding stmt parser_string_simps by (cases ast rule: length2_cases, simp_all)
next
  assume stmt: "stmt = STR ''Jmp''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 1 then map_result_value Jmp (parse_exp (ast ! 0)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Jmp'' 1 (length ast)))"
    unfolding stmt parser_string_simps by (cases ast rule: length1_cases, simp_all)
next
  assume stmt: "stmt = STR ''CpuExn''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 1 then map_result_value CpuExn (parse_int (ast ! 0)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''CpuExn'' 1 (length ast)))"
    unfolding stmt parser_string_simps by (cases ast rule: length1_cases, simp_all)
next
  assume stmt: "stmt = STR ''Special''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 1 then map_result_value (\<lambda>str. special[literal.explode str]) (map_result_value String.implode (parse_str (ast ! 0))) else Error ((ParseArgumentError \<circ> literal.explode) STR ''Special'' 1 (length ast)))"
    unfolding stmt parser_string_simps sketch (cases ast rule: length1_cases, simp_all)
  proof (cases ast rule: length1_cases , simp_all)
    fix str :: AST
    show "map_result_value Special (parse_str str) = map_result_value (\<lambda>str. special[literal.explode str]) (map_result_value String.implode (parse_str str))"
      by (cases str rule: parse_str.cases, auto)
  qed
next
  assume stmt: "stmt = STR ''While''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 2 then map_result_value2 While (parse_exp (ast ! 0)) (parse_bil (ast ! 1)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''While'' 2 (length ast)))"
    unfolding stmt parser_string_simps
    by (cases ast rule: length2_cases, simp_all)
next
  assume stmt: "stmt = STR ''If''"
  show "parse_stmt (Node (literal.explode stmt) ast)  = (if length ast = 3 then map_result_value3 stmt.If (parse_exp (ast ! 0)) (parse_bil (ast ! 1)) (parse_bil (ast ! 2)) else Error ((ParseArgumentError \<circ> literal.explode) STR ''If'' 3 (length ast)))"
    unfolding stmt parser_string_simps
    by (cases ast rule: length3_cases, simp_all)
qed

code_datatype CSpecial CpuExn While Move Jmp stmt.If

lemma [code]:
  \<open>parse_bil (CNode str ast) = (
    if str = STR '''' then flatten_error (map parse_stmt ast)
    else Error (CTagExistsError str)
  )\<close> 
unfolding CNode_def CTagExistsError_def proof (split if_splits, intro conjI impI, defer_tac)+
  assume "str \<noteq> STR ''''"
  hence \<open>literal.explode str \<noteq> ''''\<close>
    by (metis literal.explode_inject explode_Nil)
  thus "parse_bil (Node (literal.explode str) ast) = Error ((TagExistsError \<circ> literal.explode) str)"
    by (metis comp_apply int_of_string.cases parse_bil.simps(2))
qed auto

lemma ascii_of_explode[simp]: \<open>map String.ascii_of (literal.explode str) = literal.explode str\<close>    
  using String.implode_explode_eq implode.rep_eq
  by (metis )

lemma [code]:
  \<open>parse_str (CNode str []) = (
    if (size_class.size str \<ge> 2 \<and> hd (String.explode str) = CHR ''"'' \<and> last (String.explode str) = CHR ''"'') then Value (map String.ascii_of (tl (butlast (String.explode str))))
    else Error (CStringMustBeQuoted str)
  )\<close>
  \<open>parse_str (CNode str (x # xs)) = Error (CParseArgumentError (STR ''str: '' + str) 0 (length (x # xs)))\<close>
  unfolding CNode_def CParseArgumentError_def CStringMustBeQuoted_def size_literal.rep_eq apply auto
  unfolding implode_Char_Cons String.implode_explode_eq 
  by (metis Literal_plus Literal_plus_empty)

code_datatype CNode

definition \<open>CAdtInsn num bil str \<equiv> AdtInsn num bil (String.explode str)\<close>

code_datatype CAdtInsn

definition \<open>CAdtFunction num str insns = AdtFunction num (String.explode str) insns\<close>

code_datatype CAdtFunction

definition \<open>CAdtSection str funs = AdtSection (String.explode str) funs\<close>

code_datatype CAdtSection

definition 
  parse_adt_insn :: \<open>String.literal list \<Rightarrow> AdtInsn parser_result\<close>
where
  \<open>parse_adt_insn strs = Parser.parse_adt_insn (map String.explode strs)\<close>

lemma implode_parse_adt_insn: \<open>Parser_Code.parse_adt_insn \<circ> map String.implode = Parser.parse_adt_insn o (map (map String.ascii_of))\<close>
  unfolding parse_adt_insn_def comp_def
  by (auto simp del: Parser.parse_adt_insn.simps)

lemma ascii_of_split:
 \<open>map (map String.ascii_of) (split c (map String.ascii_of x)) = split c (map String.ascii_of x)\<close>
proof (induct x)
  case (Cons c' xs)
  show ?case 
  proof (cases \<open>c = c'\<close>)
    case True
    then show ?thesis 
      using Cons apply simp
      using ascii_of_ascii_of ascii_of_insert_hd explode_Nil implode.rep_eq implode_Nil list.simps(9) split_eq_char split_neq_char
      by (smt (verit))
  next
    case False
    then show ?thesis 
      using Cons apply simp
      using ascii_of_ascii_of ascii_of_insert_hd explode_Nil implode.rep_eq implode_Nil list.simps(9) split_eq_char split_neq_char
      by (smt (verit))
  qed
qed simp

lemma ascii_of_explode_split:
 \<open>map (map String.ascii_of) (split c (literal.explode str)) = split c (literal.explode str)\<close>
  by (metis ascii_of_explode ascii_of_split)

lemma ascii_of_explode_trim_split:
  assumes lines_gt_1: "n < length (split CHR '':'' (literal.explode xs))"
    shows "map String.ascii_of (trim (split CHR '':'' (literal.explode xs) ! n)) =
           trim (split CHR '':'' (literal.explode xs) ! n)"
  by (metis ascii_of_explode_split ascii_of_trim lines_gt_1 nth_map)

lemma [code]: \<open>parse_adt_insn lines = (
    if (length lines = 2 \<or> length lines = 3) then
      let 
        lines' = if length lines = 3 then drop 1 lines else lines;
        headers = map trim (split (CHR '':'') (String.explode (lines' ! 0)))
      in (
        if (length headers > 1) then
          let         
            num = map_result_error ParseNatError (nat_of_hex_string (headers ! 0))
          in
            map_result_value2 (\<lambda>addr bil. CAdtInsn addr bil (String.implode (headers ! 1))) num ((parse_bil o lexer)(lines' ! 1))
        else Error (CInvalidAdtInsn lines)
      )
    else Error (CInvalidAdtInsn lines))\<close>
  unfolding parse_adt_insn_def CInvalidAdtInsn_def Parser.parse_adt_insn.simps Let_def CAdtInsn_def
            Lexer_Code.lexer_def
  apply (split if_split, split if_splits)
  apply (auto simp del: lexer.simps trim_def)
proof (intro map_result_value2_inject ext)
  fix x :: nat
    and bil :: "stmt list"
  assume lines_gt_1: "Suc 0 < length (split CHR '':'' (literal.explode (lines ! 0)))"
    and len: "length lines = 2"
  show "AdtInsn x bil (trim (split CHR '':'' (literal.explode (lines ! 0)) ! Suc 0)) = 
        AdtInsn x bil (map String.ascii_of (trim (split CHR '':'' (literal.explode (lines ! 0)) ! Suc 0)))"
    using len apply (auto simp del: lexer.simps trim_def)
    using lines_gt_1 by (rule ascii_of_explode_trim_split[symmetric])
next
  assume lines_gt_1: "Suc 0 < length (split CHR '':'' (literal.explode (lines ! Suc 0)))"
    and len: "length lines = 3"
  show "map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (trim (split CHR '':'' (literal.explode (lines ! Suc 0)) ! Suc 0))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! Suc 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc (Suc 0))))) = map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (map String.ascii_of (trim (split CHR '':'' (literal.explode (lines ! Suc 0)) ! Suc 0)))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! Suc 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc (Suc 0)))))"
    apply (intro map_result_value2_inject ext)
    using len apply (auto simp del: lexer.simps trim_def)
    using lines_gt_1 by (rule ascii_of_explode_trim_split[symmetric])
next
  assume lines_gt_1: "Suc 0 < length (split CHR '':'' (literal.explode (lines ! 0)))"
    and "\<not> Suc 0 < length (split CHR '':'' (literal.explode (lines ! Suc 0)))"
    and len: "length lines = 2"
  show "map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (trim (split CHR '':'' (literal.explode (lines ! 0)) ! Suc 0))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc 0)))) = 
        map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (map String.ascii_of (trim (split CHR '':'' (literal.explode (lines ! 0)) ! Suc 0)))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc 0))))"
    apply (intro map_result_value2_inject ext)
    using len apply (auto simp del: lexer.simps trim_def)
    using lines_gt_1 by (rule ascii_of_explode_trim_split[symmetric])
next
  assume lines_gt_1: "Suc 0 < length (split CHR '':'' (literal.explode (lines ! Suc 0)))"
    and len: "length lines = 3"
  show "map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (trim (split CHR '':'' (literal.explode (lines ! Suc 0)) ! Suc 0))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! Suc 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc (Suc 0))))) = map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (map String.ascii_of (trim (split CHR '':'' (literal.explode (lines ! Suc 0)) ! Suc 0)))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! Suc 0))) ! 0))) (parse_bil (Lexer.lexer (literal.explode (lines ! Suc (Suc 0)))))"
    apply (intro map_result_value2_inject ext)
    using len apply (auto simp del: lexer.simps trim_def)
    using lines_gt_1 by (rule ascii_of_explode_trim_split[symmetric])
qed simp_all

definition 
  parse_adt_function :: \<open>String.literal list \<Rightarrow> AdtFunction parser_result\<close>
where
  \<open>parse_adt_function lines = Parser.parse_adt_function (map String.explode lines)\<close>


lemma implode_parse_adt_function: \<open>Parser_Code.parse_adt_function \<circ> map String.implode = Parser.parse_adt_function o (map (map String.ascii_of))\<close>
  unfolding parse_adt_function_def comp_def
  by (auto simp del: Parser.parse_adt_function.simps)

lemma ascii_of_splitWhen: \<open>map (map (map String.ascii_of)) (splitWhen P (map literal.explode xs)) = splitWhen P (map literal.explode xs)\<close>
proof (induct xs)
  case (Cons a xs)
  thus ?case 
  proof (cases \<open>P (literal.explode a)\<close>)
    case False
    then show ?thesis 
      using Cons apply simp
      by (smt (verit, best) ascii_of_explode insert_hd.elims list.inject list.simps(8) list.simps(9))
  qed simp
qed simp

lemma if_cond_eq:
  assumes "P \<Longrightarrow> X = Z" "\<not>P \<Longrightarrow> Y = W"
  shows "(if P then X else Y) = (if P then Z else W)"
  using assms by auto

lemmas flatten_error_arg_cong = arg_cong[where f = flatten_error]

lemma [code]: \<open>parse_adt_function lines = (
    if (length lines > 2) then
      let
        headers = map trim (split (CHR '':'') (String.explode (lines ! 0)))
      in
        if (length headers = 2) then 
          let
            name = tl (butlast (headers ! 1));
            addr_result = map_result_error ParseNatError (nat_of_hex_string (headers ! 0));
            insn_lines = map String.explode (drop 2 lines);
            insn_grouped_lines = splitWhen (\<lambda>s. hd s = CHR ''('') insn_lines;
            insn_results = map parse_adt_insn (map (map String.implode) insn_grouped_lines);
            insns = flatten_error insn_results
          in
            map_result_value2 (\<lambda>addr. CAdtFunction addr (String.implode name)) addr_result insns
        else
          Error (CInvalidAdtFunction lines)
    else
      Error (CInvalidAdtFunction lines)
  )\<close>
unfolding CInvalidAdtFunction_def parse_adt_function_def parse_adt_function.simps length_map 
    Let_def CAdtFunction_def String.explode_implode_eq drop_map
proof (rule if_cond_eq)
  assume len: "2 < length lines"
  have lines0: \<open>map literal.explode lines ! 0 = literal.explode (lines ! 0)\<close> 
    apply (rule nth_map)
    using len by force
  show "(if length (split CHR '':'' (map literal.explode lines ! 0)) = 2 then map_result_value2 (\<lambda>addr. AdtFunction addr (tl (butlast (map trim (split CHR '':'' (map literal.explode lines ! 0)) ! 1)))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (map literal.explode lines ! 0)) ! 0))) (flatten_error (map Parser.parse_adt_insn (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines))))) else Error (InvalidAdtFunction (map literal.explode lines))) = (if length (split CHR '':'' (literal.explode (lines ! 0))) = 2 then map_result_value2 (\<lambda>addr. AdtFunction addr (map String.ascii_of (tl (butlast (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1))))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 0))) (flatten_error (map Parser_Code.parse_adt_insn (map (map String.implode) (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines)))))) else Error ((InvalidAdtFunction \<circ> map literal.explode) lines))"
  unfolding lines0 proof (rule if_cond_eq)
    assume len: "length (split CHR '':'' (literal.explode (lines ! 0))) = 2"
    have lines1: \<open>map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1 = 
                  trim (split CHR '':'' (literal.explode (lines ! 0)) ! 1)\<close> 
      apply (rule nth_map)
      using len by force
    show "map_result_value2 (\<lambda>addr. AdtFunction addr (tl (butlast (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1)))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 0))) (flatten_error (map Parser.parse_adt_insn (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines))))) =
          map_result_value2 (\<lambda>addr. AdtFunction addr (map String.ascii_of (tl (butlast (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1))))) (map_result_error ParseNatError (nat_of_hex_string (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 0))) (flatten_error (map Parser_Code.parse_adt_insn (map (map String.implode) (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines))))))"
    proof (intro map_result_value2_inject flatten_error_arg_cong, rule arg_cong)
      fix x :: nat
      show "tl (butlast (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1)) = 
            map String.ascii_of (tl (butlast (map trim (split CHR '':'' (literal.explode (lines ! 0))) ! 1)))"
        unfolding lines1 map_butlast map_tl apply (subst ascii_of_explode_trim_split [symmetric])
        by (simp_all add: len)
    next
      show "map Parser.parse_adt_insn (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines))) =
            map Parser_Code.parse_adt_insn (map (map String.implode) (splitWhen (\<lambda>s. hd s = CHR ''('') (map literal.explode (drop 2 lines))))"
        unfolding list.map_comp implode_parse_adt_insn
        by (metis ascii_of_splitWhen list.map_comp)
    qed simp
  qed simp
qed simp


definition 
  parse_adt_section :: \<open>String.literal list \<Rightarrow> AdtSection parser_result\<close>
where
  \<open>parse_adt_section strs = Parser.parse_adt_section (map String.explode strs)\<close>

lemmas map_result_value_arg_cong = arg_cong2[where f = map_result_value]
lemmas AdtSection_arg_cong = arg_cong2[where f = AdtSection]


lemma ascii_of_list_split:
 \<open>map (map (map String.ascii_of)) (split x (map (map String.ascii_of) xs)) = split x (map (map String.ascii_of) xs)\<close>
proof (induct xs)
  case (Cons a xs)
  thus ?case
  proof (cases \<open>x = a\<close>)
    case True
    then show ?thesis 
      using Cons apply simp
      by (smt (verit, ccfv_threshold) ascii_of2 insert_hd.elims list.inject list.map_comp list.simps(8) list.simps(9) split_eq_char split_neq_char)
  next
    case False
    then show ?thesis 
      using Cons apply simp      
      by (smt (verit, ccfv_threshold) ascii_of2 insert_hd.elims list.inject list.map_comp list.simps(8) list.simps(9) split_eq_char split_neq_char)
  qed
qed simp

lemma ascii_of_explode_comp: \<open>map String.ascii_of \<circ> literal.explode = literal.explode\<close>
  by fastforce

lemma ascii_of_explode_list_split:
  \<open>map (map (map String.ascii_of)) (split x (map String.explode xs)) = split x (map String.explode xs)\<close>
  by (metis ascii_of_explode_comp ascii_of_list_split list.map_comp)

lemma [code]: \<open>parse_adt_section lines = (
    if (length lines > 1) then
      let 
        section_name = trim (drop (length section_preamble) (String.explode (lines ! 0)));
        function_lines = split [] (drop 2 (map String.explode lines));
        function_results = map parse_adt_function (map (map String.implode) function_lines);
        functions = flatten_error function_results
      in
        map_result_value (CAdtSection (String.implode section_name)) functions
    else 
      Error (CInvalidAdtSection lines)
  )\<close>
unfolding parse_adt_section_def CInvalidAdtSection_def CAdtSection_def Let_def 
          Parser.parse_adt_section.simps length_map drop_map
proof (rule if_cond_eq)
  assume len: "1 < length lines"
  have lines0: \<open>map literal.explode lines ! 0 = literal.explode (lines ! 0)\<close> 
    apply (rule nth_map)
    using len by force
  show "map_result_value (AdtSection (trim (drop (length section_preamble) (map literal.explode lines ! 0)))) (flatten_error (map Parser.parse_adt_function (split [] (map literal.explode (drop 2 lines))))) = 
        map_result_value (AdtSection (literal.explode (String.implode (trim (drop (length section_preamble) (literal.explode (lines ! 0))))))) (flatten_error (map Parser_Code.parse_adt_function (map (map String.implode) (split [] (map literal.explode (drop 2 lines))))))"
  unfolding lines0 String.explode_implode_eq list.map_comp implode_parse_adt_function
  proof (intro map_result_value_arg_cong flatten_error_arg_cong , rule arg_cong)
    show "trim (drop (length section_preamble) (literal.explode (lines ! 0))) = map String.ascii_of (trim (drop (length section_preamble) (literal.explode (lines ! 0))))"
      using ascii_of_explode ascii_of_trim drop_map
      by (smt (verit, del_insts) )
  next
    show "map Parser.parse_adt_function (split [] (map literal.explode (drop 2 lines))) = 
          map (Parser.parse_adt_function \<circ> map (map String.ascii_of)) (split [] (map literal.explode (drop 2 lines)))"
      by (metis ascii_of_explode_comp ascii_of_list_split list.map_comp)
  qed
qed simp

lemma implode_parse_adt_section: \<open>Parser_Code.parse_adt_section \<circ> map String.implode = Parser.parse_adt_section o (map (map String.ascii_of))\<close>
  unfolding parse_adt_section_def comp_def
  by (auto simp del: Parser.parse_adt_section.simps)

definition 
  parse_adt_program :: \<open>String.literal list \<Rightarrow> AdtSection list parser_result\<close>
where
  \<open>parse_adt_program strs = Parser.parse_adt_program (map String.explode strs)\<close>

lemma ascii_of_explode_splitOn':
  assumes \<open>(map String.explode xs') = xs\<close>
  shows \<open>map (map (map String.ascii_of)) (splitOn x xs) = splitOn x xs\<close>
using assms proof (induct arbitrary: xs' rule: splitOn.induct[of _ x xs])
  case (1 P x xs)
  then show ?case 
  proof (cases xs')
    case Nil
    then show ?thesis 
      using 1(2) by simp
  next
    case (Cons a list)
    show ?thesis
    proof (cases "dropWhile (\<lambda>y. \<not> P y) (x # xs)")
      case (Cons a' list')
      then show ?thesis 
        unfolding splitOn_Cons apply simp
        apply (intro conjI)
        apply (smt (verit, ccfv_SIG) "1.prems" Cons_eq_map_D ascii_of_explode_comp comp_def dropWhile_map)
        apply (smt (verit, ccfv_threshold) "1.prems" Cons_eq_map_D ascii_of_explode_comp dropWhile_map list.map_comp takeWhile_map)
        by (smt (verit) "1.hyps" "1.prems" Cons_eq_map_D dropWhile_map local.Cons)
    qed simp
  qed
qed simp

lemma ascii_of_explode_splitOn:
  \<open>map (map (map String.ascii_of)) (splitOn x (map String.explode xs)) = splitOn x (map String.explode xs)\<close>
  apply (rule ascii_of_explode_splitOn')
  by standard

lemma [code]:
  \<open>parse_adt_program lines = (
    let 
      section_lines = splitOn (prefix section_preamble) (map String.explode lines);
      section_results = map parse_adt_section (map (map String.implode) section_lines)
    in
      flatten_error section_results
  )\<close>
  unfolding parse_adt_program_def Let_def Parser.parse_adt_program.simps list.map_comp 
            implode_parse_adt_section
  apply (rule flatten_error_arg_cong)
  apply (subst ascii_of_explode_splitOn[symmetric])
  unfolding list.map_comp ..

definition
  symbol_table_function :: \<open>AdtFunction \<Rightarrow> String.literal \<times> nat\<close>
where
  \<open>symbol_table_function func = apfst String.implode (Parser.symbol_table_function func)\<close>

lemma [code]: \<open>symbol_table_function (CAdtFunction address label x) = (label, address)\<close>
  unfolding symbol_table_function_def CAdtFunction_def Let_def by auto

definition
  symbol_table_section :: \<open>AdtSection \<Rightarrow> (String.literal \<times> nat) list\<close>
where
  \<open>symbol_table_section section = map (apfst String.implode) (Parser.symbol_table_section section)\<close>

lemma [code]: 
  \<open>symbol_table_section (CAdtSection name funs) = (map symbol_table_function funs)\<close>
  unfolding symbol_table_section_def CAdtSection_def symbol_table_function_def by auto

definition
  get_symbol_table :: \<open>AdtSection list \<Rightarrow> (String.literal \<times> nat) list\<close>
where
  \<open>get_symbol_table secs = map (apfst String.implode) (Parser.get_symbol_table secs)\<close>

lemma [code]: \<open>get_symbol_table ast = fold (@) (map symbol_table_section ast) []\<close>
  unfolding get_symbol_table_def symbol_table_section_def apply auto
  apply (induct ast, auto)
  by (simp add: fold_append_concat_rev)

definition
  get_original_insn_insn :: \<open>AdtInsn \<Rightarrow> nat \<times> String.literal\<close>
where
  \<open>get_original_insn_insn insn = apsnd String.implode (Parser.get_original_insn_insn insn)\<close>

lemma [code]: \<open>get_original_insn_insn (CAdtInsn num bil str) = (num, str)\<close>
  unfolding get_original_insn_insn_def CAdtInsn_def Let_def by auto

definition
  get_original_insn_function :: \<open>AdtFunction \<Rightarrow> (nat \<times> String.literal) list\<close>
where
  \<open>get_original_insn_function fun = map (apsnd String.implode) (Parser.get_original_insn_function fun)\<close>

lemma [code]: \<open>get_original_insn_function (CAdtFunction adr name ast) = (map get_original_insn_insn ast)\<close>
  unfolding get_original_insn_function_def CAdtFunction_def get_original_insn_insn_def by auto

definition
  get_original_insn_section :: \<open>AdtSection \<Rightarrow> (nat \<times> String.literal) list\<close>
where
  \<open>get_original_insn_section section = 
      map (apsnd String.implode) (Parser.get_original_insn_section section)\<close>

lemma fold_append_concat_rev_empty[simp]: \<open>fold (@) xs [] = concat (rev xs)\<close>
  unfolding fold_append_concat_rev append.right_neutral ..

lemma [code]: 
  \<open>get_original_insn_section (CAdtSection str ast) = 
      fold (List.append) (map get_original_insn_function ast) []\<close>
  unfolding get_original_insn_section_def CAdtSection_def get_original_insn_function_def apply auto
  unfolding rev_map map_concat comp_def[symmetric] by auto

definition
  get_original_insn :: \<open>AdtSection list \<Rightarrow> (nat \<times> String.literal) list\<close>
where
  \<open>get_original_insn ast = map (apsnd String.implode) (Parser.get_original_insn ast)\<close>

lemma [code]: \<open>get_original_insn ast = fold (List.append) (map get_original_insn_section ast) []\<close>
  unfolding get_original_insn_def get_original_insn_section_def apply auto
  unfolding rev_map map_concat comp_def[symmetric] by auto

lemma [code]: \<open>get_prog_addr sz (CAdtInsn num bil str) = Word num sz\<close>
  unfolding CAdtInsn_def by simp

lemma [code]: \<open>get_prog_addrs_function sz (CAdtFunction num str bil) = map (get_prog_addr sz) bil\<close>
  unfolding CAdtFunction_def by simp

lemma [code]: \<open>get_prog_addrs_section sz (CAdtSection str funs) = 
    fold (@) (map (get_prog_addrs_function sz) funs) []\<close>
  unfolding CAdtSection_def by simp

lemma [code]:
  \<open>get_insn sza (CAdtInsn num bil str) sz = \<lparr> addr = Word num sza, size = Word sz sza, code = bil \<rparr>\<close>
  unfolding CAdtInsn_def by simp

lemma [code]:
  \<open>get_insns_function sza (CAdtFunction num str ast) = (
    let 
      words = (map (get_prog_addr sza) ast);
      addrs = (map (\<lambda>a. case a of Word sz _ \<Rightarrow> sz) words);
      szs = map (\<lambda>(a,b). b - a) (zip addrs (List.append (tl addrs) [0]))
    in
      map (\<lambda>(insn, sz). get_insn sza insn sz) (zip ast szs)
  )\<close>
  unfolding CAdtFunction_def by simp

lemma [code]:
  \<open>get_insns_section sz (CAdtSection str ast) = fold (@) (map (get_insns_function sz) ast) []\<close>
  unfolding CAdtSection_def by simp


definition 
  is_sub_in_list :: \<open>String.literal list \<Rightarrow> AdtFunction \<Rightarrow> bool\<close>
where
  \<open>is_sub_in_list lst = Parser.is_sub_in_list (map String.explode lst)\<close>

lemma code_is_sub_in_list[code]: \<open>is_sub_in_list lst (CAdtFunction adr name ast) = (name \<in> set lst)\<close>
  unfolding is_sub_in_list_def CAdtFunction_def apply simp
  by (simp add: image_iff literal.explode_inject)

definition 
  filter_subroutines_section :: \<open>String.literal list \<Rightarrow> AdtSection \<Rightarrow> AdtSection\<close>
where
  \<open>filter_subroutines_section str = Parser.filter_subroutines_section (map String.explode str)\<close>

lemma code_filter_subroutines_section[code]: 
  \<open>filter_subroutines_section lst (CAdtSection name ast) = (CAdtSection name (filter (is_sub_in_list lst) ast))\<close>
  unfolding filter_subroutines_section_def CAdtSection_def apply simp
  using is_sub_in_list_def by presburger

definition 
  filter_subroutines :: \<open>String.literal list \<Rightarrow> AdtSection list \<Rightarrow> AdtSection list\<close>
where
  \<open>filter_subroutines str = Parser.filter_subroutines (map String.explode str)\<close>

lemma code_filter_subroutines[code]: \<open>filter_subroutines lst ast = map (filter_subroutines_section lst) ast\<close>
  unfolding Parser_Code.filter_subroutines_def
  using filter_subroutines.simps filter_subroutines_section_def by presburger

definition 
  get_subroutine_addrs_function :: \<open>AdtFunction \<Rightarrow> (String.literal \<times> word list)\<close>
where
  \<open>get_subroutine_addrs_function adt = apfst String.implode (Parser.get_subroutine_addrs_function adt)\<close>

lemma get_subroutine_addrs_function_implode: \<open>get_subroutine_addrs_function = apfst String.implode \<circ>
         Parser.get_subroutine_addrs_function\<close>
  unfolding get_subroutine_addrs_function_def by auto

lemma [code]: \<open>get_subroutine_addrs_function (CAdtFunction adr name ast) 
  = (name, map (get_prog_addr 64) ast)\<close>
  unfolding get_subroutine_addrs_function_def Parser.get_subroutine_addrs_function.simps 
            CAdtFunction_def by auto

definition
  get_subroutine_addrs_section :: \<open>AdtSection \<Rightarrow> (String.literal \<times> word list) list\<close>
where
  \<open>get_subroutine_addrs_section ast = map (apfst String.implode) (Parser.get_subroutine_addrs_section ast)\<close>

lemma get_subroutine_addrs_section_implode: \<open>get_subroutine_addrs_section = map (apfst String.implode) \<circ>
    Parser.get_subroutine_addrs_section\<close>
  unfolding get_subroutine_addrs_section_def comp_def[symmetric] by auto

lemma [code]: \<open>get_subroutine_addrs_section (CAdtSection name ast) 
  = map get_subroutine_addrs_function ast\<close>
  unfolding get_subroutine_addrs_section_def Parser.get_subroutine_addrs_section.simps 
            CAdtSection_def list.map_comp get_subroutine_addrs_function_implode
  ..

definition
  get_subroutine_addrs :: \<open>AdtSection list \<Rightarrow> (String.literal \<times> word list) list\<close>
where
  \<open>get_subroutine_addrs ast = map (apfst String.implode) (Parser.get_subroutine_addrs ast)\<close>

lemma [code]: \<open>get_subroutine_addrs ast
  = fold (@) (map get_subroutine_addrs_section ast) []\<close>
  unfolding get_subroutine_addrs_def Parser.get_subroutine_addrs.simps 
  get_subroutine_addrs_section_implode
  by (simp add: map_concat rev_map)

code_datatype ParseNatError ParseIntError CParseArgumentError CStringMustBeQuoted CParseTagInvalid 
              CTagExistsError CInvalidAdtInsn CInvalidAdtFunction CInvalidAdtSection

(*parse_adt_program  *)
export_code parse_adt_program integer_of_int integer_of_nat nat_of_integer int_of_integer integer_of_char
            get_original_insn get_symbol_table get_prog_addrs get_insns String.implode
            filter_subroutines get_subroutine_addrs join parse_error_to_string in SML
  module_name AstParser file_prefix \<open>ast-parser\<close>
(*
integer_of_int integer_of_nat nat_of_integer int_of_integer integer_of_char
join
*)

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
        and ParseError = ParseNatError | ParseIntError | CParseArgumentError | CStringMustBeQuoted |
                         CParseTagInvalid | CTagExistsError | CInvalidAdtInsn | CInvalidAdtFunction |
                         CInvalidAdtSection
        and OfStringRadixError = EmptyString | InvalidRadix | InvalidCodepoint
        and insn_ext = insn_ext
  functions parse_adt_program integer_of_int integer_of_nat nat_of_integer int_of_integer integer_of_char
            get_original_insn get_symbol_table get_prog_addrs get_insns String.implode
            filter_subroutines get_subroutine_addrs join parse_error_to_string


end
