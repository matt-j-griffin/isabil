theory Parser   
  imports "../OperationalSemantics/Program_Model" 
          Lexer
          "HOL-Library.Sublist"
          "Show.Show"
begin

abbreviation \<open>join lst \<equiv> fold (\<lambda>a b. (a @ '', '') @ b) (rev lst) []\<close>

datatype ParseError =
  ParseNatError \<open>nat OfStringRadixError\<close> |
  ParseIntError \<open>int OfStringRadixError\<close> | 
  ParseArgumentError string nat nat |
  ParseTagInvalid \<open>string list\<close> string |
  StringMustBeQuoted string |
  TagExistsError string |
  InvalidAdtInsn \<open>string list\<close> |
  InvalidAdtFunction \<open>string list\<close>

fun 
  parse_error_to_string :: \<open>ParseError \<Rightarrow> string\<close>
where
  \<open>parse_error_to_string (StringMustBeQuoted str) = List.append ''Expecting string wrapped in quotes, received: '' str\<close> |
  \<open>parse_error_to_string (TagExistsError tag) = List.append ''Expecting empty string before brackets, received: '' tag\<close> |
  \<open>parse_error_to_string (ParseNatError e) = of_string_radix_error_to_string e\<close> |
  \<open>parse_error_to_string (ParseIntError e) = of_string_radix_error_to_string e\<close> |
  \<open>parse_error_to_string (ParseArgumentError tag expected actual) = List.append (List.append ''Expecting X arguments for "'' tag) ''", got: Y''\<close> |
  \<open>parse_error_to_string (ParseTagInvalid others tag) = List.append (List.append (List.append ''Expecting one of ['' (join others)) ''], but received: '') tag\<close> |
  \<open>parse_error_to_string (InvalidAdtInsn lines) = List.append (List.append ''Expecting adt insn translation to contain two or three lines: ['' (join lines)) '']''\<close> |
  \<open>parse_error_to_string (InvalidAdtFunction lines) = List.append (List.append ''Expecting adt function to contain at least two lines: ['' (join lines)) '']''\<close>

type_synonym 'a parser_result = \<open>('a, ParseError) result\<close>

fun
  parse_nat_radix :: \<open>nat \<Rightarrow> AST \<Rightarrow> nat parser_result\<close>
where
  \<open>parse_nat_radix radix (Node str []) = map_result_error ParseNatError (nat_of_string_radix radix str)\<close> |
  \<open>parse_nat_radix radix (Node str (x # xs)) = Error (ParseArgumentError (List.append ''nat: '' str) 0 (length (x # xs)))\<close>

abbreviation \<open>parse_nat_dec \<equiv> parse_nat_radix 10\<close>

fun
  parse_int :: \<open>AST \<Rightarrow> int parser_result\<close>
where
  \<open>parse_int (Node str []) = map_result_error ParseIntError (int_of_string str)\<close> |
  \<open>parse_int (Node str (x # xs)) = Error (ParseArgumentError (List.append ''int: '' str) 0 (length (x # xs)))\<close>

fun 
  parse_str :: \<open>AST \<Rightarrow> string parser_result\<close>
where
  \<open>parse_str (Node str []) = (
    if (length str \<ge> 2 \<and> hd str = CHR ''"'' \<and> last str = CHR ''"'') then Value (map String.ascii_of (tl (butlast str)))
    else Error (StringMustBeQuoted str)
  )\<close> |
  \<open>parse_str (Node str (x # xs)) = Error (ParseArgumentError (List.append ''str: '' str) 0 (length (x # xs)))\<close>

function
  parse_en :: \<open>AST \<Rightarrow> Endian parser_result\<close>
where
  \<open>parse_en (Node ''LittleEndian'' []) = Value el\<close> |
  \<open>parse_en (Node ''LittleEndian'' (x # xs)) = Error (ParseArgumentError ''LittleEndian'' 0  (length (x # xs)))\<close> |
  \<open>parse_en (Node ''BigEndian'' []) = Value be\<close> |
  \<open>parse_en (Node ''BigEndian'' (x # xs)) = Error (ParseArgumentError ''BigEndian'' 0  (length (x # xs)))\<close> |
  \<open>\<lbrakk>en \<noteq> ''BigEndian''; en \<noteq> ''LittleEndian''\<rbrakk> \<Longrightarrow> parse_en (Node en _) = Error (ParseTagInvalid [''BigEndian'', ''LittleEndian''] en)\<close>
  subgoal for P x
    apply (cases x, auto)
    subgoal for str ast
      by (cases ast, auto)
    .
  by auto
termination by lexicographic_order

function
  parse_typ :: \<open>AST \<Rightarrow> Type parser_result\<close>
where
  \<open>parse_typ (Node ''Imm'' [sz]) = map_result_value Imm (parse_nat_dec sz)\<close> |
  \<open>parse_typ (Node ''Mem'' [sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m]) = map_result_value2 Mem (parse_nat_dec sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) (parse_nat_dec sz\<^sub>m\<^sub>e\<^sub>m)\<close> |
  \<open>\<lbrakk>length asts \<noteq> 1\<rbrakk> \<Longrightarrow> parse_typ (Node ''Imm'' asts) = Error (ParseArgumentError ''Imm'' 1 (length asts))\<close> |
  \<open>\<lbrakk>length asts \<noteq> 2\<rbrakk> \<Longrightarrow> parse_typ (Node ''Mem'' asts) = Error (ParseArgumentError ''Mem'' 2 (length asts))\<close> |
  \<open>\<lbrakk>typ \<noteq> ''Imm''; typ \<noteq> ''Mem''\<rbrakk> \<Longrightarrow> parse_typ (Node typ _) = Error (ParseTagInvalid [''Imm'', ''Mem''] typ)\<close>
  subgoal for P x 
    apply (cases x, auto)
    subgoal for t asts
      apply (cases \<open>t = ''Imm'' \<or> t = ''Mem''\<close>, auto)
      apply (cases asts rule: length1_cases, auto)
      by (cases asts rule: length2_cases, auto)
    .
  by auto
termination by lexicographic_order

function
  parse_var :: \<open>AST \<Rightarrow> var parser_result\<close>
where
  \<open>parse_var (Node ''Var'' [str, typ]) = map_result_value2 Var (parse_str str) (parse_typ typ)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_var (Node ''Var'' ast) = Error (ParseArgumentError ''Var'' 2 (length ast))\<close> |
  \<open>\<lbrakk>str \<noteq> ''Var''\<rbrakk> \<Longrightarrow> parse_var (Node str _) = Error (ParseTagInvalid [''Var''] str)\<close>
  subgoal for P x
    apply (cases x, auto)
    subgoal for str ast
      apply (cases \<open>str = ''Var''\<close>, auto)
      by (cases ast rule: length2_cases, auto)
    .
  by auto
termination by lexicographic_order

function
  parse_exp :: \<open>AST \<Rightarrow> exp parser_result\<close>
where
  \<open>parse_exp (Node ''Store'' [e\<^sub>1, e\<^sub>2, e\<^sub>3, en, sz]) = map_result_value5 Store (parse_exp e\<^sub>1) (parse_exp e\<^sub>2) (parse_en en) (parse_nat_dec sz) (parse_exp e\<^sub>3)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 5\<rbrakk> \<Longrightarrow> parse_exp (Node ''Store'' ast) = Error (ParseArgumentError ''Store'' 5 (length ast))\<close> |

  \<open>parse_exp (Node ''Load'' [e\<^sub>1, e\<^sub>2, en, sz]) = map_result_value4 Load (parse_exp e\<^sub>1) (parse_exp e\<^sub>2) (parse_en en) (parse_nat_dec sz)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 4\<rbrakk> \<Longrightarrow> parse_exp (Node ''Load'' ast) = Error (ParseArgumentError ''Load'' 4 (length ast))\<close> |

  \<open>parse_exp (Node ''Var'' asts) = map_result_value EVar (parse_var (Node ''Var'' asts))\<close> |

  \<open>parse_exp (Node ''Let'' [var, e\<^sub>1, e\<^sub>2]) = map_result_value3 Let (parse_var var) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Let'' ast) = Error (ParseArgumentError ''Let'' 3 (length ast))\<close> |

  \<open>parse_exp (Node ''Int'' [num, sz]) = map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat_dec num) (parse_nat_dec sz)))\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Int'' ast) = Error (ParseArgumentError ''Int'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''Unknown'' [str, t]) = map_result_value Val (map_result_value2 Unknown (parse_str str) (parse_typ t))\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Unknown'' ast) = Error (ParseArgumentError ''Unknown'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''NOT'' [e]) = map_result_value (UnOp Not) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_exp (Node ''NOT'' ast) = Error (ParseArgumentError ''NOT'' 1 (length ast))\<close> |

  \<open>parse_exp (Node ''NEG'' [e]) = map_result_value (UnOp Neg) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_exp (Node ''NEG'' ast) = Error (ParseArgumentError ''NEG'' 1 (length ast))\<close> |

  \<open>parse_exp (Node ''SLE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Sle) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SLE'' ast) = Error (ParseArgumentError ''SLE'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''SLT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Slt) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SLT'' ast) = Error (ParseArgumentError ''SLT'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''MINUS'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Minus) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''MINUS'' ast) = Error (ParseArgumentError ''MINUS'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''TIMES'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Times) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''TIMES'' ast) = Error (ParseArgumentError ''TIMES'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''DIVIDE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Divide) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''DIVIDE'' ast) = Error (ParseArgumentError ''DIVIDE'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''XOR'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Xor) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''XOR'' ast) = Error (ParseArgumentError ''XOR'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''OR'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Or) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''OR'' ast) = Error (ParseArgumentError ''OR'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''AND'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp And) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''AND'' ast) = Error (ParseArgumentError ''AND'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''MOD'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Mod) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''MOD'' ast) = Error (ParseArgumentError ''MOD'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''SMOD'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp SMod) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SMOD'' ast) = Error (ParseArgumentError ''SMOD'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''LT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Lt) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LT'' ast) = Error (ParseArgumentError ''LT'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''LE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Le) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LE'' ast) = Error (ParseArgumentError ''LE'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''NEQ'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Neq) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''NEQ'' ast) = Error (ParseArgumentError ''NEQ'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''PLUS'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Plus) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''PLUS'' ast) = Error (ParseArgumentError ''PLUS'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''EQ'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''EQ'' ast) = Error (ParseArgumentError ''EQ'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''RSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp RShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''RSHIFT'' ast) = Error (ParseArgumentError ''RSHIFT'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''ARSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp ARShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''ARSHIFT'' ast) = Error (ParseArgumentError ''ARSHIFT'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''LSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp LShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LSHIFT'' ast) = Error (ParseArgumentError ''LSHIFT'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''LOW'' [num, e]) = map_result_value2 (Cast Low) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LOW'' ast) = Error (ParseArgumentError ''LOW'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''HIGH'' [num, e]) = map_result_value2 (Cast High) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''HIGH'' ast) = Error (ParseArgumentError ''HIGH'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''UNSIGNED'' [num, e]) = map_result_value2 (Cast Unsigned) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''UNSIGNED'' ast) = Error (ParseArgumentError ''UNSIGNED'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''SIGNED'' [num, e]) = map_result_value2 (Cast Signed) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SIGNED'' ast) = Error (ParseArgumentError ''SIGNED'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''Ite'' [e\<^sub>1, e\<^sub>2, e\<^sub>3]) = map_result_value3 Ite (parse_exp e\<^sub>1) (parse_exp e\<^sub>2) (parse_exp e\<^sub>3)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Ite'' ast) = Error (ParseArgumentError ''Ite'' 3 (length ast))\<close> |

  \<open>parse_exp (Node ''Concat'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 Concat (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Concat'' ast) = Error (ParseArgumentError ''Concat'' 2 (length ast))\<close> |

  \<open>parse_exp (Node ''Extract'' [sz\<^sub>1, sz\<^sub>2, e]) = map_result_value3 Extract (parse_nat_dec sz\<^sub>1) (parse_nat_dec sz\<^sub>2) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Extract'' ast) = Error (ParseArgumentError ''Extract'' 3 (length ast))\<close> |

  \<open>\<lbrakk>e \<noteq> ''Store''; e \<noteq> ''Load''; e \<noteq> ''Var''; e \<noteq> ''Let''; e \<noteq> ''Int'';
    e \<noteq> ''Unknown''; e \<noteq> ''NOT''; e \<noteq> ''NEG''; e \<noteq> ''SLE''; e \<noteq> ''SLT''; 
    e \<noteq> ''MINUS''; e \<noteq> ''TIMES''; e \<noteq> ''DIVIDE''; e \<noteq> ''XOR''; e \<noteq> ''OR''; 
    e \<noteq> ''AND''; e \<noteq> ''MOD''; e \<noteq> ''SMOD''; e \<noteq> ''LT''; e \<noteq> ''LE''; e \<noteq> ''NEQ''; e \<noteq> ''PLUS''; e \<noteq> ''EQ''; 
    e \<noteq> ''RSHIFT''; e \<noteq> ''ARSHIFT''; e \<noteq> ''LSHIFT''; e \<noteq> ''LOW''; e \<noteq> ''HIGH''; 
    e \<noteq> ''UNSIGNED''; e \<noteq> ''SIGNED''; e \<noteq> ''Ite''; e \<noteq> ''Concat''; e \<noteq> ''Extract''
   \<rbrakk> \<Longrightarrow> parse_exp (Node e _) = Error (ParseTagInvalid [''Store'', ''Load'', ''Var'', ''Let'',
           ''Int'', ''Unknown'', ''NOT'', ''NEG'', ''SLE'', ''SLT'', ''MINUS'', ''TIMES'', ''DIVIDE'', ''XOR'', ''OR'',
           ''AND'', ''LT'', ''LE'', ''NEQ'', ''PLUS'', ''MOD'', ''SMOD'', ''EQ'', ''RSHIFT'', ''ARSHIFT'', ''LSHIFT'', ''LOW'', ''HIGH'',
           ''UNSIGNED'', ''SIGNED'', ''Ite'', ''Concat'', ''Extract''] e)\<close>
  subgoal for P x
    apply (cases x, safe) subgoal for str ast
    unfolding AST.simps apply (cases \<open>str = ''Store'' \<or> str = ''Load'' \<or> str = ''Var'' \<or> 
        str = ''Let'' \<or> str = ''Int'' \<or> str = ''Unknown'' \<or> str = ''NOT'' \<or> str = ''NEG'' \<or> 
        str = ''SLE'' \<or> str = ''SLT'' \<or> str = ''MINUS'' \<or> str = ''TIMES'' \<or> str = ''DIVIDE'' \<or> 
        str = ''XOR'' \<or> str = ''OR'' \<or> str = ''AND'' \<or> str = ''MOD'' \<or> str = ''SMOD'' \<or> 
        str = ''LT'' \<or> str = ''LE'' \<or> str = ''NEQ'' \<or> 
        str = ''PLUS'' \<or> str = ''EQ'' \<or> str = ''RSHIFT'' \<or> str = ''ARSHIFT'' \<or> str = ''LSHIFT'' \<or> 
        str = ''LOW'' \<or> str = ''HIGH'' \<or> str = ''UNSIGNED'' \<or> str = ''SIGNED'' \<or> str = ''Ite'' \<or> 
        str = ''Concat'' \<or> str = ''Extract''\<close>)
    apply safe
    apply auto
    apply (cases ast rule: length5_cases, auto)
    apply (cases ast rule: length4_cases, auto)
    apply (cases ast rule: length3_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length1_cases, auto)
    apply (cases ast rule: length1_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length3_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length3_cases, auto)
    done
  .
  apply simp_all
  by auto (* Takes a long time *)
termination by lexicographic_order

function
  parse_bil :: \<open>AST \<Rightarrow> bil parser_result\<close> and
  parse_stmt :: \<open>AST \<Rightarrow> stmt parser_result\<close>
where
  \<open>parse_bil (Node [] ast) = flatten_error (map parse_stmt ast)\<close> |
  \<open>parse_bil (Node (x # xs) _) = Error (TagExistsError (x # xs))\<close> |

  \<open>parse_stmt (Node ''Move'' [var, e]) = map_result_value2 Move (parse_var var) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Move'' ast) = Error (ParseArgumentError ''Move'' 2 (length ast))\<close> |

  \<open>parse_stmt (Node ''Jmp'' [e]) = map_result_value Jmp (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Jmp'' ast) = Error (ParseArgumentError ''Jmp'' 1 (length ast))\<close> |

  \<open>parse_stmt (Node ''CpuExn'' [num]) = map_result_value CpuExn (parse_int num)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''CpuExn'' ast) = Error (ParseArgumentError ''CpuExn'' 1 (length ast))\<close> |

  \<open>parse_stmt (Node ''Special'' [str]) = map_result_value Special (parse_str str)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Special'' ast) = Error (ParseArgumentError ''Special'' 1 (length ast))\<close> |

  \<open>parse_stmt (Node ''While'' [e\<^sub>1, bil]) = map_result_value2 While (parse_exp e\<^sub>1) (parse_bil bil)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_stmt (Node ''While'' ast) = Error (ParseArgumentError ''While'' 2 (length ast))\<close> |

  \<open>parse_stmt (Node ''If'' [e\<^sub>1, bil\<^sub>2, bil\<^sub>3]) = map_result_value3 If (parse_exp e\<^sub>1) (parse_bil bil\<^sub>2) (parse_bil bil\<^sub>3)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_stmt (Node ''If'' ast) = Error (ParseArgumentError ''If'' 3 (length ast))\<close> |

  \<open>\<lbrakk>ast \<noteq> ''Move''; ast \<noteq> ''Jmp''; ast \<noteq> ''CpuExn''; ast \<noteq> ''Special''; ast \<noteq> ''While''; 
    ast \<noteq> ''If''
   \<rbrakk> \<Longrightarrow> parse_stmt (Node ast _) = Error (ParseTagInvalid [''Move'', ''Jmp'', ''CpuExn'', 
           ''Special'', ''While'', ''If''] ast)\<close>
  subgoal for P x
    apply (cases x, auto)
    subgoal for ast apply (cases ast, auto)
      subgoal for val ast by (cases val, auto)
      .
    subgoal for ast apply (cases ast, auto)
      subgoal for val ast'
        apply (cases \<open>val = ''Move'' \<or> val = ''Jmp'' \<or> val = ''CpuExn'' \<or> val = ''Special'' \<or> val = ''While'' \<or> val = ''If''\<close>)
        apply auto
        apply (cases ast' rule: length2_cases, auto)
        apply (cases ast' rule: length1_cases, auto)
        apply (cases ast' rule: length1_cases, auto)
        apply (cases ast' rule: length1_cases, auto)
        apply (cases ast' rule: length2_cases, auto)
        apply (cases ast' rule: length3_cases, auto)
        done
      .
    .
  by auto
termination by lexicographic_order

definition \<open>parse_string = parse_bil o lexer\<close>

datatype AdtInsn = AdtInsn nat bil string

fun 
  parse_adt_insn' :: \<open>string list \<Rightarrow> AdtInsn parser_result\<close>
where
  \<open>parse_adt_insn' lines = (
    if (length lines = 2 \<or> length lines = 3) then
      let 
        lines' = if length lines = 3 then drop 1 lines else lines;
        headers = map trim (split (CHR '':'') (lines' ! 0));
        num = map_result_error ParseNatError (nat_of_hex_string (headers ! 0))
      in 
        map_result_value2 (\<lambda>addr bil. AdtInsn addr bil (headers ! 1)) num ((parse_bil o lexer)(lines' ! 1))
    else 
      Error (InvalidAdtInsn lines)
  )\<close>
(*
fun 
  parse_adt_insn :: \<open>string \<Rightarrow> AdtInsn parser_result\<close>
where
  \<open>parse_adt_insn str = parse_adt_insn' (map trim (split LF str))\<close>

lemma \<open>
parse_adt_insn ''10450: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66642,64)))'' 
= Value (AdtInsn 66640 [Move (Var ''X28'' (Imm 64)) (Val (Immediate (Word 66642 64)))]  ''auipc t3, 2'')
\<close>
  by auto
*)
datatype AdtFunction = AdtFunction nat string \<open>AdtInsn list\<close>

fun
  split_list :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list list\<close>
where
  split_list_Cons: \<open>split_list n (x # xs) = (case n of 0 \<Rightarrow> [] | Suc m \<Rightarrow> (take n (x # xs)) # split_list n (drop n (x # xs)))\<close> |
  split_list_Nil: \<open>split_list n [] = []\<close>

fun
  splitWhen :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list\<close>
where
  splitWhen_Cons: \<open>splitWhen P (x # xs) = (if P x then [x] # splitWhen P xs else insert_hd x (splitWhen P xs))\<close> |
  splitWhen_Nil: \<open>splitWhen _ [] = []\<close>


fun 
  parse_adt_function :: \<open>string list \<Rightarrow> AdtFunction parser_result\<close>
where
  \<open>parse_adt_function lines = (
      if (length lines > 2) then
        let 
          headers = map trim (split (CHR '':'') (lines ! 0));
          name = tl (butlast (headers ! 1));
          addr_result = map_result_error ParseNatError (nat_of_hex_string (headers ! 0));
          insn_lines = drop 2 lines;
          insn_grouped_lines = splitWhen (\<lambda>s. hd s = CHR ''('') insn_lines;
          insn_results = map parse_adt_insn' insn_grouped_lines;
          insns = flatten_error insn_results
        in
          map_result_value2 (\<lambda>addr insn. AdtFunction addr name insn) addr_result insns
      else 
        Error (InvalidAdtFunction lines)
  )\<close>
(*
fun 
  parse_AdtFunction :: \<open>string \<Rightarrow> AdtFunction parser_result\<close>
where
  \<open>parse_AdtFunction str = parse_adt_function (map trim (split LF str))\<close>


lemma \<open>
parse_AdtFunction 
''10460: <setlocale>
10460:
10460: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))
10461:
10461: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))''
= Value (AdtFunction 66656 ''setlocale'' [
    AdtInsn 66656 [Move (Var ''X28'' imm\<langle>64\<rangle>) (Val (Immediate (Word 66658 64)))] ''auipc t3, 2'', 
    AdtInsn 66657 [Move (Var ''X28'' imm\<langle>64\<rangle>) (Val (Immediate (Word 66658 64)))] ''auipc t3, 2''
  ]
)\<close>
  by auto
*)


(*

10464: ld t3, -1096(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550520,64)),LittleEndian(),64)))
10468: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66668,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66664,64))))
*)

datatype AdtSection = AdtSection string \<open>AdtFunction list\<close>

abbreviation \<open>section_preamble \<equiv> length ''Disassembly of section''\<close>


fun 
  parse_adt_section :: \<open>string list \<Rightarrow> AdtSection parser_result\<close>
where
  \<open>parse_adt_section lines = (
    let 
      section_name = trim (drop section_preamble (lines ! 0));
      function_lines = split [] (drop 2 lines);
      function_results = map parse_adt_function function_lines;
      functions = flatten_error function_results
    in
      map_result_value (\<lambda>fs. (AdtSection section_name fs)) functions
  )\<close>

(*
fun
  parse_adt_section' :: \<open>string \<Rightarrow> AdtSection parser_result\<close>
where
  \<open>parse_adt_section' str = parse_adt_section (map trim (split LF str))\<close>

lemma \<open>parse_adt_section
''Disassembly of section .plt

10450: <__libc_start_main>
10450:
10450: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66642,64)))
10454: ld t3, -1088(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550528,64)),LittleEndian(),64)))
10458: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66652,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66648,64))))
1045c:
1045c: nop
()

10460: <setlocale>
10460:
10460: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))
10464: ld t3, -1096(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550520,64)),LittleEndian(),64)))
10468: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66668,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66664,64))))
'' = Value (
  AdtSection ''.plt'' [
    AdtFunction 66640 ''__libc_start_main'' [
      AdtInsn 66640 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66642 64))] ''auipc t3, 2'',
      AdtInsn 66644 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate
             (Word 18446744073709550528
               64))), el]:u64] ''ld t3, -1088(t3)'',
      AdtInsn 66648
                [Var ''X6'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66652 64)),
                 jmp BinOp
                      (EVar (Var ''X28'' imm\<langle>64\<rangle>))
                      (AOp Plus)
                      (Val (Immediate (Word 66648 64)))] ''jalr t1, t3'',
      AdtInsn 66652 [] ''nop''],
    AdtFunction 66656 ''setlocale'' [
      AdtInsn 66656 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66658 64))] ''auipc t3, 2'',
      AdtInsn 66660 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550520 64))), el]:u64] ''ld t3, -1096(t3)'',
      AdtInsn 66664 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66668 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66664 64)))] ''jalr t1, t3'']] )\<close>
  unfolding Let_def by auto
*)

function
  splitOn :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list\<close>
where
  splitOn_Cons: \<open>splitOn P (x # xs) = (
      case dropWhile (\<lambda>y. \<not>P y) (x # xs) of
        (y # ys) \<Rightarrow> (y # takeWhile (\<lambda>y. \<not>P y) ys) # splitOn P ys |
        [] \<Rightarrow> []
  )\<close> |
  splitOn_Nil: \<open>splitOn _ [] = []\<close>
  by (pat_completeness, auto)
termination apply (standard)
  apply (rule wf_mlex[of \<open>measure (\<lambda>a. length (snd a))\<close> \<open>\<lambda>s. length (snd s)\<close>])
   apply auto
  apply (rule mlex_leq)
  apply auto
  subgoal for P x
  apply (cases "P x", auto)
  by (metis Suc_leD Suc_length_conv le_SucI length_dropWhile_le)
  by (metis length_Cons length_dropWhile_le less_Suc_eq less_eq_Suc_le)


fun 
  parse_adt_program :: \<open>string list \<Rightarrow> AdtSection list parser_result\<close>
where
  \<open>parse_adt_program lines = (
    let 
      section_lines = splitOn (prefix ''Disassembly of section'') lines;
      section_results = map parse_adt_section section_lines
    in
      flatten_error section_results
  )\<close>
(*
lemma [simp]: \<open>parse_adt_program
''
Disassembly of section .plt

10450: <__libc_start_main>
10450:
10450: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66642,64)))
10454: ld t3, -1088(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550528,64)),LittleEndian(),64)))
10458: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66652,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66648,64))))
1045c:
1045c: nop
()

Disassembly of section .text

10460: <setlocale>
10460:
10460: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))
10464: ld t3, -1096(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550520,64)),LittleEndian(),64)))
10468: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66668,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66664,64))))
'' = Value [
AdtSection ''.plt'' [
  AdtFunction 66640 ''__libc_start_main'' [
    AdtInsn 66640 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66642 64))] ''auipc t3, 2'',
    AdtInsn 66644 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550528 64))), el]:u64] ''ld t3, -1088(t3)''),
    AdtInsn 66648 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66652 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66648 64)))] ''jalr t1, t3'',
                 (adti_addr = 66652,
                    adti_code = [],
                    adti_orig = ''nop'')])]),
     (adts_name = ''.text'',
        adts_func =
          [(adtf_addr = 66656,
              adtf_name = ''setlocale'',
              adtf_insn =
                [(adti_addr = 66656,
                    adti_code =
                      [Var ''X28'' imm\<langle>64\<rangle> :=
                       Val (Immediate
    (Word 66658 64))],
                    adti_orig = ''auipc t3, 2''),
                 (adti_addr = 66660,
                    adti_code =
                      [Var ''X28'' imm\<langle>64\<rangle> :=
                       EVar
                        (Var ''mem''
 mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>))
              (AOp Plus)
              (Val (Immediate
                     (Word 18446744073709550520
                       64))), el]:u64],
                    adti_orig =
                      ''ld t3, -1096(t3)''),
                 (adti_addr = 66664,
                    adti_code =
                      [Var ''X6'' imm\<langle>64\<rangle> :=
                       Val (Immediate
    (Word 66668 64)),
                       jmp BinOp
   (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus)
   (Val (Immediate (Word 66664 64)))],
                    adti_orig =
                      ''jalr t1, t3'')])])]\<close>
  unfolding Let_def by auto
*)
(* Most of these should be sets/maps but those are real nasty in code generation so use lists instead temporarily*)
fun
  symbol_table_function :: \<open>AdtFunction \<Rightarrow> string \<times> nat\<close>
where
  \<open>symbol_table_function (AdtFunction address label _) = (label, address)\<close>

fun
  symbol_table_section :: \<open>AdtSection \<Rightarrow> (string \<times> nat) list\<close>
where
  \<open>symbol_table_section (AdtSection _ funs) = (map symbol_table_function funs)\<close>

fun
  get_symbol_table :: \<open>AdtSection list \<Rightarrow> (string \<times> nat) list\<close>
where
  \<open>get_symbol_table ast = fold (List.append) (map symbol_table_section ast) []\<close>
(*
lemma \<open>get_symbol_table [
AdtSection ''.plt'' [
  AdtFunction 66640 ''__libc_start_main'' [
    AdtInsn 66640 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66642 64))] ''auipc t3, 2'',
    AdtInsn 66644 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550528 64))), el]:u64] ''ld t3, -1088(t3)'',
    AdtInsn 66648 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66652 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66648 64)))] ''jalr t1, t3'', 
    AdtInsn 66652 [] ''nop''
  ]
],
AdtSection ''.text'' [
  AdtFunction 66656 ''setlocale'' [
    AdtInsn 66656 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66658 64))] ''auipc t3, 2'',
    AdtInsn 66660 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550520 64))), el]:u64] ''ld t3, -1096(t3)'',
    AdtInsn 66664 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66668 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66664 64)))] ''jalr t1, t3''
  ]
]
] = [''__libc_start_main'' \<mapsto> 66640, ''setlocale'' \<mapsto> 66656] \<close>
  by auto
*)

fun 
  get_prog_addr :: \<open>nat \<Rightarrow> AdtInsn \<Rightarrow> word\<close>
where
  \<open>get_prog_addr sz (AdtInsn num _ _) = Word num sz\<close>

fun 
  get_prog_addrs_function :: \<open>nat \<Rightarrow> AdtFunction \<Rightarrow> word list\<close>
where
  \<open>get_prog_addrs_function sz (AdtFunction _ _ bil) = map (get_prog_addr sz) bil\<close>

fun 
  get_prog_addrs_section :: \<open>nat \<Rightarrow> AdtSection \<Rightarrow> word list\<close>
where
  \<open>get_prog_addrs_section sz (AdtSection _ funs) = fold (List.append) (map (get_prog_addrs_function sz) funs) []\<close>


fun
  get_original_insn_insn :: \<open>AdtInsn \<Rightarrow> nat \<times> string\<close>
where
  \<open>get_original_insn_insn(AdtInsn num _ str) = (num, str)\<close>

fun
  get_original_insn_function :: \<open>AdtFunction \<Rightarrow> (nat \<times> string) list\<close>
where
  \<open>get_original_insn_function (AdtFunction _ _ ast) = (map get_original_insn_insn ast)\<close>

fun
  get_original_insn_section :: \<open>AdtSection \<Rightarrow> (nat \<times> string) list\<close>
where
  \<open>get_original_insn_section (AdtSection _ ast) = fold (List.append) (map get_original_insn_function ast) []\<close>

fun
  get_original_insn :: \<open>AdtSection list \<Rightarrow> (nat \<times> string) list\<close>
where
  \<open>get_original_insn ast = fold (List.append) (map get_original_insn_section ast) []\<close>
(*
lemma \<open>get_original_insn [
AdtSection ''.plt'' [
  AdtFunction 66640 ''__libc_start_main'' [
    AdtInsn 66640 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66642 64))] ''auipc t3, 2'',
    AdtInsn 66644 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550528 64))), el]:u64] ''ld t3, -1088(t3)'',
    AdtInsn 66648 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66652 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66648 64)))] ''jalr t1, t3'', 
    AdtInsn 66652 [] ''nop''
  ]
],
AdtSection ''.text'' [
  AdtFunction 66656 ''setlocale'' [
    AdtInsn 66656 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66658 64))] ''auipc t3, 2'',
    AdtInsn 66660 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550520 64))), el]:u64] ''ld t3, -1096(t3)'',
    AdtInsn 66664 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66668 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66664 64)))] ''jalr t1, t3''
  ]
]
] = [66664 \<mapsto> ''jalr t1, t3'', 66660 \<mapsto> ''ld t3, -1096(t3)'', 66656 \<mapsto> ''auipc t3, 2'', 66652 \<mapsto> ''nop'', 66648 \<mapsto> ''jalr t1, t3'', 66644 \<mapsto> ''ld t3, -1088(t3)'', 66640 \<mapsto> ''auipc t3, 2'']\<close>
  by auto
*)
fun 
  get_prog_addrs :: \<open>nat \<Rightarrow> AdtSection list \<Rightarrow> word list\<close>
where
  \<open>get_prog_addrs sz ast = fold (List.append) (map (get_prog_addrs_section sz) ast) []\<close>
(*
lemma \<open>get_prog_addrs [
AdtSection ''.plt'' [
  AdtFunction 66640 ''__libc_start_main'' [
    AdtInsn 66640 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66642 64))] ''auipc t3, 2'',
    AdtInsn 66644 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550528 64))), el]:u64] ''ld t3, -1088(t3)'',
    AdtInsn 66648 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66652 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66648 64)))] ''jalr t1, t3'', 
    AdtInsn 66652 [] ''nop''
  ]
],
AdtSection ''.text'' [
  AdtFunction 66656 ''setlocale'' [
    AdtInsn 66656 [Var ''X28'' imm\<langle>64\<rangle> := Val (Immediate (Word 66658 64))] ''auipc t3, 2'',
    AdtInsn 66660 [Var ''X28'' imm\<langle>64\<rangle> := EVar (Var ''mem'' mem\<langle>64, 8\<rangle>)[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550520 64))), el]:u64] ''ld t3, -1096(t3)'',
    AdtInsn 66664 [Var ''X6'' imm\<langle>64\<rangle> := Val (Immediate (Word 66668 64)), jmp BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66664 64)))] ''jalr t1, t3''
  ]
]
] = [66656, 66660, 66664, 66640, 66644, 66648, 66652]\<close>
  by auto
*)
fun
  get_insn :: \<open>nat \<Rightarrow> AdtInsn \<Rightarrow> nat \<Rightarrow> insn\<close>
where
  \<open>get_insn sza (AdtInsn num bil _) sz = \<lparr> addr = Word num sza, size = Word sz sza, code = bil \<rparr>\<close>


fun
  get_insns_function :: \<open>nat \<Rightarrow> AdtFunction \<Rightarrow> insn list\<close>
where
  \<open>get_insns_function sza (AdtFunction _ _ ast) = (
    let 
      words = (map (get_prog_addr sza) ast);
      addrs = (map (\<lambda>a. case a of Word sz _ \<Rightarrow> sz) words);
      szs = map (\<lambda>(a,b). b - a) (zip addrs (List.append (tl addrs) [0]))
    in
      map (\<lambda>(insn, sz). get_insn sza insn sz) (zip ast szs)
  )\<close>

fun
  get_insns_section :: \<open>nat \<Rightarrow> AdtSection \<Rightarrow> insn list\<close>
where
  \<open>get_insns_section sz (AdtSection _ ast) = fold (List.append) (map (get_insns_function sz) ast) []\<close>

fun
  get_insns :: \<open>nat \<Rightarrow> AdtSection list \<Rightarrow> insn list\<close>
where
  \<open>get_insns sz ast = fold (List.append) (map (get_insns_section sz) ast) []\<close>

lemma \<open>get_insns 64 [
AdtSection ''.plt'' [
  AdtFunction 66640 ''__libc_start_main'' [
    AdtInsn 66640 [(Var ''X28'' imm\<langle>64\<rangle>) := (Val (Immediate (Word 66642 64)))] ''auipc t3, 2'',
    AdtInsn 66644 [(Var ''X28'' imm\<langle>64\<rangle>) := ((EVar (Var ''mem'' mem\<langle>64, 8\<rangle>))[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550528 64))), el]:u64)] ''ld t3, -1088(t3)'',
    AdtInsn 66648 [(Var ''X6'' imm\<langle>64\<rangle>) := (Val (Immediate (Word 66652 64))), (jmp (BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66648 64)))))] ''jalr t1, t3'', 
    AdtInsn 66652 [] ''nop''
  ]
],
AdtSection ''.text'' [
  AdtFunction 66656 ''setlocale'' [
    AdtInsn 66656 [(Var ''X28'' imm\<langle>64\<rangle>) := (Val (Immediate (Word 66658 64)))] ''auipc t3, 2'',
    AdtInsn 66660 [(Var ''X28'' imm\<langle>64\<rangle>) := ((EVar (Var ''mem'' mem\<langle>64, 8\<rangle>))[BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 18446744073709550520 64))), el]:u64)] ''ld t3, -1096(t3)'',
    AdtInsn 66664 [(Var ''X6'' imm\<langle>64\<rangle>) := (Val (Immediate (Word 66668 64))), (jmp (BinOp (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus) (Val (Immediate (Word 66664 64)))))] ''jalr t1, t3''
  ]
]
] = z\<close>
  apply auto
  oops

fun 
  is_sub_in_list :: \<open>string list \<Rightarrow> AdtFunction \<Rightarrow> bool\<close>
where
  \<open>is_sub_in_list lst (AdtFunction _ name _) = (name \<in> set lst)\<close>

fun 
  filter_subroutines_section :: \<open>string list \<Rightarrow> AdtSection \<Rightarrow> AdtSection\<close>
where
  \<open>filter_subroutines_section lst (AdtSection name ast) = (AdtSection name (filter (is_sub_in_list lst) ast))\<close>

fun 
  filter_subroutines :: \<open>string list \<Rightarrow> AdtSection list \<Rightarrow> AdtSection list\<close>
where
  \<open>filter_subroutines lst adt = map (filter_subroutines_section lst) adt\<close>


fun 
  get_subroutine_addrs_function :: \<open>AdtFunction \<Rightarrow> (string \<times> word list)\<close>
where
  \<open>get_subroutine_addrs_function (AdtFunction _ name ast) = (name, map (get_prog_addr 64) ast)\<close>

fun 
  get_subroutine_addrs_section :: \<open>AdtSection \<Rightarrow> (string \<times> word list) list\<close>
where
  \<open>get_subroutine_addrs_section (AdtSection _ ast) = map get_subroutine_addrs_function ast\<close>


fun 
  get_subroutine_addrs :: \<open>AdtSection list \<Rightarrow> (string \<times> word list) list\<close>
where
  \<open>get_subroutine_addrs ast = fold List.append (map get_subroutine_addrs_section ast) []\<close>


end
