theory Parser   
  imports "../OperationalSemantics/Program_Model" Lexer

begin


fun
  parse_nat_radix :: \<open>nat \<Rightarrow> AST \<Rightarrow> nat parser_result\<close>
where
  \<open>parse_nat_radix radix (Node str []) = map_result_error (List.append (List.append ''Failed to parse string as nat: '' str)) (nat_of_string_radix radix str)\<close> |
  \<open>parse_nat_radix radix (Node str (x # xs)) = Error (List.append (List.append ''Expecting no arguments for type "nat" ('' str) ''), got many.'')\<close>

abbreviation \<open>parse_nat_dec \<equiv> parse_nat_radix 10\<close>

fun
  parse_int :: \<open>AST \<Rightarrow> int parser_result\<close>
where
  \<open>parse_int (Node str []) = map_result_error (List.append (List.append ''Failed to parse string as int: '' str)) (int_of_string str)\<close> |
  \<open>parse_int (Node str (x # xs)) = Error (List.append (List.append ''Expecting no arguments for type "int" ('' str) ''), got many.'')\<close>

fun 
  parse_str :: \<open>AST \<Rightarrow> string parser_result\<close>
where
  \<open>parse_str (Node str []) = (
    if (length str \<ge> 2 \<and> hd str = CHR ''"'' \<and> last str = CHR ''"'') then Value (map String.ascii_of (tl (butlast str)))
    else Error (List.append ''String "'' (List.append str  ''" must be wrapped in quotes.''))
  )\<close> |
  \<open>parse_str (Node str (x # xs)) = Error (List.append (List.append ''Expecting no arguments for type "str" ('' str) ''), got many.'')\<close>

function
  parse_en :: \<open>AST \<Rightarrow> Endian parser_result\<close>
where
  \<open>parse_en (Node ''LittleEndian'' []) = Value el\<close> |
  \<open>parse_en (Node ''LittleEndian'' (x # xs)) = Error ''Expecting no arguments for type "LittleEndian", got many.''\<close> |
  \<open>parse_en (Node ''BigEndian'' []) = Value be\<close> |
  \<open>parse_en (Node ''BigEndian'' (x # xs)) = Error ''Expecting no arguments for type "BigEndian", got many.''\<close> |
  \<open>\<lbrakk>en \<noteq> ''BigEndian'' \<and> en \<noteq> ''LittleEndian''\<rbrakk> \<Longrightarrow> parse_en (Node en _) = Error (List.append ''Expecting either BigEndian or LittleEndian but received: '' en)\<close>
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
  \<open>\<lbrakk>length asts \<noteq> 1\<rbrakk> \<Longrightarrow> parse_typ (Node ''Imm'' asts) = Error ''Expecting 1 argument for type "Imm", got many.''\<close> |
  \<open>\<lbrakk>length asts \<noteq> 2\<rbrakk> \<Longrightarrow> parse_typ (Node ''Mem'' asts) = Error ''Expecting 2 arguments for type "Mem", got many.''\<close> |
  \<open>\<lbrakk>typ \<noteq> ''Imm''; typ \<noteq> ''Mem''\<rbrakk> \<Longrightarrow> parse_typ (Node typ _) = Error (List.append ''Expecting either Imm or Mem but received: '' typ)\<close>
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
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_var (Node ''Var'' ast) = Error ''Expecting 2 arguments for type "Var", got many.''\<close> |
  \<open>\<lbrakk>str \<noteq> ''Var''\<rbrakk> \<Longrightarrow> parse_var (Node str _) = Error (List.append ''Expecting "Var" but received: '' str)\<close>
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
  \<open>\<lbrakk>length ast \<noteq> 5\<rbrakk> \<Longrightarrow> parse_exp (Node ''Store'' ast) = Error ''Expecting 5 arguments for type "Store", got many.''\<close> |

  \<open>parse_exp (Node ''Load'' [e\<^sub>1, e\<^sub>2, en, sz]) = map_result_value4 Load (parse_exp e\<^sub>1) (parse_exp e\<^sub>2) (parse_en en) (parse_nat_dec sz)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 4\<rbrakk> \<Longrightarrow> parse_exp (Node ''Load'' ast) = Error ''Expecting 4 arguments for type "Load", got many.''\<close> |

  \<open>parse_exp (Node ''Var'' asts) = map_result_value EVar (parse_var (Node ''Var'' asts))\<close> |

  \<open>parse_exp (Node ''Let'' [var, e\<^sub>1, e\<^sub>2]) = map_result_value3 Let (parse_var var) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Let'' ast) = Error ''Expecting 3 arguments for type "Let", got many.''\<close> |

  \<open>parse_exp (Node ''Int'' [num, sz]) = map_result_value Val (map_result_value Immediate (map_result_value2 Word (parse_nat_dec num) (parse_nat_dec sz)))\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Int'' ast) = Error ''Expecting 2 arguments for type "Int", got many.''\<close> |

  \<open>parse_exp (Node ''Unknown'' [str, t]) = map_result_value Val (map_result_value2 Unknown (parse_str str) (parse_typ t))\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Unknown'' ast) = Error ''Expecting 2 arguments for type "Unknown", got many.''\<close> |

  \<open>parse_exp (Node ''NOT'' [e]) = map_result_value (UnOp Not) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_exp (Node ''NOT'' ast) = Error ''Expecting 1 argument for type "NOT", got many.''\<close> |

  \<open>parse_exp (Node ''NEG'' [e]) = map_result_value (UnOp Neg) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_exp (Node ''NEG'' ast) = Error ''Expecting 1 argument for type "NEG", got many.''\<close> |

  \<open>parse_exp (Node ''SLE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Sle) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SLE'' ast) = Error ''Expecting 2 arguments for type "SLE", got many.''\<close> |

  \<open>parse_exp (Node ''SLT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Slt) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SLT'' ast) = Error ''Expecting 2 arguments for type "SLT", got many.''\<close> |

  \<open>parse_exp (Node ''MINUS'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Minus) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''MINUS'' ast) = Error ''Expecting 2 arguments for type "MINUS", got many.''\<close> |

  \<open>parse_exp (Node ''TIMES'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Times) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''TIMES'' ast) = Error ''Expecting 2 arguments for type "TIMES", got many.''\<close> |

  \<open>parse_exp (Node ''DIVIDE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Divide) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''DIVIDE'' ast) = Error ''Expecting 2 arguments for type "DIVIDE", got many.''\<close> |

  \<open>parse_exp (Node ''XOR'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Xor) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''XOR'' ast) = Error ''Expecting 2 arguments for type "XOR", got many.''\<close> |

  \<open>parse_exp (Node ''OR'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Or) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''OR'' ast) = Error ''Expecting 2 arguments for type "OR", got many.''\<close> |

  \<open>parse_exp (Node ''AND'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp And) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''AND'' ast) = Error ''Expecting 2 arguments for type "AND", got many.''\<close> |

  \<open>parse_exp (Node ''LT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Lt) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LT'' ast) = Error ''Expecting 2 arguments for type "LT", got many.''\<close> |

  \<open>parse_exp (Node ''LE'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Le) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LE'' ast) = Error ''Expecting 2 arguments for type "LE", got many.''\<close> |

  \<open>parse_exp (Node ''NEQ'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Neq) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''NEQ'' ast) = Error ''Expecting 2 arguments for type "NEQ", got many.''\<close> |

  \<open>parse_exp (Node ''PLUS'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp Plus) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''PLUS'' ast) = Error ''Expecting 2 arguments for type "PLUS", got many.''\<close> |

  \<open>parse_exp (Node ''EQ'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (LOp Eq) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''EQ'' ast) = Error ''Expecting 2 arguments for type "EQ", got many.''\<close> |

  \<open>parse_exp (Node ''RSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp RShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''RSHIFT'' ast) = Error ''Expecting 2 arguments for type "RSHIFT", got many.''\<close> |

  \<open>parse_exp (Node ''ARSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp ARShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''ARSHIFT'' ast) = Error ''Expecting 2 arguments for type "ARSHIFT", got many.''\<close> |

  \<open>parse_exp (Node ''LSHIFT'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 (\<lambda>e\<^sub>1 e\<^sub>2. BinOp e\<^sub>1 (AOp LShift) e\<^sub>2) (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LSHIFT'' ast) = Error ''Expecting 2 arguments for type "LSHIFT", got many.''\<close> |

  \<open>parse_exp (Node ''LOW'' [num, e]) = map_result_value2 (Cast Low) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''LOW'' ast) = Error ''Expecting 2 arguments for type "LOW", got many.''\<close> |

  \<open>parse_exp (Node ''HIGH'' [num, e]) = map_result_value2 (Cast High) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''HIGH'' ast) = Error ''Expecting 2 arguments for type "HIGH", got many.''\<close> |

  \<open>parse_exp (Node ''UNSIGNED'' [num, e]) = map_result_value2 (Cast Unsigned) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''UNSIGNED'' ast) = Error ''Expecting 2 arguments for type "UNSIGNED", got many.''\<close> |

  \<open>parse_exp (Node ''SIGNED'' [num, e]) = map_result_value2 (Cast Signed) (parse_nat_dec num) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''SIGNED'' ast) = Error ''Expecting 2 arguments for type "SIGNED", got many.''\<close> |

  \<open>parse_exp (Node ''Ite'' [e\<^sub>1, e\<^sub>2, e\<^sub>3]) = map_result_value3 Ite (parse_exp e\<^sub>1) (parse_exp e\<^sub>2) (parse_exp e\<^sub>3)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Ite'' ast) = Error ''Expecting 3 arguments for type "Ite", got many.''\<close> |

  \<open>parse_exp (Node ''Concat'' [e\<^sub>1, e\<^sub>2]) = map_result_value2 Concat (parse_exp e\<^sub>1) (parse_exp e\<^sub>2)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_exp (Node ''Concat'' ast) = Error ''Expecting 2 arguments for type "Concat", got many.''\<close> |

  \<open>parse_exp (Node ''Extract'' [sz\<^sub>1, sz\<^sub>2, e]) = map_result_value3 Extract (parse_nat_dec sz\<^sub>1) (parse_nat_dec sz\<^sub>2) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_exp (Node ''Extract'' ast) = Error ''Expecting 3 arguments for type "Extract", got many.''\<close> |

  \<open>\<lbrakk>e \<noteq> ''Store''; e \<noteq> ''Load''; e \<noteq> ''Var''; e \<noteq> ''Let''; e \<noteq> ''Int'';
    e \<noteq> ''Unknown''; e \<noteq> ''NOT''; e \<noteq> ''NEG''; e \<noteq> ''SLE''; e \<noteq> ''SLT''; 
    e \<noteq> ''MINUS''; e \<noteq> ''TIMES''; e \<noteq> ''DIVIDE''; e \<noteq> ''XOR''; e \<noteq> ''OR''; 
    e \<noteq> ''AND''; e \<noteq> ''LT''; e \<noteq> ''LE''; e \<noteq> ''NEQ''; e \<noteq> ''PLUS''; e \<noteq> ''EQ''; 
    e \<noteq> ''RSHIFT''; e \<noteq> ''ARSHIFT''; e \<noteq> ''LSHIFT''; e \<noteq> ''LOW''; e \<noteq> ''HIGH''; 
    e \<noteq> ''UNSIGNED''; e \<noteq> ''SIGNED''; e \<noteq> ''Ite''; e \<noteq> ''Concat''; e \<noteq> ''Extract''
   \<rbrakk> \<Longrightarrow> parse_exp (Node e _) = Error (List.append ''Expecting either "Store", "Load", "Var", "Let",
           "Int", "Unknown", "NOT", "NEG", "SLE", "SLT", "MINUS", "TIMES", "DIVIDE", "XOR", "OR",
           "AND", "LT", "LE", "NEQ", "PLUS", "EQ", "RSHIFT", "ARSHIFT", "LSHIFT", "LOW", "HIGH",
           "UNSIGNED", "SIGNED", "Ite", "Concat", "Extract" but received: '' e)\<close>
  subgoal for P x
    apply (cases x, safe) subgoal for str ast
    unfolding AST.simps apply (cases \<open>str = ''Store'' \<or> str = ''Load'' \<or> str = ''Var'' \<or> 
        str = ''Let'' \<or> str = ''Int'' \<or> str = ''Unknown'' \<or> str = ''NOT'' \<or> str = ''NEG'' \<or> 
        str = ''SLE'' \<or> str = ''SLT'' \<or> str = ''MINUS'' \<or> str = ''TIMES'' \<or> str = ''DIVIDE'' \<or> 
        str = ''XOR'' \<or> str = ''OR'' \<or> str = ''AND'' \<or> str = ''LT'' \<or> str = ''LE'' \<or> str = ''NEQ'' \<or> 
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
    apply (cases ast rule: length3_cases, auto)
    apply (cases ast rule: length2_cases, auto)
    apply (cases ast rule: length3_cases, auto)
    done
  .
  apply simp_all
  by auto
termination by lexicographic_order

function
  parse_bil :: \<open>AST \<Rightarrow> bil parser_result\<close> and
  parse_stmt :: \<open>AST \<Rightarrow> stmt parser_result\<close>
where
  \<open>parse_bil (Node [] ast) = flatten_error (map parse_stmt ast)\<close> |
  \<open>parse_bil (Node (x # xs) _) = Error (List.append ''Expecting empty string before brackets, received: '' (x # xs))\<close> |

  \<open>parse_stmt (Node ''Move'' [var, e]) = map_result_value2 Move (parse_var var) (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Move'' ast) = Error ''Expecting 2 arguments for type "Move", got many.''\<close> |

  \<open>parse_stmt (Node ''Jmp'' [e]) = map_result_value Jmp (parse_exp e)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Jmp'' ast) = Error ''Expecting 1 argument for type "Jmp", got many.''\<close> |

  \<open>parse_stmt (Node ''CpuExn'' [num]) = map_result_value CpuExn (parse_int num)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''CpuExn'' ast) = Error ''Expecting 1 argument for type "CpuExn", got many.''\<close> |

  \<open>parse_stmt (Node ''Special'' [str]) = map_result_value Special (parse_str str)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 1\<rbrakk> \<Longrightarrow> parse_stmt (Node ''Special'' ast) = Error ''Expecting 1 argument for type "Special", got many.''\<close> |

  \<open>parse_stmt (Node ''While'' [e\<^sub>1, bil]) = map_result_value2 While (parse_exp e\<^sub>1) (parse_bil bil)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 2\<rbrakk> \<Longrightarrow> parse_stmt (Node ''While'' ast) = Error ''Expecting 2 arguments for type "While", got many.''\<close> |

  \<open>parse_stmt (Node ''If'' [e\<^sub>1, bil\<^sub>2, bil\<^sub>3]) = map_result_value3 If (parse_exp e\<^sub>1) (parse_bil bil\<^sub>2) (parse_bil bil\<^sub>3)\<close> |
  \<open>\<lbrakk>length ast \<noteq> 3\<rbrakk> \<Longrightarrow> parse_stmt (Node ''If'' ast) = Error ''Expecting 3 arguments for type "If", got many.''\<close> |

  \<open>\<lbrakk>ast \<noteq> ''Move''; ast \<noteq> ''Jmp''; ast \<noteq> ''CpuExn''; ast \<noteq> ''Special''; ast \<noteq> ''While'';
    ast \<noteq> ''If''
   \<rbrakk> \<Longrightarrow> parse_stmt (Node ast _) = Error (List.append ''Expecting either "Move", "Jmp", "CpuExn", "Special", "While", "If" but received: '' ast)\<close>
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

record adt_insn = 
  adti_addr :: nat
  adti_code :: bil
  adti_orig :: string

fun 
  parse_adt_insn' :: \<open>string list \<Rightarrow> adt_insn parser_result\<close>
where
  \<open>parse_adt_insn' lines = (
    if (length lines = 2 \<or> length lines = 3) then
      let 
        lines' = if length lines = 3 then drop 1 lines else lines;
        headers = map trim (split (CHR '':'') (lines' ! 0))
      in 
        map_result_value2 (\<lambda>addr bil. \<lparr> adti_addr = addr, adti_code = bil, adti_orig = (headers ! 1) \<rparr>) (nat_of_hex_string (headers ! 0)) ((parse_bil o lexer)(lines' ! 1))
    else 
      Error (List.append ''Expecting adt insn translation to contain two or three lines'' '''')
  )\<close>

fun 
  parse_adt_insn :: \<open>string \<Rightarrow> adt_insn parser_result\<close>
where
  \<open>parse_adt_insn str = parse_adt_insn' (map trim (split LF str))\<close>

lemma \<open>
parse_adt_insn ''10450: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66642,64)))'' 
= Value \<lparr> 
  adti_addr = 66640, 
  adti_code = [Move (Var ''X28'' (Imm 64)) (Val (Immediate (Word 66642 64)))],
  adti_orig = ''auipc t3, 2''
\<rparr>\<close>
  by auto

record adt_function = 
  adtf_addr :: nat
  adtf_name :: string
  adtf_insn :: \<open>adt_insn list\<close>

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
  parse_adt_function' :: \<open>string list \<Rightarrow> adt_function parser_result\<close>
where
  \<open>parse_adt_function' lines = (
      if (length lines > 2) then
        let 
          headers = map trim (split (CHR '':'') (lines ! 0));
          name = tl (butlast (headers ! 1));
          addr_result = nat_of_hex_string (headers ! 0);
          insn_lines = drop 2 lines;
          insn_grouped_lines = splitWhen (\<lambda>s. hd s = CHR ''('') insn_lines;
          insn_results = map parse_adt_insn' insn_grouped_lines;
          insns = flatten_error insn_results
        in
          map_result_value2 (\<lambda>addr insn. \<lparr>adtf_addr = addr, adtf_name = name, adtf_insn = insn\<rparr>) addr_result insns
      else 
        Error (List.append ''Expecting adt function to contain at least two lines: '' '''')
  )\<close>

fun 
  parse_adt_function :: \<open>string \<Rightarrow> adt_function parser_result\<close>
where
  \<open>parse_adt_function str = parse_adt_function' (map trim (split LF str))\<close>


lemma \<open>
parse_adt_function 
''10460: <setlocale>
10460:
10460: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))
10461:
10461: auipc t3, 2
(Move(Var("X28",Imm(64)),Int(66658,64)))''
= Value \<lparr>
  adtf_addr = 66656, 
  adtf_name = ''setlocale'',
  adtf_insn = [\<lparr> 
    adti_addr = 66656, 
    adti_code = [Move (Var ''X28'' imm\<langle>64\<rangle>) (Val (Immediate (Word 66658 64)))],
    adti_orig = ''auipc t3, 2''
  \<rparr>, \<lparr> 
    adti_addr = 66657, 
    adti_code = [Move (Var ''X28'' imm\<langle>64\<rangle>) (Val (Immediate (Word 66658 64)))],
    adti_orig = ''auipc t3, 2''
  \<rparr>]
\<rparr>\<close>
  by auto


lemma \<open>tl (butlast (''<setlocale>'')) = ''setlocale''\<close>
  by auto


(*

10464: ld t3, -1096(t3)
(Move(Var("X28",Imm(64)),Load(Var("mem",Mem(64,8)),PLUS(Var("X28",Imm(64)),Int(18446744073709550520,64)),LittleEndian(),64)))
10468: jalr t1, t3
(Move(Var("X6",Imm(64)),Int(66668,64)), Jmp(PLUS(Var("X28",Imm(64)),Int(66664,64))))
*)

record adt_section = 
  adts_name :: string
  adts_func :: \<open>adt_function list\<close>

abbreviation \<open>section_preamble \<equiv> length ''Disassembly of section''\<close>


fun 
  parse_adt_section' :: \<open>string list \<Rightarrow> adt_section parser_result\<close>
where
  \<open>parse_adt_section' lines = (
    let 
      section_name = trim (drop section_preamble (lines ! 0));
      function_lines = split [] (drop 2 lines);
      function_results = map parse_adt_function' function_lines;
      functions = flatten_error function_results
    in
      map_result_value (\<lambda>fs. \<lparr> adts_name = section_name, adts_func = fs \<rparr>) functions
  )\<close>

fun
  parse_adt_section :: \<open>string \<Rightarrow> adt_section parser_result\<close>
where
  \<open>parse_adt_section str = parse_adt_section' (map trim (split LF str))\<close>

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
'' = Value \<lparr> adts_name = ''.plt'', adts_func = [\<lparr>adtf_addr = 66640,
        adtf_name = ''__libc_start_main'',
        adtf_insn =
          [\<lparr>adti_addr = 66640,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66642 64))],
              adti_orig = ''auipc t3, 2''\<rparr>,
           \<lparr>adti_addr = 66644,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 EVar
                  (Var ''mem''
                    mem\<langle>64, 8\<rangle>)[BinOp
      (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus)
      (Val (Immediate
             (Word 18446744073709550528
               64))), el]:u64],
              adti_orig = ''ld t3, -1088(t3)''\<rparr>,
           \<lparr>adti_addr = 66648,
              adti_code =
                [Var ''X6'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66652 64)),
                 jmp BinOp
                      (EVar (Var ''X28'' imm\<langle>64\<rangle>))
                      (AOp Plus)
                      (Val (Immediate
  (Word 66648 64)))],
              adti_orig = ''jalr t1, t3''\<rparr>,
           \<lparr>adti_addr = 66652, adti_code = [],
              adti_orig = ''nop''\<rparr>]\<rparr>,
     \<lparr>adtf_addr = 66656, adtf_name = ''setlocale'',
        adtf_insn =
          [\<lparr>adti_addr = 66656,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66658 64))],
              adti_orig = ''auipc t3, 2''\<rparr>,
           \<lparr>adti_addr = 66660,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 EVar
                  (Var ''mem''
                    mem\<langle>64, 8\<rangle>)[BinOp
      (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus)
      (Val (Immediate
             (Word 18446744073709550520
               64))), el]:u64],
              adti_orig = ''ld t3, -1096(t3)''\<rparr>,
           \<lparr>adti_addr = 66664,
              adti_code =
                [Var ''X6'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66668 64)),
                 jmp BinOp
                      (EVar (Var ''X28'' imm\<langle>64\<rangle>))
                      (AOp Plus)
                      (Val (Immediate
  (Word 66664 64)))],
              adti_orig = ''jalr t1, t3''\<rparr>]\<rparr>] \<rparr>\<close>
  unfolding Let_def by auto
(* TODO
fun 
  parse_adt_program :: \<open>string \<Rightarrow> adt_section list parser_result\<close>
where
  \<open>parse_adt_program str = (
    let 
      lines = map trim (split LF str);
      section_lines = splitWhile (\<lambda>s. s = ''Disassembly of section'') lines
      section_name = trim (drop section_preamble (lines ! 0));
      function_lines = split [] (drop 2 lines);
      function_results = map parse_adt_function' function_lines;
      functions = flatten_error function_results;
      y = map_result_value (\<lambda>fs. \<lparr> adts_name = section_name, adts_func = fs \<rparr>) functions
    in
      Value []
  )\<close>

lemma \<open>parse_adt_program
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
'' = Value \<lparr> adts_name = ''.plt'', adts_func = [\<lparr>adtf_addr = 66640,
        adtf_name = ''__libc_start_main'',
        adtf_insn =
          [\<lparr>adti_addr = 66640,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66642 64))],
              adti_orig = ''auipc t3, 2''\<rparr>,
           \<lparr>adti_addr = 66644,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 EVar
                  (Var ''mem''
                    mem\<langle>64, 8\<rangle>)[BinOp
      (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus)
      (Val (Immediate
             (Word 18446744073709550528
               64))), el]:u64],
              adti_orig = ''ld t3, -1088(t3)''\<rparr>,
           \<lparr>adti_addr = 66648,
              adti_code =
                [Var ''X6'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66652 64)),
                 jmp BinOp
                      (EVar (Var ''X28'' imm\<langle>64\<rangle>))
                      (AOp Plus)
                      (Val (Immediate
  (Word 66648 64)))],
              adti_orig = ''jalr t1, t3''\<rparr>,
           \<lparr>adti_addr = 66652, adti_code = [],
              adti_orig = ''nop''\<rparr>]\<rparr>,
     \<lparr>adtf_addr = 66656, adtf_name = ''setlocale'',
        adtf_insn =
          [\<lparr>adti_addr = 66656,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66658 64))],
              adti_orig = ''auipc t3, 2''\<rparr>,
           \<lparr>adti_addr = 66660,
              adti_code =
                [Var ''X28'' imm\<langle>64\<rangle> :=
                 EVar
                  (Var ''mem''
                    mem\<langle>64, 8\<rangle>)[BinOp
      (EVar (Var ''X28'' imm\<langle>64\<rangle>)) (AOp Plus)
      (Val (Immediate
             (Word 18446744073709550520
               64))), el]:u64],
              adti_orig = ''ld t3, -1096(t3)''\<rparr>,
           \<lparr>adti_addr = 66664,
              adti_code =
                [Var ''X6'' imm\<langle>64\<rangle> :=
                 Val (Immediate (Word 66668 64)),
                 jmp BinOp
                      (EVar (Var ''X28'' imm\<langle>64\<rangle>))
                      (AOp Plus)
                      (Val (Immediate
  (Word 66664 64)))],
              adti_orig = ''jalr t1, t3''\<rparr>]\<rparr>] \<rparr>\<close>
  unfolding Let_def by auto
*)

end
