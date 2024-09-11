val syntax_simps = @{thms syntax_simps}


fun describe_string_error AstParser.EmptyString = "Cannot convert empty string"
  | describe_string_error (AstParser.InvalidRadixa _) = "The provided radix was too large (max 32)"
  | describe_string_error (AstParser.InvalidCodepointa (c, _)) = "Codepoint out of range for radix: "

(* TODO SHOULD BE CODEGEN *)
fun describe_parse_error (AstParser.ParseNatError en) = describe_string_error en
  | describe_parse_error (AstParser.ParseIntError ei) = describe_string_error ei
  | describe_parse_error (AstParser.ParseArgumentError (str, expected, actual)) = "Expecting X arguments for \"" ^ (AstParser.implode str) ^ "\", got: Y"
  | describe_parse_error (AstParser.StringMustBeQuoted str) = "Expecting string wrapped in quotes, received: " ^ AstParser.implode str
  | describe_parse_error (AstParser.ParseTagInvalid (strs, str)) = "Expecting one of [" ^ (AstParser.join (map AstParser.implode strs)) ^ "], but received: " ^ AstParser.implode str
  | describe_parse_error (AstParser.TagExistsError str) = "Expecting empty string before brackets, received: " ^ AstParser.implode str
  | describe_parse_error (AstParser.InvalidAdtInsn strs) = "Expecting adt insn translation to contain two or three lines: [" ^ (AstParser.join (map AstParser.implode strs)) ^ "]"
  | describe_parse_error (AstParser.InvalidAdtFunction strs) = "Expecting adt function to contain at least two lines: [" ^ (AstParser.join (map AstParser.implode strs)) ^ "]"

(**
 or_raise
 ----------------------
 If Value return it, otherwise throw the error.
 **)
fun or_raise _ (AstParser.Value v) = v
  | or_raise f (AstParser.Error e) = raise Fail (f e)

(**
 mk_prog
 ----------------------
 Make a BIL program with unbound variables in Isabelle/HOL. 
 arg{0} - the address of the program
 **)
fun mk_prog addr = 
  HOLogic.mk_prod (@{term "\<Delta>::variables"}, HOLogic.mk_prod (IsaBIL.mk_word addr, @{term "mem::var"}))

(**
 mk_symbol_table
 ----------------------
 Make a symbol table (map of strings to words) for a program in Isabelle/HOL. 
 arg{0} - a list of pairs, containing symbols (string) and their associated addresses (word)
 **)
fun mk_symbol_table lst =
  let 
    val term_lst = lst
      |> List.map (fn (label, tid) => (AstParser.implode label, AstParser.integer_of_nat tid)) 
      |> List.map (fn (label, tid) => (HOLogic.mk_string label, IsaBIL.mk_word_of_int tid 64)) 
      |> List.map HOLogic.mk_prod 
      |> HOLogic.mk_list @{typ "(string \<times> word)"}
  in
    Const ("Map.map_of", @{typ "(string \<times> word) list \<Rightarrow> string \<Rightarrow> word option"}) $ term_lst
  end

(**
 mk_original_table
 ----------------------
 Make a table of the original assembly instructions in Isabelle/HOL.
 arg{0} - a list of pairs, containing addresses (word) and the original instruction (string)
 **)
fun mk_original_table lst =
  let 
    val term_lst = lst
      |> List.map (fn (tid, label) => (AstParser.integer_of_nat tid, AstParser.implode label)) 
      |> List.map (fn (tid, label) => (IsaBIL.mk_word_of_int tid 64, HOLogic.mk_string label)) 
      |> List.map HOLogic.mk_prod 
      |> HOLogic.mk_list @{typ "(word \<times> string)"}
  in
    Const ("Map.map_of", @{typ "(word \<times> string) list \<Rightarrow> word \<Rightarrow> string option"}) $ term_lst
  end

(**
 make_const_def
 ----------------------
 Make a constant in Isabelle/HOL. 
 **)
fun make_const_def (binding, trm) lthy = 
  let
    val lthy' =  snd ( Local_Theory.begin_nested lthy )
    val arg = ((binding, NoSyn), ((Thm.def_binding binding,@{attributes [code]}), trm)) 
    val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
  in
    (thm, Local_Theory.end_nested lthy'')
  end

(**
 mk_addr_set
 ----------------------
 Make a set of addresses in the program in Isabelle/HOL. 
 arg{0} - a list of program words
 **)
fun mk_addr_set words = 
  let 
    val addrs = map IsaBIL.mk_word words 
  in
    HOLogic.mk_set (@{typ "word"}) addrs
  end

(**
 mk_decode_name
 ----------------------
 Make the name binding for decode in Isabelle/HOL. 
 arg{0} - The word associated with this decode
 **)
fun mk_decode_name (AstParser.Word (num, _)) = 
  "decode_" ^ LargeInt.fmt StringCvt.HEX (AstParser.integer_of_nat num)


fun mk_sz_word (AstParser.Word (num, sz)) =
  let
    val num_term = (if (AstParser.integer_of_nat num) = 0 then @{term "sz::nat"} else IsaBIL.mk_numeral_nat num)
  in
    @{term "Word"} $ num_term $ IsaBIL.mk_numeral_nat sz
  end

fun mk_insn (AstParser.Insn_ext (addr,sz,bil,_)) =
  Const ("Instruction_Syntax.insn.make", @{typ "word \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> insn"}) $ 
    (IsaBIL.mk_word addr) $ 
    (mk_sz_word sz) $ 
    IsaBIL.mk_bil bil

(**
 mk_original_table_def
 ----------------------
 Grab the original instructions (i.e. x86) from the AST as strings and put them in a map 
 (word \<rightarrow> string), add this to the target theory
 arg{0} - Theory to add the original table to
 arg{1} - The AST to generate the original table from
 **)
fun mk_original_table_def lthy ast =
  let 
    val orig_insns = AstParser.get_original_insn ast
    val orig_table_def = mk_original_table orig_insns
    val orig_binding = (Binding.name "orig_table", orig_table_def)
  in 
    make_const_def orig_binding lthy
  end;

(**
 make_decode_for_word
 ----------------------
 **)
fun make_decode_for_addr lthy addr =
  let 
    val asm_name = mk_decode_name addr;
    val thm = Proof_Context.get_thm lthy asm_name;
  in
    Local_Defs.unfold lthy syntax_simps thm
  end;

(**
 make_subroutine_decode
 ----------------------
 **)
fun make_subroutine_decode lthy (str, addrs) =
  let
    val name = "decode_" ^ AstParser.implode str
    val facts = map (make_decode_for_addr lthy) addrs
  in
    ((Binding.qualified_name name, []), [(facts, [])])
  end;

(**
 make_subroutine_decodes
 ----------------------
 **)
fun make_subroutine_decodes subs lthy = 
  Local_Theory.notes (map (make_subroutine_decode lthy) subs) lthy

(**
 bil_parser_lines
 ----------------------
 **)
fun bil_parser_lines localename assembly subroutines lthy =
  let   
    val thy = Local_Theory.exit_global lthy
    (* Build a locale name *)
    val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Given localename looks like qualified Isabelle ID: " ^ localename)
    val _ = localename <> "" orelse raise Fail ("Given localename is illegal")

    (* The locale fixes a predicate called "decode" of type "program \<Rightarrow> insn \<Rightarrow> bool" *)
    val fixes_decode = Element.Fixes [( Binding.name "decode" , SOME (@{typ "program \<Rightarrow> insn \<Rightarrow> bool"}), Infixr (Input.string "\<mapsto>\<^sub>b\<^sub>i\<^sub>l", 91, Position.no_range))]

    (* the locale contains a list of assumptions, one for each instruction. They are given the [simp] attribute. *)
    val simp_attrib = Attrib.internal (Position.start) (fn (_) => Simplifier.simp_add)
    fun mk_assume thm_name term = ((Binding.name thm_name, [simp_attrib]), [term]);
    
    val mk_decode = Free ("decode", @{typ "program \<Rightarrow> insn \<Rightarrow> bool"})
    fun mk_decode_equality_assume (insn as AstParser.Insn_ext (tid,_,_,_)) =
      let 
        val asm_name = mk_decode_name tid
        val decode_term = (mk_decode $ (mk_prog tid) $ (mk_insn insn))
      in
        mk_assume asm_name (HOLogic.Trueprop $ decode_term, [])
      end

    val _ = tracing ("Start time: " ^ Time.toString (Time.now()))

    val _ = tracing ("Parsing BIL AST")

    (* Parse AST using the code-generator *)
    val ast_unprocessed = assembly 
      |> AstParser.parse_ast
      |> or_raise describe_parse_error
 
    val _ = tracing ("Done parsing BIL" ^ Time.toString (Time.now()))
   
    val ast = if (List.null subroutines) 
      then 
        ast_unprocessed
      else
        (AstParser.filter_subroutines subroutines ast_unprocessed)

    val _ = tracing ("Done filtering BIL" ^ Time.toString (Time.now()))

    (* Architecture size, currently fixed - TODO specify as an option *)
    val arch_sz = (AstParser.nat_of_integer 64)

    (* Grab the instructions *)
    val insns = AstParser.get_insns arch_sz ast
    val _ = tracing ("Done grabbing instructions" ^ Time.toString (Time.now()))


    (* Create a locale in the current theory with a fixed decode predicate and assumes for each 
       instruction *)
    val _ = tracing ("Creating Isabelle/HOL Elements")
    val loc_bindings = Binding.name localename
    val decode_assumes = Element.Assumes (List.map mk_decode_equality_assume insns)    
    val _ = tracing ("Adding locale: " ^ Time.toString (Time.now()))
    val loc_elems = [fixes_decode, decode_assumes]
    val (_,lthy) = Expression.add_locale loc_bindings loc_bindings [] ([],[]) loc_elems thy
    val _ = tracing ("Done adding locale: " ^ Time.toString (Time.now()))

    (* Create the symbol table (in the locale) *)
    val symbol_table = AstParser.get_symbol_table ast
    val sym_table_def = mk_symbol_table symbol_table
    val (_,lthy) = (make_const_def (Binding.name "sym_table", sym_table_def)) lthy
    val _ = tracing ("Done adding symbol table: " ^ Time.toString (Time.now()))


    (* Create the program addresses (in the locale *)
    val addrs = AstParser.get_prog_addrs arch_sz ast
    val addr_set_def = mk_addr_set addrs
    val (_,lthy) = (make_const_def (Binding.name "addr_set", addr_set_def)) lthy
    val _ = tracing ("Done adding addr_set table: " ^ Time.toString (Time.now()))

    (* Grab the program addresses associated with each function (TODO with above for performance) *)
    val function_addrs = AstParser.get_subroutine_addrs ast
    val (_,lthy) = make_subroutine_decodes function_addrs lthy
    val _ = tracing ("Done adding subroutine decodes: " ^ Time.toString (Time.now()))

    (* Only include the original table if the include_asm option is set *)
    val include_asm = Config.get_global thy bil_include_asm
    val lthy = if include_asm then snd (mk_original_table_def lthy ast) else lthy
    val _ = tracing ("Done adding orig_table: " ^ Time.toString (Time.now()))

    val _ = tracing ("Added locale: " ^ localename ^ " with a decode predicate for " ^ Int.toString (length addrs) ^ " instructions. To get started, execute:\n\ncontext " ^ localename ^ "\nbegin\n   find_theorems decode\nend\n")
  in
    lthy
  end

fun bil_parser localename assembly subroutines lthy = bil_parser_lines localename (String.fields (fn c => c = #"\n") assembly) subroutines lthy

fun bil_file_parser localename assembly_file subroutines thy = 
  let 
    val ({lines, ...}:Token.file) = assembly_file thy
    val thy' = Named_Target.theory_map (bil_parser_lines localename lines subroutines) thy
  in
    thy'    
  end
