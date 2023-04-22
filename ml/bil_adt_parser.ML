
structure BILADTParser : BIL_PARSER =
struct

(**
 parse_adt_cons
 ----------------------
 Parses the given substring as an ADT constructor

 example - parse_adt_cons "Example(1, Example(2))" \<Rightarrow> ("Example", ["1", "Example(2)"])
 **)
val parse_adt_cons = splitlr is_lbracket is_rbracket 
  ##> fst
  ##> remove_outer 
  ##> Substring.string 
  ##> splitXX

(**
 parse_adt_cons
 ----------------------
 Parses the given substring as an ADT constructor

 example - parse_adt_cons "Example(1, Example(2))" \<Rightarrow> ("Example", ["1", "Example(2)"])
 **)
fun parse_typ str =
  let
    val (name, args) = parse_adt_cons str
    (*val _ = tracing ("Parsing typ '" ^ Substring.string str ^ "'")*)
  in
    if Substring.string name = "Imm" then     
      Imm (intfromString_forced (Substring.string (List.nth (args, 0))))
    else if Substring.string name = "Mem" then
      Mem (intfromString_forced (Substring.string (List.nth (args, 0))), intfromString_forced (Substring.string (List.nth (args, 1))))
    else raise Fail ("Parser Error. Encountered invalid string '" ^ Substring.string str ^ "' when parsing type. Should be 'Imm' or 'Mem'")
  end

fun parse_var str: var =
  let
    val (name, args) = parse_adt_cons str
    (*val _ = tracing ("Parsing var '" ^ Substring.string str ^ "'")*)
  in
    if Substring.string name = "Var" then
      (Substring.string (remove_outer (List.nth (args, 0))), parse_typ (List.nth (args, 1)))
    else raise Fail ("Parser Error. Encountered invalid string '" ^ Substring.string str ^ "' when parsing var, should be 'Var'")
  end

fun parse_en str =
  if Substring.string str = "LittleEndian()" then EL
  else if Substring.string str = "BigEndian()" then BE
  else raise Fail ("Parser Error. Encountered invalid string '" ^ Substring.string str ^ "' when parsing endian, should be 'Little/BigEndian()'")

fun parse_exp str =
  let
    val (name, args) = parse_adt_cons str
    (*val _ = tracing ("Parsing exp '" ^ Substring.string str ^ "'")*)
  in
    if Substring.string name = "Store" then
      Store (parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)), 
             parse_exp (List.nth (args, 2)), parse_en (List.nth (args, 3)), 
             intfromString_forced (Substring.string (List.nth (args, 4))))
    else if Substring.string name = "Load" then
      Load (parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)), 
            parse_en (List.nth (args, 2)), 
            intfromString_forced (Substring.string (List.nth (args, 3))))

    else if Substring.string name = "Var" then
      Var (parse_var str)

    else if Substring.string name = "Let" then
      Let (parse_var (List.nth (args, 0)), parse_exp (List.nth (args, 1)), parse_exp (List.nth (args, 2)))

    else if Substring.string name = "Int" then
      Int ((intfromString_forced (Substring.string (List.nth (args, 0)))), (intfromString_forced (Substring.string (List.nth (args, 1)))))

    else if Substring.string name = "Unknown" then
      Unknown (Substring.string (remove_outer (List.nth (args, 0))), parse_typ (List.nth (args, 1)))

    else if Substring.string name = "NOT" then
      UnOp (NOT, parse_exp (List.nth (args, 0)))
    else if Substring.string name = "NEG" then
      UnOp (NEG, parse_exp (List.nth (args, 0)))

    else if Substring.string name = "SLE" then
      BinOp (SLE, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "SLT" then
      BinOp (SLT, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "MINUS" then
      BinOp (MINUS, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "TIMES" then
      BinOp (TIMES, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "DIVIDE" then
      BinOp (DIVIDE, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "XOR" then
      BinOp (XOR, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "OR" then
      BinOp (OR, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "AND" then
      BinOp (AND, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "LT" then
      BinOp (LT, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "LE" then
      BinOp (LE, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "NEQ" then
      BinOp (NEQ, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "PLUS" then
      BinOp (PLUS, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "EQ" then
      BinOp (EQ, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "RSHIFT" then
      BinOp (RSHIFT, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "ARSHIFT" then
      BinOp (ARSHIFT, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "LSHIFT" then
      BinOp (LSHIFT, parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "LOW" then
      Cast (LOW, intfromString_forced (Substring.string (List.nth (args, 0))), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "HIGH" then
      Cast (HIGH, intfromString_forced (Substring.string (List.nth (args, 0))), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "UNSIGNED" then
      Cast (UNSIGNED, intfromString_forced (Substring.string (List.nth (args, 0))), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "SIGNED" then
      Cast (SIGNED, intfromString_forced (Substring.string (List.nth (args, 0))), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "Ite" then
      Ite (parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)), parse_exp (List.nth (args, 2)))
    else if Substring.string name = "Concat" then
      Concat (parse_exp (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "Extract" then
      Extract (intfromString_forced (Substring.string (List.nth (args, 0))), 
               intfromString_forced (Substring.string (List.nth (args, 1))), 
               parse_exp (List.nth (args, 2)))

    else raise Fail ("Parser Error. Encountered invalid string '" ^ Substring.string name ^ "' when parsing exp.")
  end

(**
 parse_stmt
 ----------------------
 Parse a BIL statement read from a BIL listing. 
 arg{0} - the statement (as a string) to parse
 ret - a parsed BIL statement (stmt)
 **)
fun parse_stmt str = 
  let
    val (name, args) = parse_adt_cons str
    (*val _ = tracing ("Parsing stmt '" ^ Substring.string str ^ "'")*)
  in
    if Substring.string name = "Move" then
      Move (parse_var (List.nth (args, 0)), parse_exp (List.nth (args, 1)))
    else if Substring.string name = "Jmp" then
      Jmp (parse_exp (List.nth (args, 0)))
    else if Substring.string name = "CpuExn" then
      CpuExn (intfromString_forced (Substring.string (List.nth (args, 0))))
    else if Substring.string name = "If" then
      If (parse_exp (List.nth (args, 0)), parse_bil (List.nth (args, 1)), parse_bil (List.nth (args, 2)))
    else if Substring.string name = "Special" then
      Special (Substring.string (remove_outer (List.nth (args, 0))))
    else raise Fail ("Parser Error. Encountered invalid string '" ^ Substring.string name ^ "' when parsing stmt.")
  end
(**
 parse_bil
 ----------------------
 Parses a list of BIL statements read from a BIL listing, terminates when encountering '}'. 
 arg{0} - the lines of statements to parse
 ret - a list of the parsed BIL statements
 **)
and parse_bil str =  
  let 
    (*val _ = tracing ("Parsing bil '" ^ Substring.string str ^ "'")*)
  in
    str |> parse_adt_cons |> snd |> map parse_stmt
  end

end;


(**
 parse_bilput_for
 ----------------------
 Parses a BIL input file for the given tid read from a BIL listing, terminates when encounters a 
 list of BIL  statements. 
 arg{0} - the tid of the insn
 arg{1} - the lines of the insn to parse
 arg{2} - an aggregated count of meta lines for this insn
 ret - a list of the tids and parsed BIL statements
 **)
fun parse_bilput_for tid [] _ = raise Fail ("Parser Error. Expected '" ^ Int.toString tid ^ ": *' or 'bil' but input ended")
  | parse_bilput_for tid (ln::lns) cnt =
    let 
      val (tid_str,_)   = Substring.splitl is_colon (trim ln)
      (*val _ = tracing ("Parsing block with tid: " ^ Int.toString tid ^ " line: " ^ Substring.string ln)*)
    in
    case intFromHexString tid_str of
         SOME tid' =>
           if tid = tid' then (* We can skip this line *)
             parse_bilput_for tid lns (cnt + 1)
           else
             raise Fail ("Parser Error. Expected tid: '" ^ Int.fmt StringCvt.HEX tid ^ "' but found tid: '" ^ Int.fmt StringCvt.HEX tid')
       | NONE => BILADTParser.parse_bil ln
    end

fun parse_header ln =
  let
    val (tid_str, rest) = Substring.splitl is_colon (trim ln)
    val tid = intFromHexString_forced (Substring.full ("0x" ^ (Substring.string tid_str)))
    val (_, (label_str, _)) = splitlr is_lt is_gt rest
    val label_opt = (if Substring.isEmpty label_str then NONE else SOME (remove_outer label_str))
  in
    (tid, label_opt)    
  end

fun find_next_block [] = 0
  | find_next_block (ln::lns) = 
    if Substring.isSubstring ":" ln then
      1 + find_next_block lns
    else
      1


fun group_insns [] = [] 
  | group_insns (ln::lns) = 
    let
      val block_length = find_next_block lns
(*      val _ = tracing ("Parsing BIL: Found group starting at line: " ^ Substring.string ln ^ 
                       " and ending after " ^ Int.toString block_length ^ " lines.")*)
    in
      (ln::take (block_length) lns) :: group_insns (drop block_length lns)
    end

fun parse_bil_listing_blk [] = raise Fail("Parser Error: Encountered empty BIL block")
  | parse_bil_listing_blk (header::lines) = 
    let 
      val (tid, label) = parse_header header
      (*val _ = tracing ("Parsing block with tid: " ^ Int.toString tid)*)
    in
      ((tid, label), (tid, parse_bilput_for tid lines 0))
    end

(**
 parse_bil_listing_blks
 ----------------------
 Parses a block in BIL listing, generating a list of pairs: (tid \<times> bil). 
 **)
fun parse_bil_listing_blks [] = []
  | parse_bil_listing_blks (blk::blks) =
    let 

    in
      (parse_bil_listing_blk blk):: parse_bil_listing_blks blks
    end

datatype insn = Insn of LargeInt.int * LargeInt.int * bil

fun fix_insn_size [] = []
  | fix_insn_size [(tid, bil)] = [Insn (tid, 1, bil)]
  | fix_insn_size ((tid, bil)::(tid', bil')::bils) = 
     if tid' > tid then (* if this contains a jmp then the sz doesn't matter *)
       (Insn (tid, (tid' - tid), bil)) :: fix_insn_size ((tid', bil')::bils)
     else 
       (Insn (tid, 1, bil)) :: fix_insn_size ((tid', bil')::bils)



(**
 parse_bil_listing
 ----------------------
 Parses a BIL listing, generating a list of machine instructions. 
 **)
fun parse_bil_listing lns = 
  lns |> group_insns 
      |> parse_bil_listing_blks 
      |> Library.split_list 
      |>> List.filter (fn (_, label_opt) => is_some label_opt)
      |>> List.map (fn tid_label => tid_label ||> the)
      ||> fix_insn_size

fun bil_parser_lines localename assembly lthy =
  let   
    val thy = Local_Theory.exit_global lthy
    (* Build a locale name *)
    val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Given localename looks like qualified Isabelle ID: " ^ localename)
    val _ = localename <> "" orelse raise Fail ("Given localename is illegal")

  (* The locale fixes a predicate called "decode" of type "program \<Rightarrow> insn \<Rightarrow> bool" *)
  val fixes_decode = Element.Fixes [( Binding.name "decode" , SOME (@{typ "program \<Rightarrow> insn \<Rightarrow> bool"}), NoSyn)]

  (* the locale contains a list of assumptions, one for each instruction. They are given the [simp] attribute. *)
  val simp_attrib = Attrib.internal (fn (_) => Simplifier.simp_add)
  fun mk_assume thm_name term = ((Binding.name thm_name, [simp_attrib]), [term]);

  val mk_decode = Free ("decode", @{typ "program \<Rightarrow> insn \<Rightarrow> bool"})
  fun mk_prog addr = 
    HOLogic.mk_prod (@{term "\<Delta>::variables"}, HOLogic.mk_prod (IsaBIL.mk_word addr 64, @{term "mem::var"}))

  fun mk_decode_equality_assume (Insn (tid,sz,bil)) =
    let val asm_name = "decode_" ^ LargeInt.fmt StringCvt.HEX tid
        (*val _ = tracing("Creating: " ^ asm_name ^ " with sz: " ^ LargeInt.toString sz)*)
        val decode_term = (mk_decode $ (mk_prog tid) $ (IsaBIL.mk_insn tid sz bil))
    in
      mk_assume asm_name (HOLogic.Trueprop $ decode_term, [])
    end

  fun mk_label (tid, label: substring) = 
    let 
      val sanitized_label = label |> Substring.explode |> List.filter (fn x => x <> #".") |> String.implode
      val label_term = Free (sanitized_label, @{typ "word"})
      val label_eq_term = (HOLogic.mk_eq (label_term, IsaBIL.mk_word tid 64))
      val asm_name = sanitized_label ^ "_" ^ LargeInt.fmt StringCvt.HEX tid 
      val assm = mk_assume asm_name (HOLogic.Trueprop $ label_eq_term, [])
      val fix = (Binding.name sanitized_label, SOME (@{typ "word"}), NoSyn)
    in
      (fix, assm)
    end

  val parse_as_locale = parse_bil_listing
    #>> List.map mk_label
    #>> Library.split_list
    ##> List.map mk_decode_equality_assume

  val assembly = assembly 
    |> List.filter (Substring.full 
        #> Substring.explode 
        #> List.all Char.isSpace 
        #> not
       )
    |> List.filter ((fn s => String.isSubstring "Disassembly of section .text" s)
        #> not
       )
    |> List.map Substring.full


  (* Create a locale in the current theory with a fixed decode predicate and assumes for each 
     instruction *)
  val loc_bindings = Binding.name localename
    
    val ((fixes_label, label_assms), decode_assms) = parse_as_locale assembly

    val loc_elems = [fixes_decode, Element.Fixes fixes_label, Element.Assumes decode_assms, Element.Assumes label_assms] (*[mk_assume "TEST" (HOLogic.Trueprop $ (mk_decode $ @{term "prog::program"} $ @{term "insn::insn"}), []) *)
    val (_,lthy) = Expression.add_locale loc_bindings loc_bindings [] ([],[]) loc_elems thy
    val _ = tracing ("Added locale: " ^ localename ^ " with a decode predicate for " ^ Int.toString (length assembly) ^ " instructions. To get started, execute:\n\ncontext " ^ localename ^ "\nbegin\n   find_theorems decode\nend\n")

  in
   lthy
  end

fun bil_parser localename assembly lthy = bil_parser_lines localename (String.fields (fn c => c = #"\n") assembly) lthy

fun bil_file_parser localename assembly_file thy = 
  let 
    val ({lines, ...}:Token.file) = assembly_file thy
    val thy' = Named_Target.theory_map (bil_parser_lines localename lines) thy
  in
    thy'    
  end

