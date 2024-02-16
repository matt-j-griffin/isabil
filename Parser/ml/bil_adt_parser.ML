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
      val _ = tracing ("Parsing block with tid: " ^ Int.toString tid ^ " line: " ^ Substring.string ln)
    in
    case intFromHexString tid_str of
         SOME tid' =>
           if tid = tid' then (* We can skip this line *)
             parse_bilput_for tid lns (cnt + 1)
           else
             raise Fail ("Parser Error. Expected tid: '" ^ Int.fmt StringCvt.HEX tid ^ "' but found tid: '" ^ Int.fmt StringCvt.HEX tid')
       | NONE => or_raise (AstParser.parse_ast (Substring.string ln))
    end

fun parse_header ln =
  let
    val (tid_str, rest) = Substring.splitl is_colon (trim ln)
    val tid = intFromHexString_forced (Substring.full ("0x" ^ (Substring.string tid_str)))
    val (_, (label_str, _)) = splitlr is_lt is_gt rest
    val label_opt = (if Substring.isEmpty label_str then NONE else SOME (Substring.string (remove_outer label_str)))
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
      ((label, tid), (tid, parse_bilput_for tid lines 0))
    end

(**
 parse_bil_listing_blks
 ----------------------
 Parses a block in BIL listing, generating a list of pairs: (tid \<times> bil). 
 **)
val parse_bil_listing_blks = List.map parse_bil_listing_blk

datatype insn = Insn of LargeInt.int * LargeInt.int * AstParser.stmt list

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
val parse_bil_listing = group_insns 
  #> parse_bil_listing_blks 
  #> ListPair.unzip 
  #>> List.filter (fn (label_opt, _) => is_some label_opt)
  #>> List.map (fn tid_label => tid_label |>> the)
  ##> fix_insn_size

fun mk_prog addr = 
  HOLogic.mk_prod (@{term "\<Delta>::variables"}, HOLogic.mk_prod (IsaBIL.mk_word_of_int addr 64, @{term "mem::var"}))


fun mk_symbol_table lst =
  let 
    val term_lst = lst
      |> List.map (fn (label, tid) => (HOLogic.mk_string label, IsaBIL.mk_word_of_int tid 64)) 
      |> List.map HOLogic.mk_prod 
      |> HOLogic.mk_list @{typ "(string \<times> word)"}
  in
    Const ("Map.map_of", @{typ "(string \<times> word) list \<Rightarrow> string \<Rightarrow> word option"}) $ term_lst
  end

fun make_const_def (binding, trm) lthy = 
  let
    val lthy' =  snd ( Local_Theory.begin_nested lthy )
    val arg = ((binding, NoSyn), ((Thm.def_binding binding,@{attributes [code]}), trm)) 
    val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
  in
    (thm, Local_Theory.end_nested lthy'')
  end

fun bil_parser_lines localename assembly lthy =
  let   
    val thy = Local_Theory.exit_global lthy
    (* Build a locale name *)
    val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Given localename looks like qualified Isabelle ID: " ^ localename)
    val _ = localename <> "" orelse raise Fail ("Given localename is illegal")

    (* The locale fixes a predicate called "decode" of type "program \<Rightarrow> insn \<Rightarrow> bool" *)
    val fixes_decode = Element.Fixes [( Binding.name "decode" , SOME (@{typ "program \<Rightarrow> insn \<Rightarrow> bool"}), NoSyn)]

    (* the locale contains a list of assumptions, one for each instruction. They are given the [simp] attribute. *)
    val simp_attrib = Attrib.internal (Position.start) (fn (_) => Simplifier.simp_add)
    fun mk_assume thm_name term = ((Binding.name thm_name, [simp_attrib]), [term]); (* string -> term -> (binding * Token.src list) * term list*)
    
    val mk_decode = Free ("decode", @{typ "program \<Rightarrow> insn \<Rightarrow> bool"})
    fun mk_decode_equality_assume (Insn (tid,sz,bil)) =
      let val asm_name = "decode_" ^ LargeInt.fmt StringCvt.HEX tid
          val decode_term = (mk_decode $ (mk_prog tid) $ (IsaBIL.mk_insn tid sz bil))
      in
        mk_assume asm_name (HOLogic.Trueprop $ decode_term, [])
      end

    fun mk_addr_set insns = 
      let 
        val addrs = insns |> List.map (fn (Insn (w,_,_)) => IsaBIL.mk_word_of_int w 64)
      in
        HOLogic.mk_set (@{typ "word"}) addrs
      end
  

  val parse_as_locale = parse_bil_listing
    #>> mk_symbol_table

  val assembly = assembly 
    |> List.filter (Substring.full 
        #> Substring.explode 
        #> List.all Char.isSpace 
        #> not
       )
    |> List.filter ((fn s => String.isSubstring "Disassembly of section" s)
        #> not
       )
    |> List.map Substring.full


  (* Create a locale in the current theory with a fixed decode predicate and assumes for each 
     instruction *)
  val loc_bindings = Binding.name localename
    
    val (symbol_table, insns) = parse_as_locale assembly

    val loc_elems = [fixes_decode, Element.Assumes (List.map mk_decode_equality_assume insns)]
    val (_,lthy) = Expression.add_locale loc_bindings loc_bindings [] ([],[]) loc_elems thy
    val (_,lthy) = (make_const_def (Binding.name "sym_table", symbol_table)) lthy
    val (_,lthy) = (make_const_def (Binding.name "addr_set", mk_addr_set insns)) lthy

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

