(* TODO rename BIR_Parse*)
theory BIL_Parse
  imports Program_Model
  keywords "BIR" :: thy_decl
       and "BIR_file" :: thy_load
begin


find_consts insn
print_record insn

lemma "insn.make (0 \<Colon> 0) (0 \<Colon> 0) Empty = no_insn" 
  unfolding make_def by auto

text \<open>BIR Parse, adds commands to parse BIR from strings (with BIR) or from files (with BIR_file)\<close>

ML \<open>
(*
fun mk_nat_numeral i =
  if i=0 then
    Const ("Groups.zero_class.zero", HOLogic.natT)
  else if i=1 then
    Const ("Groups.one_class.one", HOLogic.natT)
  else if i < 0 then
    raise Fail ("Failed to parse negative integer to number ^ Int.toString i")
  else
    Const ("Num.numeral_class.numeral", HOLogic.natT) $ HOLogic.mk_numeral i
*)                                                         

val intFromHexString = StringCvt.scanString (LargeInt.scan StringCvt.HEX) o Substring.string

fun intFromHexString_forced s =
    case intFromHexString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ Substring.string s ^ "' to int.")


type var = string;

datatype endian = 
      EL
    | BE

(** Different forms of casting *)
datatype cast =
      UNSIGNED (** 0-padding widening cast. *)
    | SIGNED   (** Sign-extending widening cast. *)
    | HIGH     (** Narrowning cast. Keeps the high bits. *)
    | LOW      (** Narrowing cast. Keeps the low bits. *)

datatype binop =
      PLUS    (** Integer addition. (commutative, associative) *)
    | MINUS   (** Subtract second integer from first. *)
    | TIMES   (** Integer multiplication. (commutative, associative) *)
    | DIVIDE  (** Unsigned integer division. *)
    | SDIVIDE (** Signed integer division. *)
    | MOD     (** Unsigned modulus. *)
    | SMOD    (** Signed modulus. *)
    | LSHIFT  (** Left shift. *)
    | RSHIFT  (** Right shift, fill with 0. *)
    | ARSHIFT (** Right shift, sign extend. *)
    | AND     (** Bitwise and. (commutative, associative) *)
    | OR      (** Bitwise or. (commutative, associative) *)
    | XOR     (** Bitwise xor. (commutative, associative) *)
    | EQ      (** Equals. (commutative) (associative on booleans) *)
    | NEQ     (** Not equals. (commutative) (associative on booleans) *)
    | LT      (** Unsigned less than. *)
    | LE      (** Unsigned less than or equal to. *)
    | SLT     (** Signed less than. *)
    | SLE     (** Signed less than or equal to. *)

datatype unop =
      NEG (** Negate. (2's complement) *)
    | NOT (** Bitwise not. *)

datatype exp =
    (** Load    (mem,  idx,  endian,  size) *)
      Load    of exp * exp * endian * int
    (** Store   (mem,  idx,  val,  endian,  size) *)
    | Store   of exp * exp * exp * endian * int
    | BinOp   of binop * exp * exp
    | UnOp    of unop * exp
    | Var     of var
    | Int     of word
    (** Cast to a new type *)
    | Cast    of cast * int * exp
    | Let     of var * exp * exp
    | Unknown of string * typ
    | Ite     of exp * exp * exp
    (** Extract hbits to lbits of e (Reg type) *)
    | Extract of int * int * exp
    (** Concat two reg expressions together *)
    | Concat  of exp * exp

datatype stmt =
    (** Assign the value on the right to the var on the left *)
      Move    of var * exp
    (** Jump to a address *)
    | Jmp     of exp
    (** Statement with semantics not expressible in BIL *)
    | Special of string
    | While   of exp * stmt list
    | If      of exp * stmt list * stmt list
    | CpuExn  of int

type bil = stmt list

datatype bir =
      Goto
    | WhenGoto 

datatype Instr = Instr of (LargeInt.int * LargeInt.int * string)

fun is_whitespace c = (c = #" " orelse c = #"\t"  orelse c = #"\n")

fun trim str =
  let val (_,x) = Substring.splitl is_whitespace str
      val (y,_) = Substring.splitr is_whitespace x in
    y
  end;

fun parse_instr si str =
  let (*val str'          = remove_comment (Substring.full str)*)
      val (addr,rem0)   = Substring.splitl (fn c => c <> #":") (Substring.full str)
      val a             = intFromHexString_forced (Substring.full ("0x" ^ Substring.string (trim addr)))
  in
    (Instr (a,si,"")) 
    (*parse_normal_instr a si rem0*)
  end;

fun read_instr_addr str =
  let val instr = parse_instr 0 str
      val (Instr (a,_,_)) = instr in
    a
  end
(*
fun parse_instr si str =
  let val (addr,rem0)   = Substring.splitl (fn c => c <> #":") str
      val a             = intFromHexString_forced (Substring.full ("0x" ^ Substring.string (trim addr)))
  in
    parse_normal_instr a si rem0
  end;
*)

fun main localename assembly lthy = let
  (* Build a locale name *)
  val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Given localename looks like qualified Isabelle ID: " ^ localename)
  val _ = localename <> "" orelse raise Fail ("Given localename is illegal")

  (* The locale fixes a predicate called "decode" of type "program \<Rightarrow> insn \<Rightarrow> bool" *)
  val fixes_decode = Element.Fixes [( Binding.name "decode" , SOME (@{typ "program \<Rightarrow> insn \<Rightarrow> bool"}), NoSyn)]


  (* the locale contains a list of assumptions, one for each instruction. They are given the [simp] attribute. *)
  val simp_attrib = Attrib.internal (fn (_) => Simplifier.simp_add)
  fun mk_assume thm_name term = ((Binding.name thm_name, [simp_attrib]), [term]);

  val mk_decode = Free ("decode", @{typ "program \<Rightarrow> insn \<Rightarrow> bool"})
  fun mk_word nat sz = 
    Const ("Bitvector_Syntax.word_constructor_class.word_constructor", @{typ "nat \<Rightarrow> nat \<Rightarrow> word"}) $ HOLogic.mk_number HOLogic.natT nat $ HOLogic.mk_number HOLogic.natT sz
  fun mk_insn addr sz bil = 
    Const ("Instruction_Syntax.insn.make", @{typ "word \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> insn"}) $ (mk_word addr 64) $ (mk_word sz 64) $ bil
  fun mk_prog addr = 
    HOLogic.mk_prod (@{term "\<Delta>::variables"}, HOLogic.mk_prod (mk_word addr 64, @{term "mem::var"}))

  fun mk_decode_equality_assume si str =
    let val instr = parse_instr si str
        val (Instr (a,_,_)) = instr
        val asm_name = "decode_" ^ LargeInt.toString a
        val decode_term = (mk_decode $ (mk_prog a) $ (mk_insn a si @{term "Empty"}))
        val _ = tracing ("Parse insn " ^ Int.toString a ^ " with sz: " ^ Int.toString si ^ ". insn = " ^ str)
    in
      mk_assume asm_name (HOLogic.Trueprop $ decode_term, [])
    end

  fun mk_decode_equality_assumes [] = []
    | mk_decode_equality_assumes [str] = [mk_decode_equality_assume 1 str]
    | mk_decode_equality_assumes (""::str1::strs) = (mk_decode_equality_assumes (str1::strs))
    | mk_decode_equality_assumes (str0::""::strs) = (mk_decode_equality_assume 0 str0) :: mk_decode_equality_assumes (strs)
    | mk_decode_equality_assumes (str0::str1::strs) = (mk_decode_equality_assume (read_instr_addr str1 - read_instr_addr str0) str0) :: mk_decode_equality_assumes (str1::strs)

                            
  val assembly = String.fields (fn c => c = #"\n") assembly (*|>
    List.filter (Substring.full (*#> remove_comment*) #> Substring.explode (*#> List.all Char.isSpace*) #> not)*)

  (* Create a locale in the current theory with a fixed decode predicate and assumes for each 
     instruction *)
  val loc_bindings = Binding.name localename
  val loc_elems = [fixes_decode, Element.Assumes (mk_decode_equality_assumes assembly)] (*[mk_assume "TEST" (HOLogic.Trueprop $ (mk_decode $ @{term "prog::program"} $ @{term "insn::insn"}), []) *)
  val thy = Local_Theory.exit_global lthy
  (*val loc_expr : (string, term) Expression.expr = [(Locale.intern thy "unknowns",(("",false),(Expression.Named [], [])))]*)
  val (_,lthy) = Expression.add_locale loc_bindings loc_bindings [] ([],[]) loc_elems thy


  val _ = tracing ("Added locale: " ^ localename ^ " with a decode predicate for " ^ Int.toString (length assembly) ^ " instructions. To get started, execute:\n\ncontext " ^ localename ^ "\nbegin\n   find_theorems decode\nend\n")

  in
   lthy
  end

val _ =
    Outer_Syntax.local_theory
      \<^command_keyword>\<open>BIR\<close>
      "Generate a locale from a list of BIL instructions."
      (Parse.embedded -- Parse.embedded >> (fn (localename, assembly) => main localename assembly))

\<close>

BIR hello \<open>
0001965a: sub foo(foo_result)
00019757: foo_result :: out u32 = low:32[RAX]

000144aa: 
000144ac: goto %0001341e

0001341e: 
00013428: mem := mem with [RSP + 8, el]:u32 <- low:32[RCX]
00013446: RSP := RSP - 0x18
0001346a: RAX := pad:64[mem[0x180008203]]
00013493: CF := mem[RSP + 0x20, el]:u32 < low:32[RAX]
000134b7: when ~CF  goto %000134b4
0001965c: goto %0001358e

000134b4: 
000134c6: RAX := 63:8[RAX].0
0001965b: goto %000134da

0001358e: 
0001359e: RAX := 0
000135b6: RCX := 0x180008201
000135c2: RAX := pad:64[mem[0x180008201]] read a\<^sub>1 from a\<^sub>1_addr
000135ce: mem := mem with [RSP] <- low:8[RAX] write a\<^sub>1 to stack
000135d8: RAX := pad:64[mem[RSP]]  read a\<^sub>1 from stack
000135e0: RCX := pad:64[mem[0x180008202]] read S
000135f6: #12582285 := extend:64[low:32[RAX]] * extend:64[low:32[RCX]] S * a\<^sub>1 = a\<^sub>1\<^sub>1'
000135fa: RAX := pad:64[low:32[#12582285]]
00013618: RAX := extend:64[low:32[RAX]]
0001361e: RCX := 0x1800081F8
0001362a: RAX := pad:64[mem[0x1800081F8 + RAX]] (* read a2 from a2_addr + S * a\<^sub>1 *)
00013652: #12582283 := mem[RSP + 0x20, el]:u32
00013657: RAX := pad:64[low:32[RAX] + #12582283] (* a2 + i *)
0001367c: goto %000134da

000134da: 
000134f9: RSP := RSP + 0x18
00013525: #12582287 := mem[RSP, el]:u64
00013529: RSP := RSP + 8
0001352c: call #12582287 with noreturn
\<close>

context hello
begin
find_theorems decode

lemma "\<And>k .decode a b"
  using decode_78878
  unfolding make_def sorry

end

end
