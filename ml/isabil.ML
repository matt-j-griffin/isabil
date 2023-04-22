(*  Title:      ML/isabil.ML
    Author:     Matt Griffin, University of Surrey

Locale expressions and user interface layer of locales.
*)

datatype typ = Imm of int 
             | Mem of int * int  

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

type var = (string * typ)

datatype exp =
    (** Load    (mem,  idx,  endian,  size) *)
      Load    of exp * exp * endian * int
    (** Store   (mem,  idx,  val,  endian,  size) *)
    | Store   of exp * exp * exp * endian * int
    | BinOp   of binop * exp * exp
    | UnOp    of unop * exp
    | Var     of var
    | Int     of int * int
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

signature ISABIL =
sig

  val mk_typ: typ -> term
  val mk_en: endian -> term
  val mk_cast: cast -> term
  val mk_uop: unop -> term
  val mk_bop: binop -> term
  val mk_word: int -> int -> term
  val mk_exp: exp -> term
  val mk_stmt: stmt -> term
  val mk_bil: bil -> term
  val mk_insn: int -> int -> bil -> term

end;

structure IsaBIL : ISABIL =
struct

fun mk_typ (Imm sz) = @{term "Imm"} $ HOLogic.mk_number HOLogic.natT sz
  | mk_typ (Mem (sza, szv)) = @{term "Mem"} $ HOLogic.mk_number HOLogic.natT sza $ HOLogic.mk_number HOLogic.natT szv

fun mk_var (str, t) = @{term "var_constructor"} $ HOLogic.mk_string str $ mk_typ t

fun mk_en EL = @{term "LittleEndian"}
  | mk_en BE = @{term "BigEndian"}

fun mk_cast LOW = @{term "Low"}
  | mk_cast HIGH = @{term "High"}
  | mk_cast SIGNED = @{term "Signed"}
  | mk_cast UNSIGNED = @{term "Unsigned"}

fun mk_uop NOT = @{term "Not"}
  | mk_uop NEG = @{term "Neg"}

fun mk_bop PLUS = @{term "AOp Plus"}
  | mk_bop MINUS = @{term "AOp Minus"}
  | mk_bop TIMES = @{term "AOp Times"}
  | mk_bop DIVIDE = @{term "AOp Divide"}
  | mk_bop SDIVIDE = @{term "AOp SDivide"}
  | mk_bop MOD = @{term "AOp Mod"}
  | mk_bop SMOD = @{term "AOp SMod"}
  | mk_bop LSHIFT = @{term "AOp LShift"}
  | mk_bop RSHIFT = @{term "AOp RShift"}
  | mk_bop ARSHIFT = @{term "AOp ARShift"}
  | mk_bop AND = @{term "AOp And"}
  | mk_bop OR = @{term "AOp Or"}
  | mk_bop XOR = @{term "AOp Xor"}
  | mk_bop EQ = @{term "LOp Eq"}
  | mk_bop NEQ = @{term "LOp Neq"}
  | mk_bop LT = @{term "LOp Lt"}
  | mk_bop LE = @{term "LOp Le"}
  | mk_bop SLT = @{term "LOp Slt"}
  | mk_bop SLE = @{term "LOp Sle"}

fun mk_word nat sz = 
    Const ("Bitvector_Syntax.word_constructor_class.word_constructor", @{typ "nat \<Rightarrow> nat \<Rightarrow> word"}) $ HOLogic.mk_number HOLogic.natT nat $ HOLogic.mk_number HOLogic.natT sz

fun mk_exp (Load (e1, e2, en, sz)) = @{term "Load"} $ mk_exp e1  $ mk_exp e2 $ mk_en en $ HOLogic.mk_number HOLogic.natT sz
  | mk_exp (Store (e1, e2, e3, en, sz)) = @{term "Store"} $ mk_exp e1  $ mk_exp e2 $ mk_en en $ HOLogic.mk_number HOLogic.natT sz $ mk_exp e3
  | mk_exp (BinOp (bop, e1, e2)) = @{term "BinOp"} $ mk_exp e1 $ mk_bop bop $ mk_exp e2 
  | mk_exp (UnOp (uop, e1)) = @{term "UnOp"} $ mk_uop uop $ mk_exp e1
  | mk_exp (Var (str, t)) = Const ("BIL_Syntax.var_syntax_class.var_constructor", @{typ "string \<Rightarrow> Type \<Rightarrow> exp"}) $ HOLogic.mk_string str $ mk_typ t
  | mk_exp (Int (num, sz)) = Const ("Bitvector_Syntax.word_constructor_class.word_constructor", @{typ "nat \<Rightarrow> nat \<Rightarrow> exp"}) $ HOLogic.mk_number HOLogic.natT num $ HOLogic.mk_number HOLogic.natT sz
  | mk_exp (Cast (cast, int, e)) = @{term "Cast"} $ mk_cast cast $ HOLogic.mk_number HOLogic.natT int $ mk_exp e
  | mk_exp (Let ((str, t), e1, e2)) = @{term "Let"} $ (Const ("BIL_Syntax.var_syntax_class.var_constructor", @{typ "string \<Rightarrow> Type \<Rightarrow> var"}) $ HOLogic.mk_string str $ mk_typ t) $ mk_exp e1 $ mk_exp e2
  | mk_exp (Unknown (str, t)) = Const ("BIL_Syntax.unknown_constructor_class.unknown_constructor", @{typ "string \<Rightarrow> Type \<Rightarrow> exp"}) $ HOLogic.mk_string str $ mk_typ t
  | mk_exp (Ite (e1, e2, e3)) = @{term "Ite"} $ mk_exp e1  $ mk_exp e2 $ mk_exp e3
  | mk_exp (Extract (lo,hi,e)) = @{term "Extract"} $ HOLogic.mk_number HOLogic.natT lo  $ HOLogic.mk_number HOLogic.natT hi $ mk_exp e
  | mk_exp (Concat (e1, e2)) = @{term "Concat"} $ mk_exp e1  $ mk_exp e2

(**
 mk_bil
 ----------------------
 Converts ML/BIL to Isabelle/BIL 
 **)
fun mk_bil [] = @{term "Empty"}
  | mk_bil (stmt::bil) = @{term "Stmt"} $ mk_stmt stmt $ mk_bil bil  
and mk_stmt (CpuExn i) = @{term "CpuExn"} $ HOLogic.mk_number HOLogic.intT i
  | mk_stmt (Jmp e) = @{term "Jmp"} $ mk_exp e
  | mk_stmt (Special str) = @{term "Special"} $ HOLogic.mk_string str
  | mk_stmt (While (e,bil)) = @{term "While"} $ mk_exp e $ mk_bil bil
  | mk_stmt (If (e, bil1, bil2)) = @{term "If"} $ mk_exp e $ mk_bil bil1 $ mk_bil bil2
  | mk_stmt (Move ((str, t), e)) = @{term "Move"} $ (Const ("BIL_Syntax.var_syntax_class.var_constructor", @{typ "string \<Rightarrow> Type \<Rightarrow> var"}) $ HOLogic.mk_string str $ mk_typ t) $ mk_exp e

fun mk_insn addr sz bil = Const ("Instruction_Syntax.insn.make", @{typ "word \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> insn"}) $ (mk_word addr 64) $ (mk_word sz 64) $ mk_bil bil


end;
