(*  Title:      ML/isabil.ML
    Author:     Matt Griffin, University of Surrey

Locale expressions and user interface layer of locales.
*)

signature ISABIL =
sig

  val mk_typ: AstParser.typea -> term
  val mk_en: AstParser.endian -> term
  val mk_cast: AstParser.cast -> term
  val mk_uop: AstParser.unOp -> term
  val mk_aop: AstParser.aOp -> term
  val mk_lop: AstParser.lOp -> term
  val mk_bop: AstParser.binOp -> term
  val mk_word_of_int: int -> int -> term
  val mk_word: AstParser.word -> term
  val mk_val: AstParser.vala -> term
  val mk_exp: AstParser.exp -> term
  val mk_stmt: AstParser.stmt -> term
  val mk_bil: AstParser.stmt list -> term
  val mk_insn: int -> int -> AstParser.stmt list -> term

end;

structure IsaBIL : ISABIL =
struct

(**
 mk_numeral_nat
 ----------------------
 Converts ML/BIL numeral nat to Isabelle/BIL 
 **)
fun mk_numeral_nat num = HOLogic.mk_number HOLogic.natT (AstParser.integer_of_nat num)

(**
 mk_numeral_nat
 ----------------------
 Converts ML/BIL numeral nat to Isabelle/BIL 
 **)
fun mk_numeral_int num = HOLogic.mk_number HOLogic.intT (AstParser.integer_of_int num)

(**
 mk_types
 ----------------------
 Converts ML/BIL types to Isabelle/BIL 
 **)
fun mk_typ (AstParser.Imm sz) = @{term "Imm"} $ mk_numeral_nat sz
  | mk_typ (AstParser.Mem (sza, szv)) = @{term "Mem"} $ mk_numeral_nat sza $ mk_numeral_nat szv

(**
 mk_var
 ----------------------
 Converts ML/BIL vars to Isabelle/BIL 
 **)
fun mk_var (AstParser.CVar (str, t)) = @{term "Var"} $ HOLogic.mk_string str $ mk_typ t

(**
 mk_en
 ----------------------
 Converts ML/BIL endians to Isabelle/BIL 
 **)
fun mk_en AstParser.LittleEndian = @{term "LittleEndian"}
  | mk_en AstParser.BigEndian = @{term "BigEndian"}

(**
 mk_casts
 ----------------------
 Converts ML/BIL casts to Isabelle/BIL 
 **)
fun mk_cast AstParser.Low = @{term "Low"}
  | mk_cast AstParser.High = @{term "High"}
  | mk_cast AstParser.Signed = @{term "Signed"}
  | mk_cast AstParser.Unsigned = @{term "Unsigned"}

(**
 mk_uop
 ----------------------
 Converts ML/BIL uops to Isabelle/BIL 
 **)
fun mk_uop AstParser.Not = @{term "Not"}
  | mk_uop AstParser.Neg = @{term "Neg"}

(**
 mk_aop
 ----------------------
 Converts ML/BIL aops to Isabelle/BIL 
 **)
fun mk_aop AstParser.Plus = @{term "Plus"}
  | mk_aop AstParser.Minus = @{term "Minus"}
  | mk_aop AstParser.Times = @{term "Times"}
  | mk_aop AstParser.Divide = @{term "Divide"}
  | mk_aop AstParser.SDivide = @{term "SDivide"}
  | mk_aop AstParser.Mod = @{term "Mod"}
  | mk_aop AstParser.SMod = @{term "SMod"}
  | mk_aop AstParser.LShift = @{term "LShift"}
  | mk_aop AstParser.RShift = @{term "RShift"}
  | mk_aop AstParser.ARShift = @{term "ARShift"}
  | mk_aop AstParser.And = @{term "And"}
  | mk_aop AstParser.Or = @{term "Or"}
  | mk_aop AstParser.Xor = @{term "Xor"}

(**
 mk_lop
 ----------------------
 Converts ML/BIL lops to Isabelle/BIL 
 **)
fun mk_lop AstParser.Eq = @{term "Eq"}
  | mk_lop AstParser.Neq = @{term "Neq"}
  | mk_lop AstParser.Lt = @{term "Lt"}
  | mk_lop AstParser.Le = @{term "Le"}
  | mk_lop AstParser.Slt = @{term "Slt"}
  | mk_lop AstParser.Sle = @{term "Sle"}

(**
 mk_bop
 ----------------------
 Converts ML/BIL bops to Isabelle/BIL 
 **)
fun mk_bop (AstParser.AOp aop) = @{term "AOp"} $ mk_aop aop
  | mk_bop (AstParser.LOp lop) = @{term "LOp"} $ mk_lop lop

(**
 mk_word
 ----------------------
 Converts ML/BIL words to Isabelle/BIL 
 **)
fun mk_word (AstParser.Word (num, sz)) = @{term "Word"} $ mk_numeral_nat num $ mk_numeral_nat sz


(**
 mk_word_of_int 
 ----------------------
 Converts ML int pair to Isabelle/BIL words
**)
fun mk_word_of_int num sz = mk_word (AstParser.Word (AstParser.nat_of_integer num, AstParser.nat_of_integer sz))

(**
 mk_vala
 ----------------------
 Converts ML/BIL values to Isabelle/BIL 
 **)
fun mk_val (AstParser.Immediate w) = @{term "Immediate"} $ mk_word w
  | mk_val (AstParser.Storage (v, w, v', sz)) = @{term "Storage"} $ mk_val v $ mk_word w $ mk_val v' $ mk_numeral_nat sz
  | mk_val (AstParser.CUnknown (str, t)) = @{term "Unknown"} $ HOLogic.mk_string str $ mk_typ t

(**
 mk_exp
 ----------------------
 Converts ML/BIL expressions to Isabelle/BIL 
 **)
fun mk_exp (AstParser.Load (e1, e2, en, sz)) = @{term "Load"} $ mk_exp e1  $ mk_exp e2 $ mk_en en $ mk_numeral_nat sz
  | mk_exp (AstParser.Store (e1, e2, en, sz, e3)) = @{term "Store"} $ mk_exp e1  $ mk_exp e2 $ mk_en en $ mk_numeral_nat sz $ mk_exp e3
  | mk_exp (AstParser.BinOp (e1, bop, e2)) = @{term "BinOp"} $ mk_exp e1 $ mk_bop bop $ mk_exp e2 
  | mk_exp (AstParser.UnOp (uop, e1)) = @{term "UnOp"} $ mk_uop uop $ mk_exp e1
  | mk_exp (AstParser.EVar var) = @{term "EVar"} $ mk_var var
  | mk_exp (AstParser.Cast (cast, int, e)) = @{term "Cast"} $ mk_cast cast $ mk_numeral_nat int $ mk_exp e
  | mk_exp (AstParser.Let (var, e1, e2)) = @{term "Let"} $ mk_var var $ mk_exp e1 $ mk_exp e2
  | mk_exp (AstParser.Ite (e1, e2, e3)) = @{term "Ite"} $ mk_exp e1 $ mk_exp e2 $ mk_exp e3
  | mk_exp (AstParser.Extract (lo,hi,e)) = @{term "Extract"} $ mk_numeral_nat lo $ mk_numeral_nat hi $ mk_exp e
  | mk_exp (AstParser.Concat (e1, e2)) = @{term "Concat"} $ mk_exp e1 $ mk_exp e2
  | mk_exp (AstParser.Val v) = @{term "Val"} $ mk_val v

(**
 mk_bil, mk_stmt
 ----------------------
 Converts ML/BIL sequences and statements to Isabelle/BIL 
 **)
fun mk_bil bil = HOLogic.mk_list @{typ "stmt"} (List.map mk_stmt bil)
and mk_stmt (AstParser.CpuExn i) = @{term "CpuExn"} $ mk_numeral_int i
  | mk_stmt (AstParser.Jmp e) = @{term "Jmp"} $ mk_exp e
  | mk_stmt (AstParser.CSpecial str) = @{term "Special"} $ HOLogic.mk_string str
  | mk_stmt (AstParser.While (e,bil)) = @{term "While"} $ mk_exp e $ mk_bil bil
  | mk_stmt (AstParser.If (e, bil1, bil2)) = @{term "If"} $ mk_exp e $ mk_bil bil1 $ mk_bil bil2
  | mk_stmt (AstParser.Move (var, e)) = @{term "Move"} $ mk_var var $ mk_exp e

fun mk_insn addr sz bil = Const ("Instruction_Syntax.insn.make", @{typ "word \<Rightarrow> word \<Rightarrow> bil \<Rightarrow> insn"}) $ (mk_word_of_int addr 64) $ (mk_word_of_int sz 64) $ mk_bil bil


end;
