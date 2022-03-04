theory BIL_Syntax
  imports Main Bitvector_Syntax
begin


typedecl Id
axiomatization where
unique: "\<exists>x::Id. \<forall>y. x \<noteq> y"


text \<open>The type system of BIL consists of two type families - immediate values, indexed by a bitwidth,
and storagies (aka memories), indexed with address bitwidth and values bitwidth.\<close>

datatype Type =
    Imm nat      (* immediate of size sz *)
  | Mem nat nat  (* memory with address size sz1 and element size sz2 *)


text \<open>BIL program is reperesented as a sequence of statements. Each statement performs some 
      side-effectful computation.\<close>

datatype Cast =
    Unsigned  (* 0-padding widening cast. *)
  | Signed    (* Sign-extending widening cast. *)
  | High      (* Narrowing cast. Keeps the high bits. *)
  | Low       (* Narrowing cast. Keeps the low bits. *)

datatype Endian = 
    LittleEndian (\<open>el\<close>)
  | BigEndian (\<open>be\<close>)

datatype UnOp =    
    Neg  (* Negate. (2's complement) *)
  | Not  (* Bitwise not.(1's complement) *)

primrec 
  operator_unop :: \<open>UnOp \<Rightarrow> (word \<Rightarrow> word)\<close>
where
  \<open>operator_unop Not = negation\<close> |
  \<open>operator_unop Neg = uminus\<close>

datatype LOp = 
    Eq      (* Equals. (commutative) (associative on booleans) *)
  | Neq     (* Not equals. (commutative) (associative on booleans) *)
  | Lt      (* Unsigned less than. *)
  | Le      (* Unsigned less than or equal to. *)
  | Slt     (* Signed less than. *)
  | Sle     (* Signed less than or equal to. *)

primrec
  operator_lop :: \<open>LOp \<Rightarrow> (word \<Rightarrow> word \<Rightarrow> word)\<close>
where
  \<open>operator_lop Eq = (=\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Neq = (\<noteq>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Lt = (<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Le = (\<le>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Slt = (<\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_lop Sle = (\<le>\<^sub>s\<^sub>b\<^sub>v)\<close>

datatype AOp =
    Plus    (* Integer addition. (commutative, associative) *)
  | Minus   (* Subtract second integer from first. *)
  | Times   (* Integer multiplication. (commutative, associative) *)
  | Divide  (* Unsigned integer division. *)
  | SDivide (* Signed integer division. *)
  | Mod     (* Unsigned modulus. *)
  | SMod    (* Signed modulus. *)
  | And     (* Bitwise and. (commutative, associative) *)
  | Or      (* Bitwise or. (commutative, associative) *)
  | Xor     (* Bitwise xor. (commutative, associative) *)
  | LShift  (* Left shift. *)
  | RShift  (* Right shift, zero padding. *)
  | ARShift (* Right shift, sign extend. *)

primrec
  operator_aop :: \<open>AOp \<Rightarrow> (word \<Rightarrow> word \<Rightarrow> word)\<close>
where
  \<open>operator_aop Plus = (+\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Minus = (-\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Times = (*\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Divide = (div\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SDivide = (div\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Mod = (%\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop SMod = (%\<^sub>s\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop And = (&\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Or = (|\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop Xor = (xor\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop LShift = (<<\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop RShift = (>>\<^sub>b\<^sub>v)\<close> |
  \<open>operator_aop ARShift = (>>>\<^sub>b\<^sub>v)\<close>


datatype BinOp =
    AOp AOp
  | LOp LOp

type_synonym var = \<open>(Id \<times> Type)\<close>

section \<open>Value syntax\<close>

text \<open>Values are syntactic subset of expressions. They are used to represent expressions that are 
      not reducible.

      We have three kinds of values | immediates, represented as bitvectors; unknown values and
      storages (memories in BIL parlance), represented symbolically as a list of assignments:\<close>

datatype val = 
    Immediate word
  | Unknown string Type
  | Storage val word val nat

datatype exp =
    Val val                      (* A variable *)
  | Var var
  | Load exp exp Endian nat	     (* load from memory (should be Exp not memory) *)
  | Store exp exp Endian nat exp (* store to memory *)
  | BinOp exp BinOp exp          (* binary operation *)
  | UnOp UnOp exp                (* unary operation *)
  | Cast Cast nat exp            (* casting *)
  | Let var exp exp	             (* let-binding *)
  | Ite exp exp exp              (* if-then-else expression *)
  | Extract nat nat exp          (* extract portion of word *)
  | Concat exp exp               (* concatenate two words *)

text \<open>Expressions are well formed if they recursively contain loads that target memory widths 
      greater than zero (in bytes). Well formed expressions can be evaluated ahead of time.\<close>

fun 
  wfe :: \<open>exp \<Rightarrow> bool\<close>
where
  \<open>wfe (Load e\<^sub>1 e\<^sub>2 _ sz) = (sz \<ge> 8 \<and> wfe e\<^sub>1 \<and> wfe e\<^sub>2)\<close> |
  \<open>wfe (Store e\<^sub>1 e\<^sub>2 _ sz e\<^sub>3) = (sz \<ge> 8 \<and> wfe e\<^sub>1 \<and> wfe e\<^sub>2 \<and> wfe e\<^sub>3)\<close> |  
  \<open>wfe (BinOp e\<^sub>1 _ e\<^sub>2) = (wfe e\<^sub>1 \<and> wfe e\<^sub>2)\<close> |
  \<open>wfe (UnOp _ e) = wfe e\<close> |
  \<open>wfe (Cast _ _ e) = wfe e\<close> |
  \<open>wfe (Let _ e\<^sub>1 e\<^sub>2) = (wfe e\<^sub>1 \<and> wfe e\<^sub>2)\<close> |
  \<open>wfe (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (wfe e\<^sub>1 \<and> wfe e\<^sub>2 \<and> wfe e\<^sub>3)\<close> |
  \<open>wfe (Extract _ _ e) = wfe e\<close> |
  \<open>wfe (Concat e\<^sub>1 e\<^sub>2) = (wfe e\<^sub>1 \<and> wfe e\<^sub>2)\<close> |
  \<open>wfe _ = True\<close>

(*TODO capture-avoiding? *)
primrec 
  let_substitute_val :: \<open>exp \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close> (\<open>[_\<sslash>_]_\<close>)
where
  \<open>([_\<sslash>_](Val v)) = (Val v)\<close> |
  \<open>([e\<sslash>var](Var var')) = (if var = var' then e else (Var var'))\<close> |
  \<open>([e\<sslash>var](Load e\<^sub>1 e\<^sub>2 ed sz)) = Load ([e\<sslash>var]e\<^sub>1) ([e\<sslash>var]e\<^sub>2) ed sz\<close> |
  \<open>([e\<sslash>var](Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3)) = Store ([e\<sslash>var]e\<^sub>1) ([e\<sslash>var]e\<^sub>2) ed sz ([e\<sslash>var]e\<^sub>3)\<close> |
  \<open>([e\<sslash>var](BinOp e\<^sub>1 bop e\<^sub>2)) = BinOp ([e\<sslash>var]e\<^sub>1) bop ([e\<sslash>var]e\<^sub>2)\<close> |
  \<open>([e\<sslash>var](UnOp uop e')) = UnOp uop ([e\<sslash>var]e')\<close> |
  \<open>([e\<sslash>var](Cast cast sz e')) = Cast cast sz ([e\<sslash>var]e')\<close> |
  \<open>([e\<sslash>var](Let var' e\<^sub>1 e\<^sub>2)) = Let var' ([e\<sslash>var]e\<^sub>1) ([e\<sslash>var]e\<^sub>2)\<close> |
  \<open>([e\<sslash>var](Ite e\<^sub>1 e\<^sub>2 e\<^sub>3)) = Ite ([e\<sslash>var]e\<^sub>1) ([e\<sslash>var]e\<^sub>2) ([e\<sslash>var]e\<^sub>3)\<close> |
  \<open>([e\<sslash>var](Extract sz\<^sub>1 sz\<^sub>2 e')) = Extract sz\<^sub>1 sz\<^sub>2 ([e\<sslash>var]e')\<close> |
  \<open>([e\<sslash>var](Concat e\<^sub>1 e\<^sub>2)) = Concat ([e\<sslash>var]e\<^sub>1) ([e\<sslash>var]e\<^sub>2)\<close>

datatype stmt =
    Move var exp
  | Jmp exp
  | CpuExn int
  | Special string
  | While exp bil
  | If exp bil bil
and bil = 
    Stmt stmt bil
  | Empty

abbreviation \<open>IfThen e bil \<equiv> If e bil Empty\<close> 

end