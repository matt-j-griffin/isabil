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
  | Unknown string Type (\<open>unknown[_]: _\<close>)
  | Storage val word val nat (\<open>_[_ \<leftarrow> _, _]\<close>)


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

instantiation exp :: minus
begin

fun 
  minus_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>minus_exp e1 e2 = (BinOp e1 (AOp Minus) e2)\<close>


instance
  by standard
end

lemma "(e1::exp) - e2 = (BinOp e1 (AOp Minus) e2)"
  by simp


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

class capture_avoiding_sub =
  fixes let_substitute :: \<open>'a \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close> (\<open>[_\<sslash>_]_\<close>)

instantiation exp :: capture_avoiding_sub
begin

primrec 
  let_substitute_exp :: \<open>exp \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>let_substitute_exp _ _ (Val v) = (Val v)\<close> |
  \<open>let_substitute_exp e var (Var var') = (if var = var' then e else (Var var'))\<close> |
  \<open>let_substitute_exp e var (Load e\<^sub>1 e\<^sub>2 ed sz) = Load (let_substitute_exp e var e\<^sub>1) (let_substitute_exp e var e\<^sub>2) ed sz\<close> |
  \<open>let_substitute_exp e var (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) = Store (let_substitute_exp e var e\<^sub>1) (let_substitute_exp e var e\<^sub>2) ed sz (let_substitute_exp e var e\<^sub>3)\<close> |
  \<open>let_substitute_exp e var (BinOp e\<^sub>1 bop e\<^sub>2) = BinOp (let_substitute_exp e var e\<^sub>1) bop (let_substitute_exp e var e\<^sub>2)\<close> |
  \<open>let_substitute_exp e var (UnOp uop e') = UnOp uop (let_substitute_exp e var e')\<close> |
  \<open>let_substitute_exp e var (Cast cast sz e') = Cast cast sz (let_substitute_exp e var e')\<close> |
  \<open>let_substitute_exp e var (Let var' e\<^sub>1 e\<^sub>2) = Let var' (let_substitute_exp e var e\<^sub>1) (let_substitute_exp e var e\<^sub>2)\<close> |
  \<open>let_substitute_exp e var (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = Ite (let_substitute_exp e var e\<^sub>1) (let_substitute_exp e var e\<^sub>2) (let_substitute_exp e var e\<^sub>3)\<close> |
  \<open>let_substitute_exp e var (Extract sz\<^sub>1 sz\<^sub>2 e') = Extract sz\<^sub>1 sz\<^sub>2 (let_substitute_exp e var e')\<close> |
  \<open>let_substitute_exp e var (Concat e\<^sub>1 e\<^sub>2) = Concat (let_substitute_exp e var e\<^sub>1) (let_substitute_exp e var e\<^sub>2)\<close>

instance ..
end 

instantiation val :: capture_avoiding_sub
begin

primrec 
  let_substitute_val :: \<open>val \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>let_substitute_val _ _ (Val v) = (Val v)\<close> |
  \<open>let_substitute_val v var (Var var') = (if var = var' then (Val v) else (Var var'))\<close> |
  \<open>let_substitute_val v var (Load e\<^sub>1 e\<^sub>2 ed sz) = Load (let_substitute_val v var e\<^sub>1) (let_substitute_val v var e\<^sub>2) ed sz\<close> |
  \<open>let_substitute_val v var (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) = Store (let_substitute_val v var e\<^sub>1) (let_substitute_val v var e\<^sub>2) ed sz (let_substitute_val v var e\<^sub>3)\<close> |
  \<open>let_substitute_val v var (BinOp e\<^sub>1 bop e\<^sub>2) = BinOp (let_substitute_val v var e\<^sub>1) bop (let_substitute_val v var e\<^sub>2)\<close> |
  \<open>let_substitute_val v var (UnOp uop e') = UnOp uop (let_substitute_val v var e')\<close> |
  \<open>let_substitute_val v var (Cast cast sz e') = Cast cast sz (let_substitute_val v var e')\<close> |
  \<open>let_substitute_val v var (Let var' e\<^sub>1 e\<^sub>2) = Let var' (let_substitute_val v var e\<^sub>1) (let_substitute_val v var e\<^sub>2)\<close> |
  \<open>let_substitute_val v var (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = Ite (let_substitute_val v var e\<^sub>1) (let_substitute_val v var e\<^sub>2) (let_substitute_val v var e\<^sub>3)\<close> |
  \<open>let_substitute_val v var (Extract sz\<^sub>1 sz\<^sub>2 e') = Extract sz\<^sub>1 sz\<^sub>2 (let_substitute_val v var e')\<close> |
  \<open>let_substitute_val v var (Concat e\<^sub>1 e\<^sub>2) = Concat (let_substitute_val v var e\<^sub>1) (let_substitute_val v var e\<^sub>2)\<close>

instance ..
end 

lemma let_substitue_val_exp_val_eq:
  \<open>[v\<sslash>var]e = [(Val v)\<sslash>var]e\<close>
  by (induct e, auto)
  
lemma let_substitute_val_size_eq: 
    fixes v :: val
    shows \<open>size_class.size e = size_class.size ([v\<sslash>var]e)\<close>
  by (induct e, auto)

datatype stmt =
    Move var exp (\<open>_ := _\<close>)
  | Jmp exp (\<open>jmp _\<close>)
  | CpuExn int (\<open>cpuexn _\<close>)
  | Special string (\<open>special[_]\<close>)
  | While exp bil
  | If exp bil bil
and bil = 
    Stmt stmt bil
  | Empty

abbreviation \<open>IfThen e bil \<equiv> If e bil Empty\<close> 

end