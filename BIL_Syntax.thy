theory BIL_Syntax
  imports Bitvector_Syntax 
          HOL.String
begin            

text \<open>The type system of BIL consists of two type families - immediate values, indexed by a bitwidth,
and storagies (aka memories), indexed with address bitwidth and values bitwidth.\<close>

datatype Type =
    Imm nat (\<open>imm\<langle>_\<rangle>\<close>)
  | Mem nat nat (\<open>mem\<langle>_, _\<rangle>\<close>)

text \<open>BIL program is represented as a sequence of statements. Each statement performs some 
      side-effectful computation.\<close>

datatype Cast =
    Unsigned (\<open>pad\<close>)  (* 0-padding widening cast. *)
  | Signed   (\<open>extend\<close>)  (* Sign-extending widening cast. *)
  | High     (\<open>high\<close>)  (* Narrowing cast. Keeps the high bits. *)
  | Low      (\<open>low\<close>)  (* Narrowing cast. Keeps the low bits. *)

datatype Endian = 
    LittleEndian (\<open>el\<close>)
  | BigEndian (\<open>be\<close>)

datatype UnOp =    
    Neg  (* Negate. (2's complement) *)
  | Not  (* Bitwise not.(1's complement) *)

datatype LOp = 
    Eq      (* Equals. (commutative) (associative on booleans) *)
  | Neq     (* Not equals. (commutative) (associative on booleans) *)
  | Lt      (* Unsigned less than. *)
  | Le      (* Unsigned less than or equal to. *)
  | Slt     (* Signed less than. *)
  | Sle     (* Signed less than or equal to. *)

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


datatype BinOp =
    AOp AOp
  | LOp LOp

no_notation Set.member (\<open>(_/ : _)\<close> [51, 51] 50)

class var_syntax =
    fixes var_constructor :: \<open>string \<Rightarrow> Type \<Rightarrow> 'a\<close> (\<open>(_/ :\<^sub>t _)\<close> [151, 101] 100)
  assumes var_eq[simp]: \<open>\<And>id t id' t'. (id :\<^sub>t t) = (id' :\<^sub>t t') \<longleftrightarrow> id = id' \<and> t = t'\<close>
begin

lemma var_syntax_exhaust:
  obtains 
    (Var) id t where \<open>var = (id :\<^sub>t t)\<close>
  | (NotVar) \<open>\<forall>id t. var \<noteq> (id :\<^sub>t t)\<close>
  by auto

end


class var = var_syntax +
  assumes var_exhaust: \<open>\<And>P var. (\<And>id t. var = (id :\<^sub>t t) \<Longrightarrow> P) \<Longrightarrow> P\<close>


datatype var = Var (name: string) (var_type: Type) (* TODO remove var_type in favour of type var. Ideally prod type though *)

instantiation var :: var
begin

definition 
  var_constructor_var :: \<open>string \<Rightarrow> Type \<Rightarrow> BIL_Syntax.var\<close>
where
  \<open>(id' :\<^sub>t t) \<equiv> Var id' t\<close>

instance
  apply standard
  unfolding var_constructor_var_def 
  subgoal by simp
  subgoal by (rule var.exhaust)
  .

end


section \<open>Value syntax\<close>

text \<open>Values are syntactic subset of expressions. They are used to represent expressions that are 
      not reducible.

      We have three kinds of values | immediates, represented as bitvectors; unknown values and
      storages (memories in BIL parlance), represented symbolically as a list of assignments:\<close>

datatype val = 
    Immediate word
  | Unknown string Type
  | Storage val word val nat

class unknown_constructor = 
    fixes unknown_constructor :: \<open>string \<Rightarrow> Type \<Rightarrow> 'a\<close> (\<open>unknown[_]: _\<close>)
  assumes unknown_eq[simp]: 
            \<open>\<And>str str' t t'. (unknown[str]: t) = (unknown[str']: t') \<longleftrightarrow> str = str' \<and> t = t'\<close>

class storage_constructor = size + word_constructor +
    fixes storage_constructor :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>_[_ \<leftarrow> _, _]\<close>)
  assumes storage_eq[simp]: \<open>\<And>mem w v sz mem' w' v' sz'. (mem[w \<leftarrow> v, sz]) = (mem'[w' \<leftarrow> v', sz']) \<longleftrightarrow>
                                        mem = mem' \<and> w = w' \<and> v = v' \<and> sz = sz'\<close>

class val_syntax = word_constructor + unknown_constructor + storage_constructor +
  assumes storage_word_neq[simp]: \<open>\<And>v w v' sz num sz'. v[w \<leftarrow> v', sz] \<noteq> (num \<Colon> sz')\<close>
      and storage_unknown_neq[simp]: \<open>\<And>v w v' sz str t. v[w \<leftarrow> v', sz] \<noteq> unknown[str]: t\<close>
      and word_unknown_neq[simp]: \<open>\<And>str t num sz. (num \<Colon> sz) \<noteq> unknown[str]: t\<close>
      and unknown_not_true[simp]: \<open>\<And>str t. (unknown[str]: t) \<noteq> true\<close>
      and unknown_not_false[simp]: \<open>\<And>str t. (unknown[str]: t) \<noteq> false\<close>
      and storage_not_true[simp]: \<open>\<And>v w v' sz. (v[w \<leftarrow> v', sz]) \<noteq> true\<close>
      and storage_not_false[simp]: \<open>\<And>v w v' sz. (v[w \<leftarrow> v', sz]) \<noteq> false\<close>
begin

lemma word_storage_neq[simp]: \<open>(num \<Colon> sz') \<noteq> (v[w \<leftarrow> v', sz])\<close>
  by (metis storage_word_neq)

lemma unknown_storage_neq[simp]: \<open>(unknown[str]: t) \<noteq> (v[w \<leftarrow> v', sz])\<close>
  by (metis storage_unknown_neq)

lemma unknown_word_neq[simp]: \<open>(unknown[str]: t) \<noteq> (num \<Colon> sz)\<close>
  by (metis word_unknown_neq)


lemma val_syntax_induct: (* TODO get rid? *)
  assumes \<open>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q (num \<Colon> sz)\<close>
      and \<open>\<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q (unknown[str]: t)\<close>
      and \<open>\<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q (mem[w \<leftarrow> v', sz])\<close>
      and \<open>\<lbrakk>\<forall>num sz. v \<noteq> (num \<Colon> sz); \<forall>mem w v' sz. v \<noteq> (mem[w \<leftarrow> v', sz]); 
              \<forall>str t. v \<noteq> (unknown[str]: t)\<rbrakk> \<Longrightarrow> Q v\<close>
    shows \<open>Q v\<close>
  using assms by blast

lemma val_syntax_exhaust:
  obtains 
    (Word) num sz where \<open>v = (num \<Colon> sz)\<close>
  | (Unknown) str t where \<open>v = (unknown[str]: t)\<close>
  | (Storage) mem w v' sz where \<open>v = (mem[w \<leftarrow> v', sz])\<close>
  | (NotVal) \<open>\<forall>num sz. v \<noteq> (num \<Colon> sz)\<close> \<open>\<forall>mem w v' sz. v \<noteq> (mem[w \<leftarrow> v', sz])\<close>
              \<open>\<forall>str t. v \<noteq> (unknown[str]: t)\<close>
  by blast

end

class val = val_syntax +
  assumes val_induct: \<open>\<And>Q v. \<lbrakk>\<And>num sz. Q (num \<Colon> sz); \<And>str t. Q (unknown[str]: t); 
                        \<And>mem w v' sz. Q (mem[w \<leftarrow> v', sz])\<rbrakk> \<Longrightarrow> Q v\<close>
      and val_exhaust: \<open>\<And>Q v. \<lbrakk>\<And>num sz. v = (num \<Colon> sz) \<Longrightarrow> Q; \<And>str t. v = (unknown[str]: t) \<Longrightarrow> Q; 
                        \<And>mem w v' sz. v = (mem[w \<leftarrow> v', sz]) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>

no_notation List.append  (infixr \<open>@\<close> 65)

class append =
  fixes append :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>@\<close> 65)

instantiation list :: (type) append
begin

fun
  append_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> 
where
  \<open>append_list xs ys = List.append xs ys\<close>

instance ..

end

class not_syntax = 
  fixes not :: \<open>'a \<Rightarrow> 'a\<close> (\<open>~ _\<close> [40] 40)

instantiation bool :: not_syntax
begin

definition
  not_bool :: \<open>bool \<Rightarrow> bool\<close>
where
  \<open>not_bool = HOL.Not\<close>

instance ..

end

datatype exp =
    Val val
  | Var var
  | Load exp exp Endian nat	 (\<open>_[_, _]:u_\<close>)
  | Store exp exp Endian nat exp (\<open>_ with [_, _]:u_ \<leftarrow> _\<close>)
  | BinOp exp BinOp exp
  | UnOp UnOp exp
  | Cast Cast nat exp  (\<open>_:_[_]\<close>)
  | Let var exp exp
  | Ite exp exp exp (\<open>ite _ _ _\<close>)
  | Extract nat nat exp (\<open>extract:_:_[_]\<close>)
  | Concat exp exp

instantiation exp :: append
begin          

definition 
  append_exp :: \<open>exp \<Rightarrow> exp \<Rightarrow> exp\<close> 
where
  \<open>append_exp \<equiv> Concat\<close>

instance ..

end

instantiation exp :: not_syntax
begin          

fun
  not_exp :: \<open>exp \<Rightarrow> exp\<close>
where
  \<open>not_exp exp = (UnOp Not exp)\<close>

instance ..

end

lemma append_inject[simp]:
  fixes e\<^sub>1 :: exp
  shows \<open>e\<^sub>1 @ e\<^sub>2 = e\<^sub>1' @ e\<^sub>2' \<longleftrightarrow> (e\<^sub>1 = e\<^sub>1' \<and> e\<^sub>2 = e\<^sub>2')\<close>
  unfolding append_exp_def by auto





class exp = val_syntax + bil_ops + var_syntax + append + not_syntax +
  assumes var_not_word_neq[simp]: \<open>\<And>id t num sz'. (id :\<^sub>t t) \<noteq> (num \<Colon> sz')\<close>
      and var_not_unknown_neq[simp]: \<open>\<And>id t str t'. (id :\<^sub>t t) \<noteq> unknown[str]: t'\<close>
      and var_not_storage_neq[simp]: \<open>\<And>id t v w v' sz. (id :\<^sub>t t) \<noteq> (v[w \<leftarrow> v', sz])\<close>
      and var_not_true[simp]: \<open>\<And>id t. (id :\<^sub>t t) \<noteq> true\<close>
      and var_not_false[simp]: \<open>\<And>id t. (id :\<^sub>t t) \<noteq> false\<close>
      and var_not_concat[simp]: \<open>\<And>id t e\<^sub>1 e\<^sub>2. (id :\<^sub>t t) \<noteq> e\<^sub>1 @ e\<^sub>2\<close>
      and concat_not_word_neq[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 num sz'. e\<^sub>1 @ e\<^sub>2 \<noteq> (num \<Colon> sz')\<close>
      and concat_not_unknown_neq[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 str t'. e\<^sub>1 @ e\<^sub>2 \<noteq> unknown[str]: t'\<close>
      and concat_not_storage_neq[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 v w v' sz. e\<^sub>1 @ e\<^sub>2 \<noteq> (v[w \<leftarrow> v', sz])\<close>
      and concat_not_true[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2. e\<^sub>1 @ e\<^sub>2 \<noteq> true\<close>
      and concat_not_false[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2. e\<^sub>1 @ e\<^sub>2 \<noteq> false\<close>
begin

lemma exp_syntax_exhaust:
  obtains 
    (Word) num sz where \<open>e = (num \<Colon> sz)\<close>
  | (Unknown) str t where \<open>e = (unknown[str]: t)\<close>
  | (Storage) mem w v' sz where \<open>e = (mem[w \<leftarrow> v', sz])\<close>
  | (Var) id t where \<open>e = (id :\<^sub>t t)\<close>
  | (NotExp) \<open>\<forall>num sz. e \<noteq> (num \<Colon> sz)\<close> \<open>\<forall>mem w v' sz. e \<noteq> (mem[w \<leftarrow> v', sz])\<close> 
    \<open>\<forall>str t. e \<noteq> unknown[str]: t\<close> \<open>\<forall>id t. e \<noteq> (id :\<^sub>t t)\<close>
  apply (rule val_syntax_exhaust[of e])
  apply blast
  apply blast
  apply blast
  apply (rule var_syntax_exhaust[of e])
  apply blast
  apply blast
  done

end

(*
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
  fixes let_substitute :: \<open>word \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close> (\<open>[_\<sslash>_]_\<close>)

instantiation exp and val :: capture_avoiding_sub
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
*)
datatype stmt =
    Move var exp
  | Jmp exp (\<open>jmp _\<close>)
  | CpuExn int (\<open>cpuexn _\<close>)
  | Special string (\<open>special[_]\<close>)
  | While exp bil (\<open>while(_) _\<close>)
  | If exp bil bil (\<open>if(_) _ else _\<close>)
and bil = 
    Stmt stmt bil
  | Empty



class move_syntax =
    fixes move_syntax :: \<open>var \<Rightarrow> exp \<Rightarrow> 'a\<close> (infixl \<open>:=\<close> 55)
  assumes move_eq[simp]: \<open>\<And>a b c d. (a := b) = (c := d) \<longleftrightarrow> a = c \<and> b = d\<close>

instantiation stmt :: move_syntax
begin

fun 
  move_syntax_stmt :: \<open>var \<Rightarrow> exp \<Rightarrow> stmt\<close>
where
  \<open>move_syntax_stmt var exp = Move var exp\<close>

instance by (standard, simp)

end

abbreviation \<open>IfThen e bil \<equiv> If e bil Empty\<close> 

end