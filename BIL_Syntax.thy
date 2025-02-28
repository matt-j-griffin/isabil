theory BIL_Syntax
  imports Bitvector_Syntax 
          Bitvector_Instance (* TODO tidy theories *)
          HOL.String
          "../Typing/Typing_Var_Typed_Ok"
begin            

section \<open>Value syntax\<close>

text \<open>Values are syntactic subset of expressions. They are used to represent expressions that are 
      not reducible.

      We have three kinds of values | immediates, represented as bitvectors; unknown values and
      storages (memories in BIL parlance), represented symbolically as a list of assignments:\<close>

datatype val = 
    Immediate word
  | Unknown string Type
  | Storage val word val nat

class unknown_constructor = type_syntax + typed_ok +
  fixes unknown_constructor :: \<open>string \<Rightarrow> Type \<Rightarrow> 'a\<close> (\<open>unknown[_]: _\<close>)
  assumes unknown_inject[simp]: 
            \<open>\<And>str str' t t'. (unknown[str]: t) = (unknown[str']: t') \<longleftrightarrow> str = str' \<and> t = t'\<close>
      and type_unknownI: \<open>\<And>str t. type (unknown[str]: t) = t\<close>
      and unknown_typed_ok: \<open>\<And>\<Gamma> str t t'. (\<Gamma> \<turnstile> (unknown[str]: t) :: t') \<longleftrightarrow> t = t' \<and> t is ok \<and> 
                                \<Gamma> is ok\<close>
begin

lemma unknown_typed_okI[intro]: 
  assumes \<open>t is ok\<close> \<open>\<Gamma> is ok\<close> shows \<open>\<Gamma> \<turnstile> (unknown[str]: t) :: t\<close>
  using assms unfolding unknown_typed_ok by auto

lemma unknown_typed_diffE[elim]:
  assumes \<open>\<Gamma> \<turnstile> (unknown[str]: t') :: t\<close> 
    shows \<open>t' = t\<close> \<open>t' is ok\<close> \<open>\<Gamma> is ok\<close>
  using assms unfolding unknown_typed_ok by auto

lemmas T_UNKNOWN = unknown_typed_okI

end

class storage_constructor = size + word_constructor + typed_ok +
    fixes storage_constructor :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>_[_ \<leftarrow> _, _]\<close>) (*TODO bad syntax*)
  assumes storage_inject[simp]: \<open>\<And>mem w v sz mem' w' v' sz'. (mem[w \<leftarrow> v, sz]) = (mem'[w' \<leftarrow> v', sz']) \<longleftrightarrow>
                                        mem = mem' \<and> w = w' \<and> v = v' \<and> sz = sz'\<close>
      and type_storageI: \<open>\<And>mem num sz\<^sub>1 v sz\<^sub>2. type (mem[(num \<Colon> sz\<^sub>1) \<leftarrow> v, sz\<^sub>2]) = mem\<langle>sz\<^sub>1,sz\<^sub>2\<rangle>\<close>
      and storage_typed_ok: \<open>\<And>\<Gamma> v num sz' v' sz t. (\<Gamma> \<turnstile> (v[(num \<Colon> sz') \<leftarrow> v', sz]) :: t) \<Longrightarrow> (
              t = mem\<langle>sz', sz\<rangle>)\<close>
begin

lemma type_storageE: 
  assumes \<open>type (mem[(num \<Colon> sz\<^sub>1) \<leftarrow> v, sz\<^sub>2]) = t\<close>
      and \<open>t = mem\<langle>sz\<^sub>1,sz\<^sub>2\<rangle> \<Longrightarrow> P\<close>
    shows P
  using assms type_storageI by blast

lemma type_storage_addrI: \<open>type w = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> type (mem[w \<leftarrow> v, sz\<^sub>2]) = mem\<langle>sz\<^sub>1,sz\<^sub>2\<rangle>\<close>
  apply (cases w rule: word_exhaust, auto)
  by (rule type_storageI)

lemma type_storage_addrE: 
  assumes major: \<open>type (mem[w \<leftarrow> v, sz\<^sub>2]) = t\<close> and caveat: \<open>type w = imm\<langle>sz\<^sub>1\<rangle>\<close>
  obtains \<open>t = mem\<langle>sz\<^sub>1,sz\<^sub>2\<rangle>\<close>
  apply standard
  unfolding major[symmetric] 
  using caveat by (rule type_storage_addrI)

lemma storage_not_imm: \<open>\<not>(\<Gamma> \<turnstile> mem[w \<leftarrow> v, sz] :: imm\<langle>sz'\<rangle>)\<close>
proof (cases w rule: word_exhaust)
  case (Word a b)
  show ?thesis 
    unfolding Word apply auto apply (drule storage_typed_ok)
    by simp
qed

end

class val_syntax = word_constructor + unknown_constructor + storage_constructor +
  assumes storage_word_neq[simp]: \<open>\<And>v w v' sz num sz'. v[w \<leftarrow> v', sz] \<noteq> (num \<Colon> sz')\<close>
      and storage_unknown_neq[simp]: \<open>\<And>v w v' sz str t. v[w \<leftarrow> v', sz] \<noteq> unknown[str]: t\<close>
      and word_unknown_neq[simp]: \<open>\<And>str t num sz. (num \<Colon> sz) \<noteq> unknown[str]: t\<close>
begin

lemma unknown_simps[simp]:
  \<open>(unknown[str]: t) \<noteq> (num \<Colon> sz)\<close> \<open>(unknown[str]: t) \<noteq> true\<close> \<open>(unknown[str]: t) \<noteq> false\<close>
  \<open>(unknown[str]: t) \<noteq> (v[w \<leftarrow> v', sz])\<close>
  using word_unknown_neq[symmetric] storage_unknown_neq[symmetric] by auto

lemmas storage_simps = storage_unknown_neq storage_word_neq

lemma word_simps':
  \<open>(num \<Colon> sz) \<noteq> (v[w \<leftarrow> v', sz'])\<close>
  using storage_word_neq[symmetric] by auto

lemmas word_simps[simp] = word_simps' word_unknown_neq

lemma val_syntax_bool_simps[simp]: 
    \<open>true \<noteq> (unknown[str]: t)\<close> \<open>false \<noteq> (unknown[str]: t)\<close>
    \<open>true \<noteq> (v[w \<leftarrow> v', sz])\<close>  \<open>false \<noteq> (v[w \<leftarrow> v', sz])\<close>
  using storage_simps[symmetric] unknown_simps[symmetric] by auto

lemma val_syntax_exhaust:
  obtains 
    (Word) num sz where \<open>v = (num \<Colon> sz)\<close>
  | (Unknown) str t where \<open>v = (unknown[str]: t)\<close>
  | (Storage) mem w v' sz where \<open>v = (mem[w \<leftarrow> v', sz])\<close>
  | (NotVal) \<open>\<forall>num sz. v \<noteq> (num \<Colon> sz)\<close> \<open>\<forall>mem w v' sz. v \<noteq> (mem[w \<leftarrow> v', sz])\<close>
              \<open>\<forall>str t. v \<noteq> (unknown[str]: t)\<close>
  by blast

end

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

datatype exp = 
    Val val
  | EVar var
  | Load exp exp Endian nat	 (\<open>_[_, _]:u_\<close>)
  | Store exp exp Endian nat exp (\<open>_ with [_, _]:u_ \<leftarrow> _\<close>) (*TODO: u?*)
  | BinOp exp BinOp exp
  | UnOp UnOp exp
  | Cast Cast nat exp  (\<open>_:_[_]\<close>)
  | Let var exp exp
  | Ite exp exp exp (\<open>ite _ _ _\<close>)
  | Extract nat nat exp (\<open>extract:_:_[_]\<close>)
  | Concat exp exp (infixr \<open>\<copyright>\<close> 70)

class exp = val_syntax + bil_ops + var_typed_ok +
  assumes var_not_word_neq[simp]: \<open>\<And>id t num sz'. (id :\<^sub>t t) \<noteq> (num \<Colon> sz')\<close>
      and var_not_unknown_neq[simp]: \<open>\<And>id t str t'. (id :\<^sub>t t) \<noteq> unknown[str]: t'\<close>
      and var_not_storage_neq[simp]: \<open>\<And>id t v w v' sz. (id :\<^sub>t t) \<noteq> (v[w \<leftarrow> v', sz])\<close>
      and exp_simps[simp]:
        \<open>\<And>id t e\<^sub>1 e\<^sub>2. id :\<^sub>t t \<noteq> e\<^sub>1 + e\<^sub>2\<close>

      and le_word_simp[simp]: \<open>\<And>e\<^sub>1 e\<^sub>2 num sz. e\<^sub>1 le e\<^sub>2 \<noteq> (num \<Colon> sz)\<close>

begin

lemma plus_not_var[simp]: \<open>e\<^sub>1 + e\<^sub>2 \<noteq> id' :\<^sub>t t\<close>
  using exp_simps(1) by metis

lemma le_simps[simp]: 
    \<open>e\<^sub>1 le e\<^sub>2 \<noteq> true\<close> \<open>e\<^sub>1 le e\<^sub>2 \<noteq> false\<close>
    \<open>e\<^sub>1 le e\<^sub>2 \<noteq> (num\<^sub>1 \<Colon> sz) =\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
    \<open>e\<^sub>1 le e\<^sub>2 \<noteq> (num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
    \<open>e\<^sub>1 le e\<^sub>2 \<noteq> (num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)\<close>
  unfolding bv_lt.simps bv_lor.simps bv_eq_def 
  using le_word_simp(* apply simp_all*)
  using le_word_simp by simp_all

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


primrec 
  capture_avoiding_sub :: \<open>val \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close> (\<open>[_\<sslash>_]_\<close> [501,500,502] 508)
where
  Val: \<open>[_\<sslash>_](Val v) = (Val v)\<close> |
  EVar: \<open>[v\<sslash>var](EVar var') = (if var = var' then (Val v) else (EVar var'))\<close> |
  Load: \<open>[v\<sslash>var](Load e\<^sub>1 e\<^sub>2 ed sz) = Load ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ed sz\<close> |
  Store: \<open>[v\<sslash>var](Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) = Store ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ed sz ([v\<sslash>var]e\<^sub>3)\<close> |
  BinOp: \<open>[v\<sslash>var](BinOp e\<^sub>1 bop e\<^sub>2) = BinOp ([v\<sslash>var]e\<^sub>1) bop ([v\<sslash>var]e\<^sub>2)\<close> |
  UnOp: \<open>[v\<sslash>var](UnOp uop e) = UnOp uop ([v\<sslash>var]e)\<close> |
  Cast: \<open>[v\<sslash>var](Cast cast sz e) = Cast cast sz ([v\<sslash>var]e)\<close> |
(*
  Let: \<open>[v\<sslash>var](Let var' e\<^sub>1 e\<^sub>2) = (if (var = var') then (Let var' ([v\<sslash>var]e\<^sub>1) (e\<^sub>2)) else (Let var' ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2)))\<close> |
*)
  Let: \<open>[v\<sslash>var](Let var' e\<^sub>1 e\<^sub>2) = (Let var' ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2))\<close> |

  Ite: \<open>[v\<sslash>var](Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = Ite ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ([v\<sslash>var]e\<^sub>3)\<close> |
  Extract: \<open>[v\<sslash>var](Extract sz\<^sub>1 sz\<^sub>2 e') = Extract sz\<^sub>1 sz\<^sub>2 ([v\<sslash>var]e')\<close> |
  Concat: \<open>[v\<sslash>var](e\<^sub>1 \<copyright> e\<^sub>2) = ([v\<sslash>var]e\<^sub>1) \<copyright> ([v\<sslash>var]e\<^sub>2)\<close>

(*
function
  capture_avoiding_sub :: \<open>val \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp\<close> (\<open>[_\<sslash>_]_\<close> [501,500,502] 508)
where
  Val: \<open>[_\<sslash>_](Val v) = (Val v)\<close> |
  EVar: \<open>[v\<sslash>var](EVar var') = (if var = var' then (Val v) else (EVar var'))\<close> |
  Load: \<open>[v\<sslash>var](Load e\<^sub>1 e\<^sub>2 ed sz) = Load ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ed sz\<close> |
  Store: \<open>[v\<sslash>var](Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) = Store ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ed sz ([v\<sslash>var]e\<^sub>3)\<close> |
  BinOp: \<open>[v\<sslash>var](BinOp e\<^sub>1 bop e\<^sub>2) = BinOp ([v\<sslash>var]e\<^sub>1) bop ([v\<sslash>var]e\<^sub>2)\<close> |
  UnOp: \<open>[v\<sslash>var](UnOp uop e) = UnOp uop ([v\<sslash>var]e)\<close> |
  Cast: \<open>[v\<sslash>var](Cast cast sz e) = Cast cast sz ([v\<sslash>var]e)\<close> |
  Let: \<open>[v\<sslash>var](Let var e\<^sub>1 e\<^sub>2) = ([v\<sslash>var]e\<^sub>2)\<close> |
  LetNeq: \<open>\<lbrakk>var \<noteq> var'\<rbrakk> \<Longrightarrow> [v\<sslash>var](Let var' e\<^sub>1 e\<^sub>2) = (Let var' ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2))\<close> |
  Ite: \<open>[v\<sslash>var](Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = Ite ([v\<sslash>var]e\<^sub>1) ([v\<sslash>var]e\<^sub>2) ([v\<sslash>var]e\<^sub>3)\<close> |
  Extract: \<open>[v\<sslash>var](Extract sz\<^sub>1 sz\<^sub>2 e') = Extract sz\<^sub>1 sz\<^sub>2 ([v\<sslash>var]e')\<close> |
  Concat: \<open>[v\<sslash>var](e\<^sub>1 \<copyright> e\<^sub>2) = ([v\<sslash>var]e\<^sub>1) \<copyright> ([v\<sslash>var]e\<^sub>2)\<close>
  sketch -
proof -
  fix P :: bool and x :: "val \<times> BIL_Syntax.var \<times> exp"
  assume F: "\<And>uu uv v. x = (uu, uv, Val v) \<Longrightarrow> P"
 "\<And>v var var'. x = (v, var, EVar var') \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 e\<^sub>2 ed sz. x = (v, var, e\<^sub>1[e\<^sub>2, ed]:usz) \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3. x = (v, var, e\<^sub>1 with [e\<^sub>2, ed]:usz \<leftarrow> e\<^sub>3) \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 bop e\<^sub>2. x = (v, var, BinOp e\<^sub>1 bop e\<^sub>2) \<Longrightarrow> P"
 "\<And>v var uop e. x = (v, var, UnOp uop e) \<Longrightarrow> P"
 "\<And>v var cast sz e. x = (v, var, cast:sz[e]) \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 e\<^sub>2. x = (v, var, exp.Let var e\<^sub>1 e\<^sub>2) \<Longrightarrow> P"
 "\<And>var var' v e\<^sub>1 e\<^sub>2. \<lbrakk>var \<noteq> var'; x = (v, var, exp.Let var' e\<^sub>1 e\<^sub>2)\<rbrakk> \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 e\<^sub>2 e\<^sub>3. x = (v, var, ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Longrightarrow> P"
 "\<And>v var sz\<^sub>1 sz\<^sub>2 e'. x = (v, var, extract:sz\<^sub>1:sz\<^sub>2[e']) \<Longrightarrow> P"
 "\<And>v var e\<^sub>1 e\<^sub>2. x = (v, var, e\<^sub>1 \<copyright> e\<^sub>2) \<Longrightarrow> P"
  show P
  proof (cases x)
    case tuple: (fields a var2 c)
    show ?thesis 
    proof (cases c)
      fix var :: BIL_Syntax.var
        and x82 :: exp
        and x83 :: exp
      assume c: "c = exp.Let var x82 x83"
      show P
        apply (cases "var = var2")
        using F[unfolded tuple c] apply auto
        by presburger
    qed (auto simp add: F[unfolded tuple])
  qed
qed auto
termination by lexicographic_order*)

lemma capture_avoiding_sub_size_eq[simp]: \<open>size_class.size ([v\<sslash>var]e) = size_class.size e\<close>
  by (induct e, auto)
  
lemma let_neq_capture_avoid_v[simp]: \<open>exp.Let var (Val v) e \<noteq> [v\<sslash>var]e\<close>
  apply (induct e, auto)
  using capture_avoiding_sub_size_eq
  by (metis add.right_neutral add_Suc_right add_cancel_right_left exp.size(12) exp.size(19) n_not_Suc_n)

lemma let_neq_capture_avoid_e[simp]: \<open>exp.Let var e\<^sub>1 e\<^sub>2 \<noteq> [v\<sslash>var]e\<^sub>2\<close>
  apply (induct e\<^sub>2, auto)
  using capture_avoiding_sub_size_eq 
  by (metis Suc_n_not_le_n add_le_same_cancel1 exp.size(19) le_add2)

lemma capture_avoiding_evar_eq[simp]: \<open>[v\<sslash>var]EVar var = Val v\<close>
  by simp



lemma capture_capture_var_eq[simp]: \<open>[val\<^sub>1\<sslash>var][val\<^sub>2\<sslash>var]e = [val\<^sub>2\<sslash>var]e\<close>
  by (induct e, auto)

lemma capture_neq_swap: 
  assumes \<open>var\<^sub>1 \<noteq> var\<^sub>2\<close>
    shows \<open>[val\<^sub>1\<sslash>var\<^sub>1][val\<^sub>2\<sslash>var\<^sub>2]e = [val\<^sub>2\<sslash>var\<^sub>2][val\<^sub>1\<sslash>var\<^sub>1]e\<close>
  using assms by (induct e, auto)


primrec 
  isnt_var :: \<open>var \<Rightarrow> exp \<Rightarrow> bool\<close>
where 
  Val: \<open>isnt_var _ (Val _) = True\<close> |
  EVar: \<open>isnt_var var1 (EVar var2) = (var1 \<noteq> var2)\<close> |
  Load: \<open>isnt_var var (Load e\<^sub>1 e\<^sub>2 _ _) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2)\<close> |
  Store: \<open>isnt_var var (Store e\<^sub>1 e\<^sub>2 _ _ e\<^sub>3) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2 \<and> isnt_var var e\<^sub>3)\<close> |
  BinOp: \<open>isnt_var var (BinOp e\<^sub>1 _ e\<^sub>2) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2)\<close> |
  UnOp: \<open>isnt_var var (UnOp _ e) = (isnt_var var e)\<close> |
  Cast: \<open>isnt_var var (Cast _ _ e) = (isnt_var var e)\<close> |
  Let: \<open>isnt_var var (Let _ e\<^sub>1 e\<^sub>2) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2)\<close> |
  Ite: \<open>isnt_var var (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2 \<and> isnt_var var e\<^sub>3)\<close> |
  Extract: \<open>isnt_var var (Extract _ _ e) = (isnt_var var e)\<close> |
  Concat: \<open>isnt_var var (Concat e\<^sub>1 e\<^sub>2) = (isnt_var var e\<^sub>1 \<and> isnt_var var e\<^sub>2)\<close>

lemma is_var[simp]: \<open>\<not>isnt_var var (EVar var)\<close>
  by simp

datatype stmt =
    Move var exp (infixl \<open>:=\<close> 55)
  | Jmp exp (\<open>jmp _\<close>)
  | CpuExn int (\<open>cpuexn _\<close>)
  | Special string (\<open>special[_]\<close>)
  | While exp \<open>stmt list\<close> (\<open>while(_) _\<close>) (* TODO *)
  | If exp \<open>stmt list\<close> \<open>stmt list\<close> (\<open>if(_) _ else _\<close>)

type_synonym bil = \<open>stmt list\<close>

abbreviation \<open>IfThen e bil \<equiv> If e bil []\<close> 

end