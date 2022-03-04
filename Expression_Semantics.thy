theory Expression_Semantics
  imports Instruction_Syntax
begin

fun 
  type :: \<open>val \<Rightarrow> Type\<close>
where
  \<open>type (Storage v w v' sz) = Mem (bits w) sz\<close> | 
  \<open>type (Immediate w) = Imm (bits w)\<close> | 
  \<open>type (Unknown str t) = t\<close>

fun 
  succ :: \<open>word \<Rightarrow> word\<close>
where
  \<open>succ w\<^sub>1 = w\<^sub>1 +\<^sub>b\<^sub>v (1 \<Colon> bits w\<^sub>1)\<close>

lemma SUCC: \<open>succ (num \<Colon> sz) = (num \<Colon> sz) +\<^sub>b\<^sub>v (1 \<Colon> sz)\<close>
  by simp

class expression =
    fixes step :: \<open>variables \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>\<turnstile>\<close> 65)
      and step_pred :: \<open>variables \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto> _\<close>)

instantiation exp :: expression
begin
(* TODO REMOVE dummy cases *)
fun 
  step_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp\<close>
where
  \<open>step_exp \<Delta> (Val val) = (Val val)\<close> |
  \<open>step_exp \<Delta> (Var var) = (let (name, t) = var in if var \<in> dom \<Delta> then (Val (the (\<Delta> var))) else (Val (Unknown [] t)))\<close> |
  \<open>step_exp \<Delta> (Load e\<^sub>1 e\<^sub>2 ed sz) = (
    case e\<^sub>2 of Val v\<^sub>2 \<Rightarrow> (
      case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
        case v\<^sub>1 of Storage v w\<^sub>1 v' sz' \<Rightarrow> (
          case v\<^sub>2 of Immediate w\<^sub>2 \<Rightarrow> (
            if sz > sz' then 
              case ed of be \<Rightarrow> (Concat (Load (Val v\<^sub>1) (Val (Immediate w\<^sub>2)) be sz') ((Load (Val v\<^sub>1) (Val (Immediate (succ w\<^sub>2))) be (sz - sz'))))
                | el \<Rightarrow> (Concat (Load (Val v\<^sub>1) (Val (Immediate (succ w\<^sub>2))) el (sz - sz')) ((Load (Val v\<^sub>1) (Val (Immediate w\<^sub>2)) el sz')))
            else (
              if w\<^sub>2 = w\<^sub>1 then (Val v')
              else (Load (Val v) (Val (Immediate w\<^sub>2)) ed sz)
            )
          ) | Unknown str t \<Rightarrow> Val (Unknown str (Imm sz))
        ) | Unknown str t \<Rightarrow> Val (Unknown str (Imm sz))
      ) | _ \<Rightarrow> (Load (step_exp \<Delta> e\<^sub>1) (Val v\<^sub>2) ed sz)
    ) | _ \<Rightarrow> (Load e\<^sub>1 (step_exp \<Delta> e\<^sub>2) ed sz)
  )\<close> |
  \<open>step_exp \<Delta> (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) = (
    case e\<^sub>3 of Val v\<^sub>3 \<Rightarrow> (
      case e\<^sub>2 of Val v\<^sub>2 \<Rightarrow> (
        case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
          let t = type v\<^sub>1 in 
          case v\<^sub>2 of Immediate w \<Rightarrow> (
            case t of Mem _ sz' \<Rightarrow> (
              if sz > sz' then 
                case ed of be \<Rightarrow> (Store (Store (Val v\<^sub>1) (Val (Immediate w)) be sz' (Cast High sz' (Val v\<^sub>3))) (Val (Immediate (succ w))) be (sz - sz') (Cast Low (sz - sz') (Val v\<^sub>3)))
                  | el \<Rightarrow> (Store (Store (Val v\<^sub>1) (Val (Immediate w)) el sz' (Cast Low sz' (Val v\<^sub>3))) (Val (Immediate (succ w))) el (sz - sz') (Cast High (sz - sz') (Val v\<^sub>3)))
              else Val (Storage v\<^sub>1 w v\<^sub>3 sz')
            )
          ) | Unknown str t' \<Rightarrow> Val (Unknown str t)
        ) | _ \<Rightarrow> (Store (step_exp \<Delta> e\<^sub>1) (Val v\<^sub>2) ed sz (Val v\<^sub>3))
      ) | _ \<Rightarrow> (Store e\<^sub>1 (step_exp \<Delta> e\<^sub>2) ed sz (Val v\<^sub>3))
    ) | _ \<Rightarrow> (Store e\<^sub>1 e\<^sub>2 ed sz (step_exp \<Delta> e\<^sub>3))
  )\<close> |
  \<open>step_exp \<Delta> (BinOp e\<^sub>1 binop e\<^sub>2) = (
    case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
      case e\<^sub>2 of Val v\<^sub>2 \<Rightarrow> (
        case binop of
          AOp aop \<Rightarrow> (case v\<^sub>1 of
            Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
              Immediate w\<^sub>2 \<Rightarrow> Val (Immediate (operator_aop aop w\<^sub>1 w\<^sub>2)) |
              Unknown str t \<Rightarrow> Val (Unknown str t)) |
            Unknown str t \<Rightarrow> Val (Unknown str t))
          |
          LOp lop \<Rightarrow> (case v\<^sub>1 of
            Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
              Immediate w\<^sub>2 \<Rightarrow> Val (Immediate (operator_lop lop w\<^sub>1 w\<^sub>2)) |
              Unknown str t \<Rightarrow> Val (Unknown str (Imm 1))) |
            Unknown str t \<Rightarrow> Val (Unknown str (Imm 1)))
      ) | _ \<Rightarrow> (BinOp (Val v\<^sub>1) binop (step_exp \<Delta> e\<^sub>2))
    ) | _ \<Rightarrow> (BinOp (step_exp \<Delta> e\<^sub>1) binop e\<^sub>2)
  )\<close> |
  \<open>step_exp \<Delta> (UnOp unop e) = (
    case e of Val v \<Rightarrow> (
      case v of Immediate w \<Rightarrow> Val (Immediate ((operator_unop unop) w))
        | Unknown str t \<Rightarrow> Val (Unknown str t)
    ) | _ \<Rightarrow> UnOp unop (step_exp \<Delta> e)
  )\<close> |
  \<open>step_exp \<Delta> (Cast cast sz e) = (
    case e of Val v \<Rightarrow> (
      case v of
        Immediate w \<Rightarrow> (case cast of
          Low \<Rightarrow> Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)) |
          High \<Rightarrow> Val (Immediate (ext w \<sim> hi : (bits w - 1) \<sim> lo : (bits w - sz))) |
          Signed \<Rightarrow> Val (Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0)) |
          Unsigned \<Rightarrow> Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0))) |
        Unknown str t \<Rightarrow> Val (Unknown str (Imm sz))
    ) | _ \<Rightarrow> Cast cast sz (step_exp \<Delta> e)
  )\<close> |
  \<open>step_exp \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (
    case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
      [(Val v\<^sub>1)\<sslash>var]e\<^sub>2
    ) | _ \<Rightarrow> Let var (step_exp \<Delta> e\<^sub>1) e\<^sub>2
  )\<close> |
  \<open>step_exp \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (
    case e\<^sub>3 of Val v\<^sub>3 \<Rightarrow> (
      case e\<^sub>2 of Val v\<^sub>2 \<Rightarrow> (
        case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
          case v\<^sub>1 of Immediate w \<Rightarrow> (
            if w = true then Val v\<^sub>2
            else Val v\<^sub>3
          ) | Unknown str t \<Rightarrow> Val (Unknown str (type v\<^sub>2))
        ) | _ \<Rightarrow> (Ite (step_exp \<Delta> e\<^sub>1) (Val v\<^sub>2) (Val v\<^sub>3))
      ) | _ \<Rightarrow> (Ite e\<^sub>1 (step_exp \<Delta> e\<^sub>2) (Val v\<^sub>3))
    ) | _ \<Rightarrow> (Ite e\<^sub>1 e\<^sub>2 (step_exp \<Delta> e\<^sub>3))
  )\<close> |
  \<open>step_exp \<Delta> (Extract sz\<^sub>1 sz\<^sub>2 e) = (
    case e of Val v \<Rightarrow> (
      case v of Immediate w \<Rightarrow> Val (Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2))
        | Unknown str t \<Rightarrow> Val (Unknown str (Imm ((sz\<^sub>1 - sz\<^sub>2) + 1)))
    ) | _ \<Rightarrow> Extract sz\<^sub>1 sz\<^sub>2 (step_exp \<Delta> e)
  )\<close> |
  \<open>step_exp \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (
    case e\<^sub>2 of Val v\<^sub>2 \<Rightarrow> (
      case e\<^sub>1 of Val v\<^sub>1 \<Rightarrow> (
        case v\<^sub>1 of
          Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
            Immediate w\<^sub>2 \<Rightarrow> Val (Immediate (w\<^sub>1 \<cdot> w\<^sub>2)) |
            Unknown str (Imm sz\<^sub>2) \<Rightarrow> case type v\<^sub>1 of
              Imm sz\<^sub>1 \<Rightarrow> Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2)))
          ) |
          Unknown str (Imm sz\<^sub>1) \<Rightarrow> case type v\<^sub>2 of
            Imm sz\<^sub>2 \<Rightarrow> Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2)))
      ) | _ \<Rightarrow> (Concat (step_exp \<Delta> e\<^sub>1) (Val v\<^sub>2))
    ) | _ \<Rightarrow> (Concat e\<^sub>1 (step_exp \<Delta> e\<^sub>2))
  )\<close>

fun
  step_pred_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>step_pred_exp \<Delta> (Val val) e' = False\<close> |
  \<open>step_pred_exp \<Delta> e e' = (e' = \<Delta> \<turnstile> e)\<close>

instance ..

end

lemma VAL_NO_STEP: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<leadsto> e')\<close>
  by simp

lemma STEP_NOT_VAL: 
  assumes \<open>(\<Delta> \<turnstile> e \<leadsto> e')\<close>
    shows \<open>e \<noteq> Val v\<close>
  using assms by auto

lemma VAR_IN:
  assumes \<open>(var, v) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (Var var) \<leadsto> (Val v)\<close>
  using assms by auto

lemma VAR_UNKNOWN:
  assumes \<open>(name, t) \<notin> dom \<Delta>\<close>
    shows \<open>\<Delta> \<turnstile> (Var (name, t)) \<leadsto> (Val (Unknown [] t))\<close>
  using assms by auto

lemma LOAD_STEP_ADDR:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2')\<close>
    shows \<open>\<Delta> \<turnstile> (Load e\<^sub>1 e\<^sub>2 ed sz) \<leadsto> (Load e\<^sub>1 e\<^sub>2' ed sz)\<close>
  using assms by (cases e\<^sub>2, auto) 

lemma LOAD_STEP_MEM:
  assumes \<open>(\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1')\<close>
    shows \<open>\<Delta> \<turnstile> (Load e\<^sub>1 (Val v\<^sub>2) ed sz) \<leadsto> (Load e\<^sub>1' (Val v\<^sub>2) ed sz)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma LOAD_BYTE: \<open>\<Delta> \<turnstile> (Load (Val (Storage v w v' sz)) (Val (Immediate w)) ed' sz) \<leadsto> (Val v')\<close>
  by auto

lemma LOAD_BYTE_FROM_NEXT:
  assumes \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (Load (Val (Storage v w\<^sub>1 v' sz)) (Val (Immediate w\<^sub>2)) ed sz) \<leadsto> (Load (Val v) (Val (Immediate w\<^sub>2)) ed sz)\<close>
  using assms by auto

lemma LOAD_UN_MEM: \<open>\<Delta> \<turnstile> (Load (Val (Unknown str t)) (Val v) ed sz) \<leadsto> (Val (Unknown str (Imm sz)))\<close>
  by auto

lemma LOAD_UN_ADDR: \<open>\<Delta> \<turnstile> (Load (Val (Storage v w\<^sub>1 v' sz)) (Val (Unknown str t)) ed sz') \<leadsto> (Val (Unknown str (Imm sz')))\<close>
  by auto

lemma LOAD_WORD_BE:
  assumes \<open>sz' > sz\<close> and \<open>succ w = w'\<close> and \<open>v = (Storage v' w'' v'' sz)\<close> 
    shows \<open>\<Delta> \<turnstile> (Load (Val v) (Val (Immediate w)) be sz') \<leadsto> (Concat (Load (Val v) (Val (Immediate w)) be sz) ((Load (Val v) (Val (Immediate w')) be (sz' - sz))))\<close> 
  using assms by auto

lemma LOAD_WORD_EL:
  assumes \<open>sz' > sz\<close> and \<open>succ w = w'\<close> and \<open>v = (Storage v' w'' v'' sz)\<close>
    shows \<open>\<Delta> \<turnstile> (Load (Val v) (Val (Immediate w)) el sz') \<leadsto> (Concat (Load (Val v) (Val (Immediate w')) el (sz' - sz)) ((Load (Val v) (Val (Immediate w)) el sz)))\<close> 
  using assms by auto


lemma STORE_STEP_VAL:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3) \<leadsto> (Store e\<^sub>1 e\<^sub>2 ed sz e\<^sub>3')\<close> 
  using assms by (cases e\<^sub>3, auto) 

lemma STORE_STEP_ADDR:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 e\<^sub>2 ed sz (Val v\<^sub>3)) \<leadsto> (Store e\<^sub>1 e\<^sub>2' ed sz (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>2, auto) 

lemma STORE_STEP_MEM:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Store e\<^sub>1 (Val v\<^sub>2) ed sz (Val v\<^sub>3)) \<leadsto> (Store e\<^sub>1' (Val v\<^sub>2) ed sz (Val v\<^sub>3))\<close> 
  using assms by (cases e\<^sub>1, auto) 

lemma STORE_WORD_BE:
  assumes \<open>sz' > sz\<close> and \<open>succ w = w'\<close> and \<open>type v = (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)\<close> 
      and \<open>e\<^sub>1 = (Store (Val v) (Val (Immediate w)) be sz (Cast High sz (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) be sz' (Val val)) \<leadsto> (Store e\<^sub>1 (Val (Immediate w')) be (sz' - sz) (Cast Low (sz' - sz) (Val val)))\<close> 
  using assms by auto

lemma STORE_WORD_EL:
  assumes \<open>sz' > sz\<close> and \<open>succ w = w'\<close> and \<open>type v = (Mem sz\<^sub>m\<^sub>e\<^sub>m sz)\<close> 
      and \<open>e\<^sub>1 = (Store (Val v) (Val (Immediate w)) el sz (Cast Low sz (Val val)))\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) el sz' (Val val)) \<leadsto> (Store e\<^sub>1 (Val (Immediate w')) el (sz' - sz) (Cast High (sz' - sz) (Val val)))\<close>
  using assms by auto

lemma STORE_VAL:
  assumes \<open>type v = Mem sz\<^sub>m\<^sub>e\<^sub>m sz\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Immediate w)) ed sz (Val v')) \<leadsto> (Val (Storage v w v' sz))\<close>
  using assms by auto

lemma STORE_UN_ADDR:
  assumes \<open>type v = t\<close>
    shows \<open>\<Delta> \<turnstile> (Store (Val v) (Val (Unknown str t')) ed sz' (Val v')) \<leadsto> (Val (Unknown str t))\<close>
  using assms by auto

lemma LET_STEP:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> (Let var e\<^sub>1' e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma LET: \<open>\<Delta> \<turnstile> (Let var (Val v\<^sub>1) e\<^sub>2) \<leadsto> ([(Val v\<^sub>1)\<sslash>var]e\<^sub>2)\<close>
  by auto

lemma ITE_STEP_COND:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>1, auto)

lemma ITE_STEP_THEN:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> (Ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3))\<close>
  using assms by (cases e\<^sub>2, auto)

lemma ITE_STEP_ELSE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3')\<close>
  using assms by (cases e\<^sub>3, auto)

lemma ITE_TRUE: \<open>\<Delta> \<turnstile> (Ite (Val (Immediate true)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>2)\<close>
  by auto

lemma ITE_FALSE: \<open>\<Delta> \<turnstile> (Ite (Val (Immediate false)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>3)\<close>
  by auto

lemma ITE_UNK:
  assumes \<open>type v\<^sub>2 = t'\<close>
    shows \<open>\<Delta> \<turnstile> (Ite (Val (Unknown str t)) (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val (Unknown str t'))\<close>
  using assms by auto

lemma BOP_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val v\<^sub>1) bop e\<^sub>2) \<leadsto> (BinOp (Val v\<^sub>1) bop e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto)

lemma BOP_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp e\<^sub>1 bop e\<^sub>2) \<leadsto> (BinOp e\<^sub>1' bop e\<^sub>2)\<close>
  using assms by (cases e\<^sub>1, auto)

lemma AOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (AOp aop) (Val (Unknown str t))) \<leadsto> (Val (Unknown str t))\<close>
  by auto

lemma AOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Unknown str t)) (AOp aop) (Val v)) \<leadsto> (Val (Unknown str t))\<close>
  by (cases v, auto)

lemma LOP_UNK_RHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp lop) (Val (Unknown str t))) \<leadsto> (Val (Unknown str (Imm 1)))\<close>
  by auto

lemma LOP_UNK_LHS: \<open>\<Delta> \<turnstile> (BinOp (Val (Unknown str t)) (LOp lop) (Val v)) \<leadsto> (Val (Unknown str (Imm 1)))\<close>
  by auto

lemma PLUS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Plus) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 +\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma MINUS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Minus) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 -\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma TIMES: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Times) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 *\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma DIV: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Divide) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 div\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SDIV: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp SDivide) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 div\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma MOD: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Mod) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 %\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SMOD: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp SMod) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 %\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LSL: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp LShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <<\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LSR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp RShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 >>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma ASR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp ARShift) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 >>>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LAND: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp And) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 &\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LOR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Or) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 |\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma XOR: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (AOp Xor) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 xor\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma EQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp Eq) (Val (Immediate w))) \<leadsto> (Val (Immediate (true)))\<close>
  by auto

lemma EQ_DIFF: 
  assumes \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Eq) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate false))\<close>
  using assms apply auto
  sorry

lemma NEQ_SAME: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w)) (LOp Neq) (Val (Immediate w))) \<leadsto> (Val (Immediate false))\<close>
  by auto

lemma NEQ_DIFF: 
  assumes \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Neq) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate true))\<close>
  using assms by auto

lemma LESS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Lt) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma LESS_EQ: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Le) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<le>\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SIGNED_LESS: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Slt) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 <\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma SIGNED_LESS_EQ: \<open>\<Delta> \<turnstile> (BinOp (Val (Immediate w\<^sub>1)) (LOp Sle) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<le>\<^sub>s\<^sub>b\<^sub>v w\<^sub>2)))\<close>
  by auto

lemma UOP: 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (UnOp uop e) \<leadsto> (UnOp uop e')\<close>
  using assms by (cases e, auto)

lemma UOP_UNK: \<open>\<Delta> \<turnstile> (UnOp uop (Val (Unknown str t))) \<leadsto> (Val (Unknown str t))\<close>
  by auto

lemma NOT: \<open>\<Delta> \<turnstile> (UnOp Not (Val (Immediate w))) \<leadsto> (Val (Immediate (~\<^sub>b\<^sub>v w)))\<close>
  by auto

lemma NEG: \<open>\<Delta> \<turnstile> (UnOp Neg (Val (Immediate w))) \<leadsto> (Val (Immediate (-\<^sub>b\<^sub>v w)))\<close>
  by auto

lemma CONCAT_RHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<close>
    shows \<open>\<Delta> \<turnstile> (Concat e\<^sub>1 e\<^sub>2) \<leadsto> (Concat e\<^sub>1 e\<^sub>2')\<close>
  using assms by (cases e\<^sub>2, auto)

lemma CONCAT_LHS:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<close>
    shows \<open>\<Delta> \<turnstile> (Concat e\<^sub>1 (Val v\<^sub>2)) \<leadsto> (Concat e\<^sub>1' (Val v\<^sub>2))\<close>
  using assms by (cases e\<^sub>1, auto)

lemma CONCAT_LHS_UN:
  assumes \<open>type v\<^sub>2 = Imm sz\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> (Concat (Val (Unknown str (Imm sz\<^sub>1))) (Val v\<^sub>2)) \<leadsto> (Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))))\<close>
  using assms by auto

lemma CONCAT_RHS_UN:
  assumes \<open>bits w = sz\<^sub>1\<close>
    shows \<open>\<Delta> \<turnstile> (Concat (Val (Immediate w)) (Val (Unknown str (Imm sz\<^sub>2)))) \<leadsto> (Val (Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))))\<close>
  using assms by auto 

lemma CONCAT: \<open>\<Delta> \<turnstile> (Concat (Val (Immediate w\<^sub>1)) (Val (Immediate w\<^sub>2))) \<leadsto> (Val (Immediate (w\<^sub>1 \<cdot> w\<^sub>2)))\<close>
  by auto

lemma EXTRACT: \<open>\<Delta> \<turnstile> (Extract sz\<^sub>1 sz\<^sub>2 (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)))\<close>
  by auto

lemma CAST_REDUCE:
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
    shows \<open>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto> (Cast cast sz e')\<close>
  using assms by (cases e, auto)

lemma CAST_UNK: \<open>\<Delta> \<turnstile> (Cast cast sz (Val (Unknown str t))) \<leadsto> (Val (Unknown str (Imm sz)))\<close>
  by auto

lemma CAST_LOW: \<open>\<Delta> \<turnstile> (Cast Low sz (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto

lemma CAST_HIGH: \<open>\<Delta> \<turnstile> (Cast High sz (Val (Immediate (num \<Colon> sz')))) \<leadsto> (Val (Immediate (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))))\<close>
  by auto

lemma CAST_SIGNED: \<open>\<Delta> \<turnstile> (Cast Signed sz (Val (Immediate w))) \<leadsto> (Val (Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto

lemma CAST_UNSIGNED: \<open>\<Delta> \<turnstile> (Cast Unsigned sz (Val (Immediate w))) \<leadsto> (Val (Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)))\<close>
  by auto





fun
  load_val :: \<open>val \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>load_val (Storage v w v' sz\<^sub>m\<^sub>e\<^sub>m) w' sz\<^sub>v\<^sub>a\<^sub>l = (if (w = w' \<and> sz\<^sub>m\<^sub>e\<^sub>m = sz\<^sub>v\<^sub>a\<^sub>l) then v' else load_val v w' sz\<^sub>v\<^sub>a\<^sub>l)\<close> |
  \<open>load_val (Unknown str t) _ sz\<^sub>v\<^sub>a\<^sub>l = Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)\<close>

fun
  load_val_be :: \<open>val \<Rightarrow> nat \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>load_val_be mem sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l = (
    case load_val mem w sz\<^sub>m\<^sub>e\<^sub>m of
      Immediate w\<^sub>v\<^sub>a\<^sub>l \<Rightarrow> (
        if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
          let sz\<^sub>v\<^sub>a\<^sub>l' = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) in 
          let w' = succ w in
          case load_val_be mem sz\<^sub>m\<^sub>e\<^sub>m w' sz\<^sub>v\<^sub>a\<^sub>l' of
            Immediate w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<Rightarrow> Immediate (w\<^sub>v\<^sub>a\<^sub>l \<cdot> w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t) |
            Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
        else Immediate w\<^sub>v\<^sub>a\<^sub>l
      ) |
      Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
  )\<close>

fun
  load_val_el :: \<open>val \<Rightarrow> nat \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>load_val_el mem sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l = (
    case load_val mem w sz\<^sub>m\<^sub>e\<^sub>m of
      Immediate w\<^sub>v\<^sub>a\<^sub>l \<Rightarrow> (
        if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
          let sz\<^sub>v\<^sub>a\<^sub>l' = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) in 
          let w' = succ w in
          case load_val_el mem sz\<^sub>m\<^sub>e\<^sub>m w' sz\<^sub>v\<^sub>a\<^sub>l' of
            Immediate w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<Rightarrow> Immediate (w\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t \<cdot> w\<^sub>v\<^sub>a\<^sub>l) |
            Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
        else Immediate w\<^sub>v\<^sub>a\<^sub>l
      ) |
      Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
  )\<close>

fun
  store_val :: \<open>val \<Rightarrow> word \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>store_val (Storage mem w v _) w' v' sz\<^sub>m\<^sub>e\<^sub>m = (
    let mem' = store_val mem w' v' sz\<^sub>m\<^sub>e\<^sub>m in
    if w = w' then mem'
    else (Storage mem' w v sz\<^sub>m\<^sub>e\<^sub>m)
  )\<close> |
  \<open>store_val mem w v sz\<^sub>m\<^sub>e\<^sub>m = Storage mem w v sz\<^sub>m\<^sub>e\<^sub>m\<close>

fun
  store_val_be :: \<open>val \<Rightarrow> nat \<Rightarrow> word \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>store_val_be mem sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l = (
    if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
      let sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) in 
      let w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l' \<sim> lo : 0 in
      let w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>v\<^sub>a\<^sub>l' in
      let w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' :: word = succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r in
      (store_val (store_val_be mem sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t sz\<^sub>v\<^sub>a\<^sub>l') w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>m\<^sub>e\<^sub>m)
    else
      store_val mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>m\<^sub>e\<^sub>m
  )\<close>

fun
  store_val_el :: \<open>val \<Rightarrow> nat \<Rightarrow> word \<Rightarrow> word \<Rightarrow> nat \<Rightarrow> val\<close>
where 
  \<open>store_val_el mem sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r w\<^sub>v\<^sub>a\<^sub>l sz\<^sub>v\<^sub>a\<^sub>l = (
    if sz\<^sub>m\<^sub>e\<^sub>m > 0 \<and> sz\<^sub>v\<^sub>a\<^sub>l > sz\<^sub>m\<^sub>e\<^sub>m then
      let sz\<^sub>v\<^sub>a\<^sub>l' :: nat = (sz\<^sub>v\<^sub>a\<^sub>l - sz\<^sub>m\<^sub>e\<^sub>m) in 
      let w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>v\<^sub>a\<^sub>l \<sim> lo : sz\<^sub>m\<^sub>e\<^sub>m in
      let w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l :: word = ext w\<^sub>v\<^sub>a\<^sub>l \<sim> hi : sz\<^sub>m\<^sub>e\<^sub>m \<sim> lo : 0 in
      let w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' :: word = succ w\<^sub>a\<^sub>d\<^sub>d\<^sub>r in
      (store_val (store_val_el mem sz\<^sub>m\<^sub>e\<^sub>m w\<^sub>a\<^sub>d\<^sub>d\<^sub>r' w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>a\<^sub>t sz\<^sub>v\<^sub>a\<^sub>l') w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>m\<^sub>e\<^sub>m)
    else 
      store_val mem w\<^sub>a\<^sub>d\<^sub>d\<^sub>r (Immediate w\<^sub>v\<^sub>a\<^sub>l) sz\<^sub>m\<^sub>e\<^sub>m
  )\<close>








fun
  eval_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> val\<close>
where
  \<open>eval_exp \<Delta> (Val v) = v\<close> |
  \<open>eval_exp \<Delta> (Var var) = (let (name, t) = var in if var \<in> dom \<Delta> then (the (\<Delta> var)) else (Unknown [] t))\<close> |
  \<open>eval_exp \<Delta> (UnOp unop e) = ( 
    case (eval_exp \<Delta> e) of
      Immediate w \<Rightarrow> Immediate ((operator_unop unop) w) |
      Unknown str t \<Rightarrow> Unknown str t
  )\<close> |
  \<open>eval_exp \<Delta> (BinOp e\<^sub>1 binop e\<^sub>2) = (
    let v\<^sub>1 = (eval_exp \<Delta> e\<^sub>1) in
    let v\<^sub>2 = (eval_exp \<Delta> e\<^sub>2) in
    case binop of
      AOp aop \<Rightarrow> (case v\<^sub>1 of
        Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
          Immediate w\<^sub>2 \<Rightarrow> Immediate (operator_aop aop w\<^sub>1 w\<^sub>2) |
          Unknown str t \<Rightarrow> Unknown str t) |
        Unknown str t \<Rightarrow> Unknown str t)
       |
      LOp lop \<Rightarrow> (case v\<^sub>1 of
        Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
          Immediate w\<^sub>2 \<Rightarrow> Immediate (operator_lop lop w\<^sub>1 w\<^sub>2) |
          Unknown str t \<Rightarrow> Unknown str (Imm 1)) |
        Unknown str t \<Rightarrow> Unknown str (Imm 1))
  )\<close> |
  \<open>eval_exp \<Delta> (Cast cast sz e) = (
    let v = eval_exp \<Delta> e in
    case v of
      Immediate w \<Rightarrow> (case cast of
        Low \<Rightarrow> Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0) |
        High \<Rightarrow> Immediate (ext w \<sim> hi : (bits w - 1) \<sim> lo : (bits w - sz)) |
        Signed \<Rightarrow> Immediate (exts w \<sim> hi : (sz - 1) \<sim> lo : 0) |
        Unsigned \<Rightarrow> Immediate (ext w \<sim> hi : (sz - 1) \<sim> lo : 0)) |
      Unknown str t \<Rightarrow> Unknown str (Imm sz)
  )\<close> |
  \<open>eval_exp \<Delta> (Let var e\<^sub>1 e\<^sub>2) = (eval_exp (\<Delta>(var \<mapsto> (eval_exp \<Delta> e\<^sub>1))) e\<^sub>2)\<close> |
  \<open>eval_exp \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in
    let v\<^sub>2 = eval_exp \<Delta> e\<^sub>2 in
    case v\<^sub>1 of
      Immediate w \<Rightarrow> (
        if w = true then v\<^sub>2
        else eval_exp \<Delta> e\<^sub>3) |
      Unknown str t \<Rightarrow> Unknown str (type v\<^sub>2)
  )\<close> |
  \<open>eval_exp \<Delta> (Extract sz\<^sub>1 sz\<^sub>2 e) = (
    case (eval_exp \<Delta> e) of
      Immediate w \<Rightarrow> Immediate (ext w \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2) |
      Unknown str t \<Rightarrow> Unknown str (Imm ((sz\<^sub>1 - sz\<^sub>2) + 1))
  )\<close> |
  \<open>eval_exp \<Delta> (Concat e\<^sub>1 e\<^sub>2) = (
    let v\<^sub>1 = (eval_exp \<Delta> e\<^sub>1) in
    let v\<^sub>2 = (eval_exp \<Delta> e\<^sub>2) in
    case v\<^sub>1 of
      Immediate w\<^sub>1 \<Rightarrow> (case v\<^sub>2 of 
        Immediate w\<^sub>2 \<Rightarrow> Immediate (w\<^sub>1 \<cdot> w\<^sub>2) |
        Unknown str (Imm sz\<^sub>2) \<Rightarrow> case type v\<^sub>1 of
          Imm sz\<^sub>1 \<Rightarrow> Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))        
      ) |
      Unknown str (Imm sz\<^sub>1) \<Rightarrow> case type v\<^sub>2 of
        Imm sz\<^sub>2 \<Rightarrow> Unknown str (Imm (sz\<^sub>1 + sz\<^sub>2))
      
  )\<close> |
  \<open>eval_exp \<Delta> (Load e\<^sub>1 e\<^sub>2 ed sz\<^sub>v\<^sub>a\<^sub>l) = (
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in 
    case type v\<^sub>1 of Mem _ sz\<^sub>m\<^sub>e\<^sub>m \<Rightarrow> (
      case eval_exp \<Delta> e\<^sub>2 of 
        Immediate w \<Rightarrow> (
          case ed of
            be \<Rightarrow> load_val_be v\<^sub>1 sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l |
            el \<Rightarrow> load_val_el v\<^sub>1 sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l
        ) |
        Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
  ))\<close> |
  \<open>eval_exp \<Delta> (Store e\<^sub>1 e\<^sub>2 ed sz\<^sub>v\<^sub>a\<^sub>l e\<^sub>3) = (
    let v\<^sub>1 = eval_exp \<Delta> e\<^sub>1 in 
    case type v\<^sub>1 of Mem _ sz\<^sub>m\<^sub>e\<^sub>m \<Rightarrow> (
      case eval_exp \<Delta> e\<^sub>2 of 
        Immediate w \<Rightarrow> (
          case ed of
            be \<Rightarrow> load_val_be v\<^sub>1 sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l |
            el \<Rightarrow> load_val_el v\<^sub>1 sz\<^sub>m\<^sub>e\<^sub>m w sz\<^sub>v\<^sub>a\<^sub>l
        ) |
        Unknown str _ \<Rightarrow> Unknown str (Imm sz\<^sub>v\<^sub>a\<^sub>l)
  ))\<close>



fun
  eval_exps_pred :: \<open>variables \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto>* _\<close>)
where
  \<open>(\<Delta> \<turnstile> e \<leadsto>* v) = (v = eval_exp \<Delta> e)\<close>

(* TODO if I can prove this we're good *)
lemma REDUCE: 
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close>
      and \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto>* v\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto>* v\<close>
  using assms sorry

end
