theory Expression_Rules
  imports Expression_Syntax_Locales
begin

inductive
  step_exp :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<leadsto> _\<close> [400, 400, 400] 401)
where
  \<comment> \<open>Var rules\<close>
  VarIn: \<open>\<lbrakk>((name' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<leadsto> Val val\<close> |
  VarNotIn: \<open>\<lbrakk>((name' :\<^sub>t t)) \<notin> dom \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<leadsto> unknown[str]: t\<close> |

  \<comment> \<open>Load\<close>
  LoadStepAddr: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1[e\<^sub>2', ed]:usz)\<close> |
  LoadStepMem: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close> |
  LoadByte: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> Val v'\<close> | 
  LoadByteFromNext: \<open>\<lbrakk>w \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ((v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<leadsto> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<close> |
  LoadUnMem: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<leadsto> unknown[str]: imm\<langle>sz\<rangle>\<close> |
  LoadUnAddr: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<leadsto> unknown[str]: imm\<langle>sz'\<rangle>\<close> |
  LoadWordBe: \<open>\<lbrakk>sz > sz\<^sub>m\<^sub>e\<^sub>m; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) \<copyright> (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> |
  LoadWordEl: \<open>\<lbrakk>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) \<copyright> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> |

  \<comment> \<open>Store\<close>
  StoreStepVal: \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> |
  StoreStepAddr: \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreStepMem: \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreWordBe: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<leadsto> (((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val))) with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreWordEl: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<leadsto> (((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val))) with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreVal: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<leadsto> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close> |
  StoreUnAddr: \<open>type v = t \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [unknown[str]: t', ed]:usz \<leftarrow> (Val v')) \<leadsto> (unknown[str]: t)\<close> |


  \<comment> \<open>Let rules\<close>
  LetStep: \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> (Let var e\<^sub>1' e\<^sub>2)\<close> |
  Let: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<leadsto> [v\<sslash>var]e\<close> |
  (* one missing rule *)

  \<comment> \<open>If rules\<close>
  IfStepCond: \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<close> |
  IfStepThen: \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<close> |
  IfStepElse: \<open>\<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> ite e\<^sub>1 e\<^sub>2 e\<^sub>3'\<close> |
  IfTrue: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>2)\<close> |
  IfFalse: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> (Val v\<^sub>3)\<close> |
  IfUnknown: \<open>\<lbrakk>type v\<^sub>2 = t'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> unknown[str]: t'\<close> |

  \<comment> \<open>Binary operation rules\<close>
  BopRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<leadsto> BinOp (Val v) bop e\<^sub>2'\<close> |
  BopLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<leadsto> BinOp e\<^sub>1' bop e\<^sub>2\<close> |

  AopUnkLhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e \<leadsto> unknown[str]: t\<close> |
  AopUnkRhs: \<open>\<Delta> \<turnstile> BinOp e (AOp aop) (unknown[str]: t) \<leadsto> unknown[str]: t\<close> |

  LopUnkLhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e \<leadsto> unknown[str]: imm\<langle>1\<rangle>\<close> |
  LopUnkRhs: \<open>\<Delta> \<turnstile> BinOp e (LOp lop) (unknown[str]: t) \<leadsto> unknown[str]: imm\<langle>1\<rangle>\<close> |

  \<comment> \<open>Arithmetic rules\<close>
  Plus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Minus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Times: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Div: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SDiv: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Mod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SMod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsl: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Asr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Logical rules\<close>
  LAnd: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  XOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  (*these aren't really right*)
  EqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> true\<close> |
  EqDiff: \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> false\<close> |
  NeqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> false\<close> |
  NeqDiff: \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1)) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2) \<leadsto> true\<close> |
  Less: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLess: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<leadsto> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Unary op\<close>
  Uop: \<open>\<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> (UnOp uop e) \<leadsto> (UnOp uop e')\<close> |
  UopUnk: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<leadsto> (unknown[str]: t)\<close> |
  Not: \<open>\<Delta> \<turnstile> (\<sim>(num \<Colon> sz)) \<leadsto> (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |
  Neg: \<open>\<Delta> \<turnstile> (-(num \<Colon> sz)) \<leadsto> (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |

  \<comment> \<open>Concat\<close>
  ConcatRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> (e\<^sub>1 \<copyright> e\<^sub>2')\<close> |
  ConcatLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 \<copyright> (Val v\<^sub>2)) \<leadsto> (e\<^sub>1' \<copyright> (Val v\<^sub>2))\<close> |
  ConcatRhsUn: \<open>type v = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) \<copyright> (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<leadsto> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  ConcatLhsUn: \<open>type v = imm\<langle>sz\<^sub>2\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> (Val v)) \<leadsto> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  Concat: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |

  \<comment> \<open>Extract\<close>
  Extract: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<leadsto> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)\<close> |
  ExtractReduce: \<open>\<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<leadsto> (extract:sz\<^sub>1:sz\<^sub>2[e'])\<close> |
  ExtractUn: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<leadsto> (unknown[str]: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>)\<close> |

  \<comment> \<open>Cast\<close>
  CastReduce: \<open>\<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz e) \<leadsto> (Cast cast sz e')\<close> |
  CastUnk: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> (unknown[str]: imm\<langle>sz\<rangle>)\<close> |
  CastLow: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastHigh: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))\<close> |
  CastSigned: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastUnsigned: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<leadsto> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>

lemma step_exp_induct[consumes 1, case_names VarIn VarNotIn LoadStepAddr LoadStepMem LoadByte 
      LoadByteFromNext LoadUnMem LoadUnAddr LoadWordBe LoadWordEl StoreStepVal StoreStepAddr 
      StoreStepMem StoreWordBe StoreWordEl StoreVal StoreUnAddr LetStep Let IfStepCond IfStepThen 
      IfStepElse IfTrue IfFalse IfUnknown BopRhs BopLhs AopUnkLhs AopUnkRhs LopUnkLhs LopUnkRhs Plus 
      Minus Times Div SDiv Mod SMod Lsl Lsr Asr LAnd LOr XOr EqSame EqDiff NeqSame NeqDiff Less 
      LessEq SignedLess SignedLessEq Uop UopUnk Not Neg ConcatRhs ConcatLhs ConcatRhsUn ConcatLhsUn 
      Concat Extract ExtractReduce ExtractUn CastReduce CastUnk CastLow CastHigh CastSigned 
      CastUnsigned]:
  assumes steps: \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close>
      and inducts: \<open>\<And>name' t val. (name' :\<^sub>t t, val) \<in>\<^sub>\<Delta> \<Delta> \<Longrightarrow> P (name' :\<^sub>t t) (Val val)\<close>
           \<open>\<And>name' t str. name' :\<^sub>t t \<notin> dom \<Delta> \<Longrightarrow> P (name' :\<^sub>t t) unknown[str]: t\<close>
           \<open>\<And> e\<^sub>2 e\<^sub>2' e\<^sub>1 ed sz. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> P e\<^sub>2 e\<^sub>2' \<Longrightarrow> P e\<^sub>1[e\<^sub>2, ed]:usz e\<^sub>1[e\<^sub>2', ed]:usz\<close>
           \<open>\<And>e\<^sub>1 e\<^sub>1' v\<^sub>2 ed sz. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P e\<^sub>1[Val v\<^sub>2, ed]:usz e\<^sub>1'[Val v\<^sub>2, ed]:usz\<close>
           \<open>\<And>v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz ed. P v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz][num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, ed]:usz (Val v')\<close>
\<open>\<And>w num\<^sub>2 sz\<^sub>2 v v' sz ed. w \<noteq> num\<^sub>2 \<Colon> sz\<^sub>2 \<Longrightarrow> P v[w \<leftarrow> v', sz][num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz Val v[num\<^sub>2 \<Colon> sz\<^sub>2, ed]:usz\<close>
\<open>\<And>str t v ed sz. P unknown[str]: t[Val v, ed]:usz unknown[str]: imm\<langle>sz\<rangle>\<close>
\<open>\<And>v w v' sz str t ed sz'. P v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' unknown[str]: imm\<langle>sz'\<rangle>\<close>
\<open>\<And>sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num.
    sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
    type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow>
    P ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz) ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<copyright> ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m))\<close>
\<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m sz num.
    type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow>
    sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow> P ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz) ((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<copyright> ((Val v)[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close>
\<open>\<And>e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2 en sz. \<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3' \<Longrightarrow> P e\<^sub>3 e\<^sub>3' \<Longrightarrow> P e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3 e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3'\<close>
\<open>\<And>e\<^sub>2 e\<^sub>2' e\<^sub>1 en sz v\<^sub>3. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> P e\<^sub>2 e\<^sub>2' \<Longrightarrow> P e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> Val v\<^sub>3 e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> Val v\<^sub>3\<close>
\<open>\<And>e\<^sub>1 e\<^sub>1' v\<^sub>2 en sz v\<^sub>3. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P e\<^sub>1 with [Val v\<^sub>2, en]:usz \<leftarrow> Val v\<^sub>3 e\<^sub>1' with [Val v\<^sub>2, en]:usz \<leftarrow> Val v\<^sub>3\<close>
\<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num val.
    sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
    type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow>
    P ((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz \<leftarrow> Val val)
     (((Val v) with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> high:sz\<^sub>m\<^sub>e\<^sub>m[Val val]) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> low:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val val])\<close>
\<open>\<And>sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r num val.
    sz\<^sub>m\<^sub>e\<^sub>m < sz \<Longrightarrow>
    type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow>
    P (Val v with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz \<leftarrow> Val val)
     ((Val v with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> low:sz\<^sub>m\<^sub>e\<^sub>m[Val val]) with [succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz - sz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> high:sz - sz\<^sub>m\<^sub>e\<^sub>m[Val val])\<close>
\<open>\<And>v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m num ed v'.
    type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> P Val v with [num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> Val v' v[num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m]\<close>
\<open>\<And>v t str t' ed sz v'. type v = t \<Longrightarrow> P (Val v with [unknown[str]: t', ed]:usz \<leftarrow> Val v') unknown[str]: t\<close>
\<open>\<And>e\<^sub>1 e\<^sub>1' var e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P (exp.Let var e\<^sub>1 e\<^sub>2) (exp.Let var e\<^sub>1' e\<^sub>2)\<close>
\<open>\<And>var v e. P (exp.Let var (Val v) e) ([v\<sslash>var]e)\<close>
\<open>\<And>e\<^sub>1 e\<^sub>1' v\<^sub>2 v\<^sub>3. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P ite e\<^sub>1 Val v\<^sub>2 Val v\<^sub>3 ite e\<^sub>1' Val v\<^sub>2 Val v\<^sub>3\<close>
\<open>\<And>e\<^sub>2 e\<^sub>2' e\<^sub>1 v\<^sub>3. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> P e\<^sub>2 e\<^sub>2' \<Longrightarrow> P ite e\<^sub>1 e\<^sub>2 Val v\<^sub>3 ite e\<^sub>1 e\<^sub>2' Val v\<^sub>3\<close>
\<open>\<And>e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2. \<Delta> \<turnstile> e\<^sub>3 \<leadsto> e\<^sub>3' \<Longrightarrow> P e\<^sub>3 e\<^sub>3' \<Longrightarrow> P ite e\<^sub>1 e\<^sub>2 e\<^sub>3 ite e\<^sub>1 e\<^sub>2 e\<^sub>3'\<close>
\<open>\<And>v\<^sub>2 v\<^sub>3. P ite true Val v\<^sub>2 Val v\<^sub>3 (Val v\<^sub>2)\<close>
\<open>\<And>v\<^sub>2 v\<^sub>3. P ite false Val v\<^sub>2 Val v\<^sub>3 (Val v\<^sub>3)\<close>
\<open>\<And>v\<^sub>2 t' str t v\<^sub>3. type v\<^sub>2 = t' \<Longrightarrow> P (ite (unknown[str]: t) Val v\<^sub>2 Val v\<^sub>3) unknown[str]: t'\<close>
\<open>\<And>e\<^sub>2 e\<^sub>2' v bop. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> P e\<^sub>2 e\<^sub>2' \<Longrightarrow> P (BinOp (Val v) bop e\<^sub>2) (BinOp (Val v) bop e\<^sub>2')\<close>
\<open>\<And>e\<^sub>1 e\<^sub>1' bop e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P (BinOp e\<^sub>1 bop e\<^sub>2) (BinOp e\<^sub>1' bop e\<^sub>2)\<close>
\<open>\<And>str t aop e. P (BinOp unknown[str]: t (AOp aop) e) unknown[str]: t\<close>
\<open>\<And>e aop str t. P (BinOp e (AOp aop) unknown[str]: t) unknown[str]: t\<close>
\<open>\<And>str t lop e. P (BinOp (unknown[str]: t) (LOp lop) e) (unknown[str]: imm\<langle>1\<rangle>)\<close>
\<open>\<And>e lop str t. P (BinOp e (LOp lop) unknown[str]: t) unknown[str]: imm\<langle>1\<rangle>\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) mod (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num sz. P (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) true\<close>
\<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = (true::word) \<Longrightarrow> P (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) false\<close>
\<open>\<And>num sz. P (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) false\<close>
\<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. (num\<^sub>1 \<Colon> sz\<^sub>1) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = (true::word) \<Longrightarrow> P (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2)) true\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>num\<^sub>1 sz num\<^sub>2. P ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close>
\<open>\<And>e e' uop. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> P e e' \<Longrightarrow> P (UnOp uop e) (UnOp uop e')\<close>
\<open>\<And>uop str t. P (UnOp uop unknown[str]: t) unknown[str]: t\<close>
\<open>\<And>num sz. P (\<sim> (num \<Colon> sz)) (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
\<open>\<And>num sz. P (- (num \<Colon> sz)) (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close>
\<open>\<And>e\<^sub>2 e\<^sub>2' e\<^sub>1. \<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> P e\<^sub>2 e\<^sub>2' \<Longrightarrow> P (e\<^sub>1 \<copyright> e\<^sub>2) (e\<^sub>1 \<copyright> e\<^sub>2')\<close>
\<open>\<And>e\<^sub>1 e\<^sub>1' v\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> P e\<^sub>1 e\<^sub>1' \<Longrightarrow> P (e\<^sub>1 \<copyright> Val v\<^sub>2) (e\<^sub>1' \<copyright> Val v\<^sub>2)\<close>
\<open>\<And>v sz\<^sub>1 str sz\<^sub>2. type v = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> P (Val v \<copyright> unknown[str]: imm\<langle>sz\<^sub>2\<rangle>) unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
\<open>\<And>v sz\<^sub>2 str sz\<^sub>1. type v = imm\<langle>sz\<^sub>2\<rangle> \<Longrightarrow> P (unknown[str]: imm\<langle>sz\<^sub>1\<rangle> \<copyright> Val v) unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>\<close>
\<open>\<And>num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2. P ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close>
\<open>\<And>sz\<^sub>1 sz\<^sub>2 num sz. P extract:sz\<^sub>1:sz\<^sub>2[num \<Colon> sz] ext num \<Colon> sz \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2\<close>
\<open>\<And>e e' sz\<^sub>1 sz\<^sub>2. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> P e e' \<Longrightarrow> P extract:sz\<^sub>1:sz\<^sub>2[e] extract:sz\<^sub>1:sz\<^sub>2[e']\<close>
\<open>\<And>sz\<^sub>1 sz\<^sub>2 str t. P extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t] unknown[str]: imm\<langle>sz\<^sub>1 - sz\<^sub>2 + 1\<rangle>\<close>
\<open>\<And>e e' cast sz. \<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> P e e' \<Longrightarrow> P cast:sz[e] cast:sz[e']\<close>
\<open>\<And>cast sz str t. P cast:sz[unknown[str]: t] unknown[str]: imm\<langle>sz\<rangle>\<close>
\<open>\<And>sz num sz'. P low:sz[num \<Colon> sz'] ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
\<open>\<And>sz num sz'. P high:sz[num \<Colon> sz'] ext num \<Colon> sz' \<sim> hi : sz' - 1 \<sim> lo : sz' - sz\<close>
\<open>\<And>sz num sz'. P extend:sz[num \<Colon> sz'] ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close>
\<open>\<And>sz num sz'. P pad:sz[num \<Colon> sz'] ext num \<Colon> sz' \<sim> hi : sz - 1 \<sim> lo : 0\<close> 
    shows \<open>P e e'\<close>
  using steps apply - 
  apply (drule step_exp.induct[where P = \<open>\<lambda>\<Delta>' e e'. \<Delta>' = \<Delta> \<longrightarrow> P e e'\<close>])
  apply (rule impI, (simp only:)?, (erule impE, rule refl)?, rule inducts, (assumption+)?)+
  by auto


text \<open>An expression transition always makes progress\<close>

lemma step_exp_neq': 
  assumes \<open>\<Delta> \<turnstile> e \<leadsto> e'\<close> 
    shows \<open>e \<noteq> e'\<close>
using assms proof (induct rule: step_exp.induct)
  case (LoadByteFromNext w num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  then show ?case 
    by (cases w rule: word_exhaust, auto)
qed simp_all

corollary step_exp_neq: \<open>\<not>(\<Delta> \<turnstile> e \<leadsto> e)\<close>
  using step_exp_neq' by auto

text \<open>Therefore, a value can never be a transition\<close>

lemma step_exp_val_no_step_intermediary: \<open>\<Delta> \<turnstile> e \<leadsto> e' \<Longrightarrow> e \<noteq> (Val v)\<close>
  by (induct rule: step_exp.induct, simp_all)

corollary step_exp_not_val[simp]: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<leadsto> e)\<close>
  using step_exp_val_no_step_intermediary by blast

interpretation step_exp_not_val: exp_val_syntax \<open>\<lambda>e _. (\<And>\<Delta> e'. \<not>(\<Delta> \<turnstile> e \<leadsto> e'))\<close>
  by (standard, simp)

\<comment> \<open>Ensure transition of common values are in the simpset.\<close>
(* TODO check these do not already exist *)
declare step_exp_not_val.word[simp add] 
declare step_exp_not_val.storage[simp add]
declare step_exp_not_val.unknown[simp add]

(* TODO *)
lemma step_exp_not_bv_concat[simp]: \<open>\<not>(\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e)\<close>
  unfolding bv_concat.simps by (rule step_exp_not_val.word)

subsubsection \<open>Elimination rules\<close>

subsection \<open>Val\<close>

inductive_cases ValE: \<open>\<Delta> \<turnstile> (Val v) \<leadsto> e\<close>
inductive_cases VarE: \<open>\<Delta> \<turnstile> (name' :\<^sub>t t) \<leadsto> e\<close>

inductive_cases LoadStepAddrE: \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<leadsto> e\<close>
inductive_cases LoadStepMemE: \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<leadsto> e\<close>
inductive_cases LoadByteE: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<leadsto> e\<close> 
inductive_cases LoadByteFromNextE: \<open>\<Delta> \<turnstile> ((v[w \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<leadsto> e\<close>
inductive_cases LoadUnMemE: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<leadsto> e\<close> 
inductive_cases LoadUnAddrE: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<leadsto> e\<close> 
inductive_cases LoadWordBeE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<leadsto> e\<close>
inductive_cases LoadWordElE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<leadsto> e\<close>

inductive_cases StoreStepValE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<leadsto> e\<close>
inductive_cases StoreStepAddrE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases StoreStepMemE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases StoreWordE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), en]:usz \<leftarrow> (Val val)) \<leadsto> e\<close>
inductive_cases StoreWordBeE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<leadsto> e\<close>
inductive_cases StoreWordElE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<leadsto> e\<close>
inductive_cases StoreUnAddrE: \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: t', ed]:usz' \<leftarrow> (Val v')) \<leadsto> e\<close>

inductive_cases LetStepE: \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<leadsto> e\<close>
inductive_cases LetE: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<leadsto> e'\<close>

inductive_cases IfStepCondE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases IfStepThenE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases IfStepElseE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<leadsto> e\<close>
inductive_cases IfTrueE: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases IfFalseE: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>
inductive_cases IfUnknownE: \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<leadsto> e\<close>

inductive_cases BopRhsE: \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<leadsto> e\<close>
inductive_cases BopLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<leadsto> e\<close>

inductive_cases AopUnkRhsE: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e\<^sub>2 \<leadsto> e\<close>
inductive_cases AopUnkLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (AOp aop) unknown[str]: t \<leadsto> e\<close>

inductive_cases LopUnkRhsE: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp aop) e\<^sub>2 \<leadsto> e\<close>
inductive_cases LopUnkLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (LOp aop) unknown[str]: t \<leadsto> e\<close>

inductive_cases PlusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases MinusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases TimesE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases DivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases SDivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases ModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close>
inductive_cases SModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm SModE
inductive_cases LslE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LslE
inductive_cases LsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LsrE
inductive_cases AsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm AsrE
inductive_cases LAndE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LAndE
inductive_cases LOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LOrE
inductive_cases XOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm XOrE
inductive_cases EqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<leadsto> e\<close> thm EqSameE
inductive_cases EqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close> thm EqDiffE
inductive_cases NeqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<leadsto> e\<close> thm NeqSameE
inductive_cases NeqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1)) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2) \<leadsto> e\<close> thm NeqDiffE
inductive_cases LessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LessE
inductive_cases LessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm LessEqE
inductive_cases SignedLessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm SignedLessE
inductive_cases SignedLessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<leadsto> e\<close> thm SignedLessEqE

inductive_cases UopE: \<open>\<Delta> \<turnstile> (UnOp uop e) \<leadsto> e'\<close>
inductive_cases UopUnkE: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<leadsto> e\<close>
inductive_cases NotE: \<open>\<Delta> \<turnstile> (\<sim>(num \<Colon> sz)) \<leadsto> e\<close>
inductive_cases NegE: \<open>\<Delta> \<turnstile> (-(num \<Colon> sz)) \<leadsto> e\<close>

inductive_cases ConcatRhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> e\<^sub>2) \<leadsto> e\<close>
inductive_cases ConcatLhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 \<copyright> (Val v\<^sub>2)) \<leadsto> e\<close>
inductive_cases ConcatRhsUnE: \<open>\<Delta> \<turnstile> ((Val v) \<copyright> (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<leadsto> e\<close>
inductive_cases ConcatLhsUnE: \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) \<copyright> (Val v)) \<leadsto> e\<close>
inductive_cases ConcatE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<copyright> (num\<^sub>2 \<Colon> sz\<^sub>2)) \<leadsto> e\<close>

inductive_cases ExtractE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<leadsto> e\<close>
inductive_cases ExtractReduceE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<leadsto> e'\<close>
inductive_cases ExtractUnE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<leadsto> e\<close>

inductive_cases CastReduceE: \<open>\<Delta> \<turnstile> (Cast cast sz e) \<leadsto> e'\<close>
inductive_cases CastUnkE: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<leadsto> e\<close>
inductive_cases CastLowE: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<leadsto> e\<close>
inductive_cases CastHighE: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<leadsto> e\<close>
inductive_cases CastSignedE: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<leadsto> e\<close>
inductive_cases CastUnsignedE: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<leadsto> e\<close>

(* TODO move *)
lemma Val_not_inject: "v \<noteq> v' \<Longrightarrow> Val v \<noteq> Val v'"
  by simp
(*
subsubsection \<open>Reduced Expressions tend to be deterministic\<close>

text \<open>Reduced Loads are deterministic\<close>

inductive_cases LoadReducedE: \<open>\<Delta> \<turnstile> ((Val v)[(Val v'), en]:usz) \<leadsto> e\<close>

lemma determ_step_exp_reduced_load:
  assumes 1: \<open>\<Delta> \<turnstile> ((Val v\<^sub>1)[(Val v\<^sub>2), en]:usz) \<leadsto> e\<^sub>1\<close>
      and 2: \<open>\<Delta> \<turnstile> ((Val v\<^sub>1)[(Val v\<^sub>2), en]:usz) \<leadsto> e\<^sub>2\<close>
    shows \<open>e\<^sub>1 = e\<^sub>2\<close>
  using 1 2 apply (elim LoadReducedE ValE)
  apply simp_all
       defer defer defer defer
  using 2 apply simp_all
  apply (elim LoadByteE)
*)

(*
lemma step_exp_non_circular:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>2\<close> 
    shows \<open>\<not>(\<Delta> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>1)\<close>
using assms proof (induct rule: step_exp.induct)
  case (LoadStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 ed sz)
  show ?case
    apply (rule notI)
    apply (rule LoadStepAddrE, simp_all)
    using LoadStepAddr by simp_all
next
  case (LoadStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 ed sz)
  show ?case
    apply (rule notI)
    apply (rule LoadStepMemE, simp_all)
    using LoadStepMem by simp_all
next
  case (LoadByteFromNext num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  show ?case 
    apply (rule notI)
    apply (rule LoadStepAddrE, auto)
    using storage_constructor_exp_def storage_constructor_val_def by auto
next
  case (LoadWordBe sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    apply (rule notI)
    by (rule ConcatRhsE, auto)
next
  case (LoadWordEl sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    apply (rule notI)
    by (rule ConcatRhsE, auto)
next
  case (StoreStepVal \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2 en sz)
  show ?case 
    apply (rule notI)
    apply (rule StoreStepValE, auto)
    using StoreStepVal by auto
next
  case (StoreStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 en sz v\<^sub>3)
  show ?case 
    apply (rule notI)
    apply (rule StoreStepAddrE, auto)
    using StoreStepAddr by auto
next
  case (StoreStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 en sz v\<^sub>3)
  show ?case 
    apply (rule notI)
    apply (rule StoreStepMemE, auto)
    using StoreStepMem by auto
next
  case (StoreWordBe sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    apply (rule notI)
    apply (rule StoreStepValE)
    using StoreWordBe.hyps(3) by blast+
next
  case (StoreWordEl sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    apply (rule notI)
    apply (rule StoreStepValE)
    using StoreWordEl.hyps(3) by blast+
next
  case (LetStep \<Delta> e\<^sub>1 e\<^sub>1' var e\<^sub>2)
  show ?case 
    apply (rule notI)
    apply (rule LetStepE, auto)
    using LetStep by auto
next
  case (Let \<Delta> var v e)
  then show ?case
  proof (rule notI, induct e)
    case (Var x)
    thus ?case 
    proof (cases \<open>var = x\<close>)
      case True
      then show ?thesis 
        using Var by simp
    next
      case False
      then show ?thesis 
        using Var apply auto        
        apply (cases x rule: var_exhaust)
        using VarE var_constructor_exp_def by fastforce
    qed
  next
    case (Load e1 e2 x3 x4)
    then show ?case 
      apply auto
      apply (rule LoadStepAddrE, simp_all)
      by simp_all
  next
    case (Store e1 e2 x3 x4 e3)
    then show ?case 
      apply auto
      apply (rule StoreStepValE, simp_all)
      by simp_all      
  next
    case (BinOp e1 x2a e2)
    then show ?case 
      apply auto
      apply (rule BopLhsE, auto)
      apply (metis false.not_let true.not_let)
      apply (smt (verit, best) bv_eq_def false.not_let' lor_false lor_true(1) lor_true(2) nat_neq_iff true.not_let' word_eq)
      apply (metis false.not_let' true.not_let')
      by (smt (verit, best) bv_eq_def false_word lor_false lor_true(1) lor_true(2) order_less_imp_not_eq true_word word.not_let' word_not_sz_neqI)
  next
    case (UnOp x1a e)
    then show ?case 
      apply auto
      by (rule UopE, auto)
  next
    case (Cast x1a x2a e)
    then show ?case 
      apply auto
      apply (rule CastReduceE, auto)
      by (metis step_exp.Let step_exp_not_ext)+
  next
    case (Let x1a e1 e2)
    then show ?case 
      apply auto
      apply (rule LetStepE, auto) 
      by (metis One_nat_def add_0 add_diff_cancel_left' capture_avoiding_sub_size_eq diff_add_zero exp.size(12) exp.size(19) zero_neq_one)
  next
    case (Ite e1 e2 e3)
    then show ?case 
      apply auto
      by (rule IfStepElseE, auto)
  next
    case (Extract x1a x2a e)
    then show ?case 
      apply auto
      apply (rule ExtractReduceE, auto)
      by (metis step_exp.Let step_exp_not_ext)
  next
    case (Concat e1 e2)
    then show ?case 
      apply auto
      unfolding append_exp_def[symmetric]
      by (rule ConcatRhsE, auto)
  qed simp_all
next
  case (IfStepCond \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 v\<^sub>3)
  show ?case 
    apply (rule notI)
    apply (rule IfStepCondE, auto)
    using IfStepCond by auto
next
  case (IfStepThen \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 v\<^sub>3)
  show ?case 
    apply (rule notI)
    apply (rule IfStepThenE, auto)
    using IfStepThen by auto
next
  case (IfStepElse \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2)
  show ?case 
    apply (rule notI)
    apply (rule IfStepElseE, auto)
    using IfStepElse by auto    
next
  case (BopRhs \<Delta> e\<^sub>2 e\<^sub>2' v bop)
  show ?case 
    apply (rule notI)
    apply (rule BopRhsE, auto)
    using BopRhs apply auto
    apply (meson false.not_binop' true.not_binop')
    apply (smt (verit) bv_eq_def false.not_binop lor_false lor_true(1) lor_true(2) lor_true(3) true.not_binop')
    apply (metis false.not_binop' true.not_binop')
    by (smt (verit, best) bv_eq_def exp.distinct(7) false.not_binop lor_false lor_true(1) lor_true(2) order_less_imp_not_eq true_exp_def word_not_sz_neqI)
next
  case (BopLhs \<Delta> e\<^sub>1 e\<^sub>1' bop e\<^sub>2)
  show ?case 
    apply (rule notI)
    apply (rule BopLhsE, auto)
    using BopLhs apply auto
    apply (meson false.not_binop' true.not_binop')
    apply (metis (full_types) bv_eq_def false.not_binop' lor_false lor_true(1) lor_true(2) lor_true(3) true.not_binop')
    apply (metis false.not_binop true.not_binop)
    by (metis (full_types) bv_eq_def false.not_binop' lor_false lor_true(1) lor_true(2) lor_true(3) true.not_binop')
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply auto
    unfolding bv_lor.simps bv_eq_def apply auto
    by (metis (full_types) lor_false lor_true(1) step_exp_not_false step_exp_not_true)
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply auto
    unfolding bv_lor.simps bv_eq_def apply auto
    by (metis (full_types) lor_false lor_true(1) step_exp_not_false step_exp_not_true)
next
  case (Uop \<Delta> e e' uop)
  show ?case 
    apply (rule notI)
    apply (rule UopE, simp_all)
    using Uop by simp_all    
next
  case (ConcatRhs \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1)
  show ?case 
    apply (rule notI)
    apply (rule ConcatRhsE, simp_all)
    using ConcatRhs by simp_all
next
  case (ConcatLhs \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2)
  show ?case 
    apply (rule notI)
    apply (rule ConcatLhsE, simp_all)
    using ConcatLhs by simp_all
next
  case (ExtractReduce \<Delta> e e' sz\<^sub>1 sz\<^sub>2)
  show ?case 
    apply (rule notI)
    apply (rule ExtractReduceE, simp_all)
    using ExtractReduce apply simp_all
    by (metis step_exp.ExtractReduce step_exp_not_ext)
next
  case (CastReduce \<Delta> e e' cast sz)
  show ?case 
    apply (rule notI)
    apply (rule CastReduceE, simp_all)
    using CastReduce apply simp_all
    using step_exp_not_ext
    by (metis step_exp.CastReduce step_exp_not_ext)+
qed (simp_all)
*)



interpretation capture_avoiding_var: exp_val_syntax \<open>\<lambda>e v. (\<And>nm t. [v\<sslash>(nm :\<^sub>t t)](nm :\<^sub>t t) = e)\<close>
  apply standard using capture_avoiding_var by meson

lemmas string_simps = 
  list.inject char.inject refl simp_thms False_not_True not_False_eq_True 
  capture_avoiding_var_name_neq

lemmas capture_avoiding_sub_simps = 
  plus.capture_avoiding_sub minus.capture_avoiding_sub times.capture_avoiding_sub 
  divide.capture_avoiding_sub mod.capture_avoiding_sub sdivide.capture_avoiding_sub
  smod.capture_avoiding_sub land.capture_avoiding_sub lor.capture_avoiding_sub 
  xor.capture_avoiding_sub lsl.capture_avoiding_sub lsr.capture_avoiding_sub 
  asr.capture_avoiding_sub capture_avoiding_var.word
  capture_avoid.word capture_avoid.unknown capture_avoid.storage capture_avoid.plus
  capture_avoid.minus capture_avoid.lsl capture_avoid.lsr capture_avoid.xor
  capture_avoiding_sub.simps
  string_simps

end
