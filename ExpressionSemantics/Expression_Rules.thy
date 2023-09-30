theory Expression_Rules
  imports Expression_Syntax
begin

inductive
  eval_exp' :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<Rrightarrow> _\<close> [400, 400, 400] 401)
where
  \<comment> \<open>Var rules\<close>
  VarIn: \<open>\<lbrakk>((name' :\<^sub>t t), val) \<in>\<^sub>\<Delta> \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> Val val\<close> |
  VarNotIn: \<open>\<lbrakk>((name' :\<^sub>t t)) \<notin> dom \<Delta>\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> unknown[str]: t\<close> |

  \<comment> \<open>Load\<close>
  LoadStepAddr: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'; e\<^sub>2 \<noteq> e\<^sub>2'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<Rrightarrow> (e\<^sub>1[e\<^sub>2', ed]:usz)\<close> |
  LoadStepMem: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'; e\<^sub>1 \<noteq> e\<^sub>1'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<Rrightarrow> (e\<^sub>1'[Val v\<^sub>2, ed]:usz)\<close> |
  LoadByte: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> Val v'\<close> | 
  LoadByteFromNext: \<open>\<lbrakk>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq> (num\<^sub>2 \<Colon> sz\<^sub>2)\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ((v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<Rrightarrow> ((Val v)[(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)\<close> |
  LoadUnMem: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<Rrightarrow> unknown[str]: imm\<langle>sz\<rangle>\<close> |
  LoadUnAddr: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<Rrightarrow> unknown[str]: imm\<langle>sz'\<rangle>\<close> |
  LoadWordBe: \<open>\<lbrakk>sz > sz\<^sub>m\<^sub>e\<^sub>m; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> (((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m) @ (((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))))\<close> |
  LoadWordEl: \<open>\<lbrakk>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; sz > sz\<^sub>m\<^sub>e\<^sub>m\<rbrakk> \<Longrightarrow> 
      \<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> ((((Val v)[succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m))) @ ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m))\<close> |

  \<comment> \<open>Store\<close>
  StoreStepVal: \<open>\<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3')\<close> |
  StoreStepAddr: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1 with [e\<^sub>2', en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreStepMem: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> (e\<^sub>1' with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3))\<close> |
  StoreWordBe: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast High sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), be]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast Low (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreWordEl: \<open>\<lbrakk>sz\<^sub>m\<^sub>e\<^sub>m < sz; type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle>; e\<^sub>1 = ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Cast Low sz\<^sub>m\<^sub>e\<^sub>m (Val val)))\<rbrakk> \<Longrightarrow>
    \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<Rrightarrow> (e\<^sub>1 with [(succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r)), el]:u(sz - sz\<^sub>m\<^sub>e\<^sub>m) \<leftarrow> (Cast High (sz - sz\<^sub>m\<^sub>e\<^sub>m) (Val val)))\<close> |
  StoreVal: \<open>type v = mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<Rrightarrow> (v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz\<^sub>m\<^sub>e\<^sub>m])\<close> |
  StoreUnAddr: \<open>type v = t \<Longrightarrow> \<Delta> \<turnstile> ((Val v) with [unknown[str]: t', ed]:usz \<leftarrow> (Val v')) \<Rrightarrow> (unknown[str]: t)\<close> |


  \<comment> \<open>Let rules\<close>
  LetStep: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<Rrightarrow> (Let var e\<^sub>1' e\<^sub>2)\<close> |
  Let: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<Rrightarrow> [v\<sslash>var]e\<close> |
  (* one missing rule *)

  \<comment> \<open>If rules\<close>
  IfStepCond: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> ite e\<^sub>1' (Val v\<^sub>2) (Val v\<^sub>3)\<close> |
  IfStepThen: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<Rrightarrow> ite e\<^sub>1 e\<^sub>2' (Val v\<^sub>3)\<close> |
  IfStepElse: \<open>\<Delta> \<turnstile> e\<^sub>3 \<Rrightarrow> e\<^sub>3'\<Longrightarrow> \<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Rrightarrow> ite e\<^sub>1 e\<^sub>2 e\<^sub>3'\<close> |
  IfTrue: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> (Val v\<^sub>2)\<close> |
  IfFalse: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> (Val v\<^sub>3)\<close> |
  IfUnknown: \<open>\<lbrakk>type v\<^sub>2 = t'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> unknown[str]: t'\<close> |

  \<comment> \<open>Binary operation rules\<close>
  BopRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<Rrightarrow> BinOp (Val v) bop e\<^sub>2'\<close> |
  BopLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<Rrightarrow> BinOp e\<^sub>1' bop e\<^sub>2\<close> |

  AopUnkRhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e \<Rrightarrow> unknown[str]: t\<close> |
  AopUnkLhs: \<open>\<Delta> \<turnstile> BinOp e (AOp aop) (unknown[str]: t) \<Rrightarrow> unknown[str]: t\<close> |

  LopUnkRhs: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp lop) e \<Rrightarrow> unknown[str]: imm\<langle>1\<rangle>\<close> |
  LopUnkLhs: \<open>\<Delta> \<turnstile> BinOp e (LOp lop) (unknown[str]: t) \<Rrightarrow> unknown[str]: imm\<langle>1\<rangle>\<close> |

  \<comment> \<open>Arithmetic rules\<close>
  Plus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Minus: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) -\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Times: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) *\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Div: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) div\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SDiv: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) div\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Mod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) %\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SMod: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) %\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsl: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <<\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Lsr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) >>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  Asr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) >>>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Logical rules\<close>
  LAnd: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) &\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) |\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  XOr: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) xor\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  (*these aren't really right*)
  EqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<Rrightarrow> true\<close> |
  EqDiff: \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> false\<close> |
  NeqSame: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<Rrightarrow> false\<close> |
  NeqDiff: \<open>((num\<^sub>1 \<Colon> sz\<^sub>1)::word) \<noteq>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz\<^sub>2) = true \<Longrightarrow> \<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1)) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2) \<Rrightarrow> true\<close> |
  Less: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  LessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLess: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) <\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |
  SignedLessEq: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz) \<le>\<^sub>s\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz))\<close> |

  \<comment> \<open>Unary op\<close>
  Uop: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (UnOp uop e) \<Rrightarrow> (UnOp uop e')\<close> |
  UopUnk: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<Rrightarrow> (unknown[str]: t)\<close> |
  Not: \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<Rrightarrow> (~\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |
  Neg: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<Rrightarrow> (-\<^sub>b\<^sub>v (num \<Colon> sz))\<close> |

  \<comment> \<open>Concat\<close>
  ConcatRhs: \<open>\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>2' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<Rrightarrow> (e\<^sub>1 @ e\<^sub>2')\<close> |
  ConcatLhs: \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>1' \<Longrightarrow> \<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<Rrightarrow> (e\<^sub>1' @ (Val v\<^sub>2))\<close> |
  ConcatRhsUn: \<open>type v = imm\<langle>sz\<^sub>1\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((Val v) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  ConcatLhsUn: \<open>type v = imm\<langle>sz\<^sub>2\<rangle> \<Longrightarrow> \<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<^sub>1 + sz\<^sub>2\<rangle>)\<close> |
  Concat: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> ((num\<^sub>1 \<Colon> sz\<^sub>1) \<cdot> (num\<^sub>2 \<Colon> sz\<^sub>2))\<close> |

  \<comment> \<open>Extract\<close>
  Extract: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<Rrightarrow> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>1 \<sim> lo : sz\<^sub>2)\<close> |
  ExtractReduce: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Rrightarrow> (extract:sz\<^sub>1:sz\<^sub>2[e'])\<close> |
  ExtractUn: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<Rrightarrow> (unknown[str]: imm\<langle>(sz\<^sub>1 - sz\<^sub>2) + 1\<rangle>)\<close> |

  \<comment> \<open>Cast\<close>
  CastReduce: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz e) \<Rrightarrow> (Cast cast sz e')\<close> |
  CastUnk: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> \<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<Rrightarrow> (unknown[str]: imm\<langle>sz\<rangle>)\<close> |
  CastLow: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastHigh: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz' - 1) \<sim> lo : (sz' - sz))\<close> |
  CastSigned: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close> |
  CastUnsigned: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<Rrightarrow> (ext (num \<Colon> sz') \<sim> hi : (sz - 1) \<sim> lo : 0)\<close>

inductive_cases VarE: \<open>\<Delta> \<turnstile> (name' :\<^sub>t t) \<Rrightarrow> e\<close>

inductive_cases LoadStepAddrE: \<open>\<Delta> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz \<Rrightarrow> e\<close>
inductive_cases LoadStepMemE: \<open>\<Delta> \<turnstile> e\<^sub>1[Val v\<^sub>2, ed]:usz \<Rrightarrow> e\<close>
inductive_cases LoadByteE: \<open>\<Delta> \<turnstile> v[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r) \<leftarrow> v', sz][(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz \<Rrightarrow> e\<close> 
inductive_cases LoadByteFromNextE: \<open>\<Delta> \<turnstile> ((v[(num\<^sub>1 \<Colon> sz\<^sub>1) \<leftarrow> v', sz][(num\<^sub>2 \<Colon> sz\<^sub>2), ed]:usz)::exp) \<Rrightarrow> e\<close>
inductive_cases LoadUnMemE: \<open>\<Delta> \<turnstile> (unknown[str]: t)[Val v, ed]:usz \<Rrightarrow> e\<close> 
inductive_cases LoadUnAddrE: \<open>\<Delta> \<turnstile> v[w \<leftarrow> v', sz][unknown[str]: t, ed]:usz' \<Rrightarrow> e\<close> 
inductive_cases LoadWordBeE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz) \<Rrightarrow> e\<close>
inductive_cases LoadWordElE: \<open>\<Delta> \<turnstile> ((Val v)[(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz) \<Rrightarrow> e\<close>

inductive_cases StoreStepValE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> e\<^sub>3) \<Rrightarrow> e\<close>
inductive_cases StoreStepAddrE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [e\<^sub>2, en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases StoreStepMemE: \<open>\<Delta> \<turnstile> (e\<^sub>1 with [(Val v\<^sub>2), en]:usz \<leftarrow> (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases StoreWordBeE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), be]:usz \<leftarrow> (Val val)) \<Rrightarrow> e\<close>
inductive_cases StoreWordElE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), el]:usz \<leftarrow> (Val val)) \<Rrightarrow> e\<close>
inductive_cases StoreValE: \<open>\<Delta> \<turnstile> ((Val v) with [(num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r), ed]:usz\<^sub>m\<^sub>e\<^sub>m \<leftarrow> (Val v')) \<Rrightarrow> e\<close>
inductive_cases StoreUnAddrE: \<open>\<Delta> \<turnstile> ((Val v) with [unknown[str]: t', ed]:usz' \<leftarrow> (Val v')) \<Rrightarrow> e\<close>

inductive_cases LetStepE: \<open>\<Delta> \<turnstile> (Let var e\<^sub>1 e\<^sub>2) \<Rrightarrow> e\<close>
inductive_cases LetE: \<open>\<Delta> \<turnstile> (Let var (Val v) e) \<Rrightarrow> e'\<close>

inductive_cases IfStepCondE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfStepThenE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfStepElseE: \<open>\<Delta> \<turnstile> (ite e\<^sub>1 e\<^sub>2 e\<^sub>3) \<Rrightarrow> e\<close>
inductive_cases IfTrueE: \<open>\<Delta> \<turnstile> (ite true (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfFalseE: \<open>\<Delta> \<turnstile> (ite false (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>
inductive_cases IfUnknownE: \<open>\<Delta> \<turnstile> (ite unknown[str]: t (Val v\<^sub>2) (Val v\<^sub>3)) \<Rrightarrow> e\<close>

inductive_cases BopRhsE: \<open>\<Delta> \<turnstile> BinOp (Val v) bop e\<^sub>2 \<Rrightarrow> e\<close>
inductive_cases BopLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 bop e\<^sub>2 \<Rrightarrow> e\<close>

inductive_cases AopUnkRhsE: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (AOp aop) e\<^sub>2 \<Rrightarrow> e\<close>
inductive_cases AopUnkLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (AOp aop) unknown[str]: t \<Rrightarrow> e\<close>

inductive_cases LopUnkRhsE: \<open>\<Delta> \<turnstile> BinOp (unknown[str]: t) (LOp aop) e\<^sub>2 \<Rrightarrow> e\<close>
inductive_cases LopUnkLhsE: \<open>\<Delta> \<turnstile> BinOp e\<^sub>1 (LOp aop) unknown[str]: t \<Rrightarrow> e\<close>

inductive_cases PlusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) + (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases MinusE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) - (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases TimesE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) * (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases DivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) div (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SDivE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sdiv (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases ModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) % (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SModE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) smod (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LslE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) << (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases AsrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) >>> (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LAndE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) && (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) || (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases XOrE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) xor (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases EqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Eq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases EqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1) (LOp Eq) (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close>
inductive_cases NeqSameE: \<open>\<Delta> \<turnstile> (BinOp (num \<Colon> sz) (LOp Neq) (num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases NeqDiffE: \<open>\<Delta> \<turnstile> (BinOp (num\<^sub>1 \<Colon> sz\<^sub>1)) (LOp Neq) (num\<^sub>2 \<Colon> sz\<^sub>2) \<Rrightarrow> e\<close>
inductive_cases LessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) lt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases LessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) le (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SignedLessE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) slt (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases SignedLessEqE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) sle (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e\<close>

inductive_cases UopE: \<open>\<Delta> \<turnstile> (UnOp uop e) \<Rrightarrow> e'\<close>
inductive_cases UopUnkE: \<open>\<Delta> \<turnstile> (UnOp uop (unknown[str]: t)) \<Rrightarrow> e\<close>
inductive_cases NotE: \<open>\<Delta> \<turnstile> (~(num \<Colon> sz)) \<Rrightarrow> e\<close>
inductive_cases NegE: \<open>\<Delta> \<turnstile> (UnOp Neg (num \<Colon> sz)) \<Rrightarrow> e\<close>

inductive_cases ConcatRhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 @ e\<^sub>2) \<Rrightarrow> e\<close>
inductive_cases ConcatLhsE: \<open>\<Delta> \<turnstile> (e\<^sub>1 @ (Val v\<^sub>2)) \<Rrightarrow> e\<close>
inductive_cases ConcatRhsUnE: \<open>\<Delta> \<turnstile> ((Val v) @ (unknown[str]: imm\<langle>sz\<^sub>2\<rangle>)) \<Rrightarrow> e\<close>
inductive_cases ConcatLhsUnE: \<open>\<Delta> \<turnstile> ((unknown[str]: imm\<langle>sz\<^sub>1\<rangle>) @ (Val v)) \<Rrightarrow> e\<close>
inductive_cases ConcatE: \<open>\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz\<^sub>1) @ (num\<^sub>2 \<Colon> sz\<^sub>2)) \<Rrightarrow> e\<close>

inductive_cases ExtractE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[(num \<Colon> sz)]) \<Rrightarrow> e\<close>
inductive_cases ExtractReduceE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[e]) \<Rrightarrow> e'\<close>
inductive_cases ExtractUnE: \<open>\<Delta> \<turnstile> (extract:sz\<^sub>1:sz\<^sub>2[unknown[str]: t]) \<Rrightarrow> e\<close>

inductive_cases CastReduceE: \<open>\<Delta> \<turnstile> (Cast cast sz e) \<Rrightarrow> e'\<close>
inductive_cases CastUnkE: \<open>\<Delta> \<turnstile> (Cast cast sz (unknown[str]: t)) \<Rrightarrow> e\<close>
inductive_cases CastLowE: \<open>\<Delta> \<turnstile> (low:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastHighE: \<open>\<Delta> \<turnstile> (high:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastSignedE: \<open>\<Delta> \<turnstile> (extend:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>
inductive_cases CastUnsignedE: \<open>\<Delta> \<turnstile> (pad:sz[(num \<Colon> sz')]) \<Rrightarrow> e\<close>

lemma Val_not_inject: "v \<noteq> v' \<Longrightarrow> Val v \<noteq> Val v'"
  by simp

lemma step_exp_neq': \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> e \<noteq> e'\<close>
proof (induct rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  then show ?case 
    using var.not_val by blast
next
  case (VarNotIn name' t \<Delta> str)
  then show ?case by simp
next
  case (Plus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding plus_exp.simps bv_plus.simps by simp
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by simp
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by simp
next
  case (Extract sz\<^sub>2 sz\<^sub>1 \<Delta> num sz)
  then show ?case
    unfolding xtract.simps by simp
next
  case (CastLow \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastHigh \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastSigned \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (CastUnsigned \<Delta> sz num sz')
  then show ?case 
    unfolding xtract.simps by simp
next
  case (Let \<Delta> var v e)
  then show ?case 
    by (rule let_neq_capture_avoid_v)
qed simp_all

lemma step_exp_neq: \<open>\<not>(\<Delta> \<turnstile> e \<Rrightarrow> e)\<close>
  using step_exp_neq' by auto

lemma eval_exp'_val_no_step_intermediary: \<open>\<Delta> \<turnstile> e \<Rrightarrow> e' \<Longrightarrow> e \<noteq> (Val v)\<close>
  by (induct rule: eval_exp'.induct, unfold plus_exp.simps, simp_all)


lemma step_exp_not_val[simp]: \<open>\<not>(\<Delta> \<turnstile> (Val v) \<Rrightarrow> e)\<close>
  using eval_exp'_val_no_step_intermediary by blast

lemma step_exp_not_word[simp]: \<open>\<not>(\<Delta> \<turnstile> (num \<Colon> sz) \<Rrightarrow> e)\<close>
  unfolding word_constructor_exp_def by (rule step_exp_not_val)

lemma step_exp_not_plus[simp]: \<open>\<not>(\<Delta> \<turnstile> ((num\<^sub>1 \<Colon> sz) +\<^sub>b\<^sub>v (num\<^sub>2 \<Colon> sz)) \<Rrightarrow> e)\<close>
  unfolding bv_plus.simps by (rule step_exp_not_word)

lemma step_exp_not_ext[simp]: \<open>\<not>(\<Delta> \<turnstile> (ext num \<Colon> sz \<sim> hi : szh \<sim> lo : szl) \<Rrightarrow> e)\<close>
  unfolding xtract.simps by (rule step_exp_not_word)

lemma step_exp_not_unknown[simp]: \<open>\<not>(\<Delta> \<turnstile> (unknown[str]: t) \<Rrightarrow> e)\<close>
  unfolding unknown_constructor_exp_def by (rule step_exp_not_val)

lemma step_exp_not_true[simp]: \<open>\<not>(\<Delta> \<turnstile> true \<Rrightarrow> e)\<close>
  unfolding true_exp_def by (rule step_exp_not_val)

lemma step_exp_not_false[simp]: \<open>\<not>(\<Delta> \<turnstile> false \<Rrightarrow> e)\<close>
  unfolding false_exp_def by (rule step_exp_not_val)

lemma step_exp_not_storage[simp]: \<open>\<not>(\<Delta> \<turnstile> v[w \<leftarrow> v', sz] \<Rrightarrow> e')\<close>
  unfolding storage_constructor_exp_def by (rule step_exp_not_val)


text \<open>We describe a well formed delta as one which\<close>
(*
definition
  wf\<Delta> :: \<open>variables \<Rightarrow> bool\<close>
where
  \<open>wf\<Delta> \<Delta> = (\<forall>var \<in> dom \<Delta>. var_type var = type (the (\<Delta> var)))\<close>


function 
  no_stored_unknowns :: \<open>val \<Rightarrow> bool\<close>
where
  \<open>no_stored_unknowns (v[_ \<leftarrow> v', _]) = ((\<forall>str t. v' \<noteq> unknown[str]: t) \<and> no_stored_unknowns v)\<close> |
  \<open>\<lbrakk>\<forall>v' w v'' sz. v \<noteq> (v'[w \<leftarrow> v'', sz])\<rbrakk> \<Longrightarrow> no_stored_unknowns v = True\<close>
  subgoal for P v
    by (cases \<open>\<forall>v' w v'' sz. v \<noteq> (v'[w \<leftarrow> v'', sz])\<close>, auto)
  by auto 
termination
  apply standard
  apply (relation \<open>(\<lambda>p. size_class.size p) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  unfolding storage_constructor_val_def
  by (rule mlex_less, force)+

function
  no_unknowns :: \<open>variables \<Rightarrow> exp \<Rightarrow> bool\<close>
where
  \<open>no_unknowns _ (unknown[_]: _) = False\<close> |
  \<open>no_unknowns _ (_ \<Colon> _) = True\<close> |
  \<open>no_unknowns _ (v[w \<leftarrow> v', sz]) = no_stored_unknowns (v[w \<leftarrow> v', sz])\<close> |
  \<open>no_unknowns \<Delta> (name' :\<^sub>t t) = ((name' :\<^sub>t t) \<in> dom \<Delta> \<and> (\<forall>str t. the (\<Delta> (name' :\<^sub>t t)) \<noteq> unknown[str]: t))\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1[e\<^sub>2, _]:u_) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1 with [e\<^sub>2, _]:u_ \<leftarrow> e\<^sub>3) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2 \<and> no_unknowns \<Delta> e\<^sub>3)\<close> |
  \<open>no_unknowns \<Delta> (BinOp e\<^sub>1 _ e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (UnOp _ e) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (Cast _ _ e) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (Let _ e\<^sub>1 e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close> |
  \<open>no_unknowns \<Delta> (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2 \<and> no_unknowns \<Delta> e\<^sub>3)\<close> |
  \<open>no_unknowns \<Delta> (extract:_:_[e]) = (no_unknowns \<Delta> e)\<close> |
  \<open>no_unknowns \<Delta> (e\<^sub>1 @ e\<^sub>2) = (no_unknowns \<Delta> e\<^sub>1 \<and> no_unknowns \<Delta> e\<^sub>2)\<close>
  subgoal for P x
    apply (cases x, simp)
    subgoal for \<Delta> e
      by (cases e rule: exp_exhaust, auto)
    .
  apply auto
  apply (metis var_not_unknown_neq)
  apply (metis concat_not_unknown_neq)
  apply (metis var_not_word_neq)
  apply (metis var_not_word_neq)
  apply (metis concat_not_word_neq)
  apply (metis concat_not_word_neq)
  apply (metis var_not_storage_neq)+
  apply (metis concat_not_storage_neq)+
  done
termination 
  apply standard
  apply (relation \<open>(\<lambda>p. size_class.size (snd p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  unfolding append_exp_def
  by (rule mlex_less, force)+

lemma no_unknowns_ext[simp]: \<open>no_unknowns \<Delta> (ext (num \<Colon> sz) \<sim> hi : sz\<^sub>h\<^sub>i \<sim> lo : sz\<^sub>l\<^sub>o\<^sub>w)\<close>
  unfolding xtract.simps by simp

lemma no_unknowns_succ[simp]: \<open>no_unknowns \<Delta> (succ (num \<Colon> sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r))\<close>
  unfolding succ.simps by simp

lemma no_unknowns_true[simp]: \<open>no_unknowns \<Delta> true\<close>
  by (simp add: true_word)

lemma no_unknowns_false[simp]: \<open>no_unknowns \<Delta> false\<close>
  by (simp add: false_word)


lemma typing_exp_det: fixes e :: exp shows \<open>\<Gamma> \<turnstile> e :: t \<Longrightarrow> \<Gamma> \<turnstile> e :: t' \<Longrightarrow> t = t'\<close>
  apply (induct e)



lemma 
  assumes \<open>\<Gamma> \<turnstile> e\<^sub>1[e\<^sub>2, ed]:usz :: t\<close>
    shows \<open> t = imm\<langle>sz\<rangle> \<Longrightarrow> 0 < sz \<Longrightarrow> sz\<^sub>m\<^sub>e\<^sub>m dvd sz \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>1 :: mem\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r, sz\<^sub>m\<^sub>e\<^sub>m\<rangle> \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>2 :: imm\<langle>sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r\<rangle> \<Longrightarrow> Q\<close>
  using assms apply (rule typed_ok_exp.elims, auto)


lemma step_exp_no_unknowns:
  assumes \<open>\<Delta> \<turnstile> e \<Rrightarrow> e'\<close> and \<open>\<Gamma> \<turnstile> e :: t\<close>
      and \<open>wf\<Delta> \<Delta>\<close> and \<open>no_unknowns \<Delta> e\<close>
    shows \<open>no_unknowns \<Delta> e'\<close>
using assms proof (induction rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  then show ?case 
(*    apply auto
    apply (rule no_unknowns_Val)
    apply auto
    subgoal for y str t'
      apply (erule allE[of _ str], erule allE[of _ t])
      unfolding val_var_in_vars.simps wf\<Delta>_def 
      by (metis val_syntax_class.type_unknownI var.sel(2) var_constructor_var_def)
    .*)
    sorry
next
  case (LoadByte \<Delta> v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz ed)
  then show ?case 
    apply (cases v' rule: val_exhaust)
    apply auto
    unfolding no_unknowns.simps(2) Val_simp_storage Val_simp_word apply simp_all
    using   apply auto[1]
    sorry
next
  case (LoadByteFromNext num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  then show ?case 
    apply auto
    sorry
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_eq_def by auto
next
  case (SignedLess \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_le.simps bv_land.simps bv_eq_def by auto
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    unfolding bv_le.simps bv_land.simps bv_eq_def by auto
qed (unfold no_unknowns.simps, simp_all)


lemma eval_exp'_deterministic:
  assumes \<open>\<Delta> \<turnstile> e \<Rrightarrow> e\<^sub>1\<close> and \<open>\<Delta> \<turnstile> e \<Rrightarrow> e\<^sub>2\<close>
    shows \<open>e\<^sub>1 = e\<^sub>2\<close>
using assms proof (induction arbitrary: e\<^sub>2 rule: eval_exp'.induct)
  case (VarIn name' t val \<Delta>)
  show ?case 
    using VarIn(2) apply (rule VarE, simp_all)
    using VarIn.hyps apply (rule var_in_deterministic, blast)
    using VarIn.hyps val_var_in_vars.simps by blast
next
  case (VarNotIn name' t \<Delta> str)
  show ?case 
    using VarNotIn(2) apply (rule VarE, simp_all)
    using VarNotIn.hyps apply (simp add: val_var_in_vars.simps)
    subgoal sorry
    .
next
  case (LoadStepAddr \<Delta> e\<^sub>2' e\<^sub>2'' e\<^sub>1 ed sz)
  show ?case 
    using LoadStepAddr(4) apply (rule LoadStepAddrE)
    using LoadStepAddr.hyps apply auto
    by (rule LoadStepAddr.IH)
next
  case (LoadStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 ed sz)
  show ?case 
    using LoadStepMem(4) apply (rule LoadStepMemE)
    using LoadStepMem.hyps apply auto
    by (rule LoadStepMem.IH)
next
  case (LoadByte \<Delta> v num sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r v' sz ed)
  then show ?case 
    apply (rule LoadByteE, auto)
    apply (simp_all add: storage_constructor_exp_def)
    by fastforce+
next
  case (LoadByteFromNext num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2 \<Delta> v v' sz ed)
  show ?case 
    using LoadByteFromNext(2) apply (rule LoadByteFromNextE)
    using LoadByteFromNext.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    by fastforce+
next
  case (LoadUnMem \<Delta> str t v ed sz)
  then show ?case 
    apply (rule LoadUnMemE)
    apply auto
    sorry
next
  case (LoadUnAddr \<Delta> v w v' sz str t ed sz')
  then show ?case 
    apply (rule LoadUnAddrE)
    by auto
next
  case (LoadWordBe sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    using LoadWordBe(3) apply (rule LoadWordBeE)
    using LoadWordBe.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    sorry
next
  case (LoadWordEl sz sz\<^sub>m\<^sub>e\<^sub>m v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r \<Delta> num)
  show ?case 
    using LoadWordEl(3) apply (rule LoadWordElE)
    using LoadWordEl.hyps apply auto
    apply (simp_all add: storage_constructor_exp_def)
    sorry
next
  case (StoreStepVal \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2 en sz)
  show ?case 
    using StoreStepVal(3) apply (rule StoreStepValE)
    using StoreStepVal.hyps apply auto
    by (rule StoreStepVal.IH) 
next
  case (StoreStepAddr \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 en sz v\<^sub>3)
  show ?case 
    using StoreStepAddr(3) apply (rule StoreStepAddrE)
    using StoreStepAddr.hyps apply auto
    by (rule StoreStepAddr.IH) 
next
  case (StoreStepMem \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 en sz v\<^sub>3)
  show ?case 
    using StoreStepMem(3) apply (rule StoreStepMemE)
    using StoreStepMem.hyps apply auto
    by (rule StoreStepMem.IH) 
next
  case (StoreWordBe sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    using StoreWordBe(4) apply (rule StoreWordBeE)
    using StoreWordBe.hyps by auto
next
  case (StoreWordEl sz\<^sub>m\<^sub>e\<^sub>m sz v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r e\<^sub>1 num val \<Delta>)
  show ?case 
    using StoreWordEl(4) apply (rule StoreWordElE)
    using StoreWordEl.hyps by auto
next
  case (StoreVal v sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r sz\<^sub>m\<^sub>e\<^sub>m \<Delta> num ed v')
  show ?case 
    using StoreVal(2) apply (rule StoreValE)
    using StoreVal.hyps by auto
next
  case (StoreUnAddr v t \<Delta> str sz\<^sub>a\<^sub>d\<^sub>d\<^sub>r ed sz' v')
  show ?case 
    using StoreUnAddr(2) apply (rule StoreUnAddrE)
    using StoreUnAddr.hyps by auto
next
  case (LetStep \<Delta> e\<^sub>1 e\<^sub>1' var e\<^sub>2)
  show ?case 
    using LetStep(3) apply (rule LetStepE)
    using LetStep.hyps apply auto
    by (rule LetStep.IH) 
next
  case (IfStepCond \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2 v\<^sub>3)
  show ?case 
    using IfStepCond(3) apply (rule IfStepCondE)
    using IfStepCond.hyps apply auto
    by (rule IfStepCond.IH) 
next
  case (IfStepThen \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1 v\<^sub>3)
  show ?case 
    using IfStepThen(3) apply (rule IfStepThenE)
    using IfStepThen.hyps apply auto
    by (rule IfStepThen.IH) 
next
  case (IfStepElse \<Delta> e\<^sub>3 e\<^sub>3' e\<^sub>1 e\<^sub>2)
  show ?case 
    using IfStepElse(3) apply (rule IfStepElseE)
    using IfStepElse.hyps apply auto
    by (rule IfStepElse.IH) 
next
  case (IfTrue \<Delta> v\<^sub>2 v\<^sub>3)
  then show ?case
    apply (rule IfTrueE)
    apply auto
    using unknown_not_true by metis    
next
  case (IfFalse \<Delta> v\<^sub>2 v\<^sub>3)
  then show ?case 
    apply (rule IfFalseE)
    apply auto
    using unknown_not_false by metis
next
  case (IfUnknown v\<^sub>2 t' \<Delta> str t v\<^sub>3)
  show ?case 
    using IfUnknown(2) apply (rule IfUnknownE)
    using IfUnknown.hyps by auto
next
  case (BopRhs \<Delta> e\<^sub>2' e\<^sub>2'' v bop)
  show ?case 
    using BopRhs(3) apply (rule BopRhsE)
    using BopRhs.hyps apply auto
    apply (rule BopRhs.IH, blast)
    sorry
next
  case (BopLhs \<Delta> e\<^sub>1 e\<^sub>1' bop e\<^sub>2')
  show ?case 
    using BopLhs(3) apply (rule BopLhsE)
    using BopLhs.hyps apply auto
    apply (rule BopLhs.IH, blast)
    sorry
next
  case (AopUnkRhs \<Delta> str t aop e)
  then show ?case sorry
next
  case (AopUnkLhs \<Delta> e aop str t)
  then show ?case sorry
next
  case (LopUnkRhs \<Delta> str t lop e)
  then show ?case sorry
next
  case (LopUnkLhs \<Delta> e lop str t)
  then show ?case sorry
next
  case (Plus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule PlusE)
    by auto
next
  case (Minus \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule MinusE)
    by auto
next
  case (Times \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule TimesE)
    by auto
next
  case (Div \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule DivE)
    by auto
next
  case (SDiv \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SDivE)
    by auto
next
  case (Mod \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule ModE)
    by auto
next
  case (SMod \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SModE)
    by auto    
next
  case (Lsl \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LslE)
    by auto
next
  case (Lsr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LsrE)
    by auto
next
  case (Asr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule AsrE)
    by auto
next
  case (LAnd \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LAndE)
    by auto
next
  case (LOr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case
    apply (rule LOrE)
    by auto
next
  case (XOr \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule XOrE)
    by auto
next
  case (EqSame \<Delta> num sz)
  then show ?case 
    apply (rule EqSameE)
    apply auto    
    by (simp add: bv_eq_def)
next
  case (EqDiff num\<^sub>1 sz num\<^sub>2 \<Delta>)
  show ?case 
    using EqDiff(2) apply (rule EqDiffE)
    apply auto
    by (metis EqDiff.hyps bv_eq_def bv_negation_true_false true_neq_false_word)
next
  case (NeqSame \<Delta> num sz)
  then show ?case 
    apply (rule NeqSameE)
    apply auto
    by (simp add: bv_eq_def)
next
  case (NeqDiff num\<^sub>1 sz num\<^sub>2 \<Delta>)
  show ?case 
    using NeqDiff(2) apply (rule NeqDiffE)
    apply auto
    by (metis NeqDiff.hyps bv_eq_def bv_negation_true_false true_neq_false_word)
next
  case (Less \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LessE)
    by auto
next
  case (LessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule LessEqE)
    by auto
next
  case (SignedLess \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SignedLessE)
    by auto
next
  case (SignedLessEq \<Delta> num\<^sub>1 sz num\<^sub>2)
  then show ?case 
    apply (rule SignedLessEqE)
    by auto
next
  case (Uop \<Delta> e e' uop)
  show ?case
    using Uop(3) apply (rule UopE)
    using Uop.hyps apply auto
    by (rule Uop.IH) 
next
  case (UopUnk \<Delta> uop str t)
  then show ?case 
    apply (rule UopUnkE)
    by auto    
next
  case (Not \<Delta> num sz)
  then show ?case
    apply (rule NotE)
    by auto
next
  case (Neg \<Delta> num sz)
  then show ?case 
    apply (rule NegE)
    by auto
next
  case (ConcatRhs \<Delta> e\<^sub>2 e\<^sub>2' e\<^sub>1)
  show ?case 
    using ConcatRhs(3) apply (rule ConcatRhsE)
    using ConcatRhs.hyps apply auto
    apply (metis var_not_concat)
    apply (metis var_not_concat)
    by (rule ConcatRhs.IH)
next
  case (ConcatLhs \<Delta> e\<^sub>1 e\<^sub>1' v\<^sub>2)
  show ?case 
    using ConcatLhs(3) apply (rule ConcatLhsE)
    using ConcatLhs.hyps apply auto
    apply (metis var_not_concat)
    apply (metis var_not_concat)
    by (rule ConcatLhs.IH)
next
  case (ConcatRhsUn v sz\<^sub>1 \<Delta> str sz\<^sub>2)
  show ?case 
    using ConcatRhsUn(2) apply (rule ConcatRhsUnE)
    using ConcatRhsUn.hyps apply auto
    apply (metis var_not_concat)+
    defer
    using unknown_constructor_exp_def apply fastforce
    sorry
next
  case (ConcatLhsUn v sz\<^sub>2 \<Delta> str sz\<^sub>1)
  show ?case 
    using ConcatLhsUn(2) apply (rule ConcatLhsUnE)
    using ConcatLhsUn.hyps apply auto
    apply (metis var_not_concat)+
    defer
    using unknown_constructor_exp_def apply fastforce
    sorry    
next
  case (Concat \<Delta> num\<^sub>1 sz\<^sub>1 num\<^sub>2 sz\<^sub>2)
  then show ?case 
    apply (rule ConcatE)
    apply auto
    apply (metis var_not_concat)
    by (metis var_not_concat)
next
  case (Extract sz\<^sub>2 sz\<^sub>1 \<Delta> num sz)
  show ?case 
    using Extract(2) apply (rule ExtractE)
    using Extract.hyps by auto
next
  case (ExtractReduce \<Delta> e e' sz\<^sub>1 sz\<^sub>2)
  show ?case 
    using ExtractReduce(3) apply (rule ExtractReduceE)
    using ExtractReduce.hyps apply auto
    by (rule ExtractReduce.IH)
next
  case (ExtractUn \<Delta> sz\<^sub>1 sz\<^sub>2 str t)
  then show ?case 
    apply (rule ExtractUnE)
    by auto
next
  case (CastReduce \<Delta> e e' cast sz)
  show ?case 
    using CastReduce(3) apply (rule CastReduceE)
    using CastReduce.hyps apply auto
    by (rule CastReduce.IH)
next
  case (CastUnk \<Delta> e e' cast sz str t)
  show ?case 
    using CastUnk(3) apply (rule CastUnkE)
    using CastUnk.hyps
    by auto
next
  case (CastLow \<Delta> sz num sz')
  then show ?case
    apply (rule CastLowE)
    by auto
next
  case (CastHigh \<Delta> sz num sz')
  then show ?case 
    apply (rule CastHighE)
    by auto
next
  case (CastSigned \<Delta> sz num sz')
  then show ?case 
    apply (rule CastSignedE)
    by auto
next
  case (CastUnsigned \<Delta> sz num sz')
  then show ?case 
    apply (rule CastUnsignedE)
    by auto
qed
*)


lemma [simp]: \<open>Cast cast sz e  \<noteq> ext num \<Colon> sz \<sim> hi : szhi \<sim> lo : szlow\<close>
  unfolding xtract.simps by simp


lemma step_exp_non_circular:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2\<close> 
    shows \<open>\<not>(\<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow> e\<^sub>1)\<close>
using assms proof (induct rule: eval_exp'.induct)
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
      by (metis eval_exp'.Let step_exp_not_ext)+
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
      by (metis eval_exp'.Let step_exp_not_ext)
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
    by (metis eval_exp'.ExtractReduce step_exp_not_ext)
next
  case (CastReduce \<Delta> e e' cast sz)
  show ?case 
    apply (rule notI)
    apply (rule CastReduceE, simp_all)
    using CastReduce apply simp_all
    using step_exp_not_ext
    by (metis eval_exp'.CastReduce step_exp_not_ext)+
qed (simp_all)


declare bv_plus.simps[simp del]

inductive
  step_exps' :: \<open>variables \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ \<Rrightarrow>* _\<close> [400, 400, 400] 401)
where
  Reduce: \<open>\<lbrakk>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow>* e\<^sub>3\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow>* e\<^sub>3\<close> |
  Refl: \<open>\<Delta> \<turnstile> e \<Rrightarrow>* e\<close>

inductive_cases ReduceE: \<open>\<Delta> \<turnstile> e \<Rrightarrow>* e'\<close>

lemma step_exps_induct[consumes 1, case_names Reduce Refl]:
  "\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow>* e\<^sub>3 \<Longrightarrow> (\<And>e\<^sub>1 e\<^sub>2. \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow>* e\<^sub>3 \<Longrightarrow> P e\<^sub>2 \<Longrightarrow> P e\<^sub>1) \<Longrightarrow> P e\<^sub>3 \<Longrightarrow> P e\<^sub>1"
  by (induct \<Delta> e\<^sub>1 e\<^sub>3 rule: step_exps'.induct, blast+)

text \<open>Better reduce rule that includes the assumption e3 \<noteq> e1\<close>

lemma step_reduceE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow>* e\<^sub>3\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
      and reflE: \<open>e\<^sub>3 = e\<^sub>1 \<Longrightarrow> P\<close>
    shows P
proof (cases \<open>e\<^sub>3 = e\<^sub>1\<close>)
  case True
  then show ?thesis by (rule reflE)
next
  case False
  show ?thesis 
    using assms(1) apply (rule ReduceE)
    subgoal for e\<^sub>2
      using False by (intro reduceE[of e\<^sub>2] conjI)
    using False by (elim notE)
qed

lemma step_reduce_strictE:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow>* e\<^sub>3\<close> and \<open>e\<^sub>3 \<noteq> e\<^sub>1\<close>
      and reduceE: \<open>\<And>e\<^sub>2. \<lbrakk>e\<^sub>3 \<noteq> e\<^sub>1; \<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2; \<Delta> \<turnstile> e\<^sub>2 \<Rrightarrow>* e\<^sub>3\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) apply (rule step_reduceE)
  subgoal for e\<^sub>2
    using assms(2) by (intro reduceE[of e\<^sub>2] conjI)
  using assms(2) by (elim notE)



lemma step_exps_reduce_singleI:
  assumes \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow> e\<^sub>2\<close>
    shows \<open>\<Delta> \<turnstile> e\<^sub>1 \<Rrightarrow>* e\<^sub>2\<close>
  using assms apply (rule Reduce[of _ _ e\<^sub>2])
  by (rule Refl)




lemma 
  assumes "\<Delta> \<turnstile> (((Val v)[succ (num \<Colon> sz), el]:u56) @ ((Val v)[num \<Colon> sz, el]:u8)) \<Rrightarrow>* (num \<Colon> 64)"
      and "type v = mem\<langle>sz, 8\<rangle>"
    shows "\<Delta> \<turnstile> (Val v)[(num \<Colon> sz), el]:u64 \<Rrightarrow>* (num \<Colon> 64)"
  apply (rule Reduce)
  using assms(2) apply (rule LoadWordEl, linarith)
  apply simp
  using assms(1) by blast





end