theory BIR_x86
  imports BIR_Variables
begin

text \<open>BIR variables are passed down from LLVM IR see here: https://dse.in.tum.de/wp-content/uploads/2022/01/translating_x86_binaries_into_llvm_intermediate_representation.pdf\<close>

consts register_id :: \<open>nat \<Rightarrow> (string \<times> nat)\<close>

context var_syntax
begin

abbreviation
  mem :: 'a
where
  \<open>mem \<equiv> (''mem'' :\<^sub>t mem\<langle>addr_size, 8\<rangle>)\<close>

text \<open>Definition of named (purpose) registers\<close>

abbreviation
  RAX :: 'a
where
  \<open>RAX \<equiv> (''rax'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RBX :: 'a
where
  \<open>RBX \<equiv> (''rbx'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RCX :: 'a
where
  \<open>RCX \<equiv> (''rcx'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RDX :: 'a
where
  \<open>RDX \<equiv> (''rdx'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RSP :: 'a
where
  \<open>RSP \<equiv> (''rsp'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RBP :: 'a
where
  \<open>RBP \<equiv> (''rbp'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RDI :: 'a
where
  \<open>RDI \<equiv> (''rdi'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RSI :: 'a
where
  \<open>RSI \<equiv> (''rsi'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>Definition of unnamed (general purpose) registers\<close>

abbreviation
  R8 :: 'a
where
  \<open>R8 \<equiv> (''r8'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R9 :: 'a
where
  \<open>R9 \<equiv> (''r9'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R10 :: 'a
where
  \<open>R10 \<equiv> (''r10'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R11 :: 'a
where
  \<open>R11 \<equiv> (''r11'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R12 :: 'a
where
  \<open>R12 \<equiv> (''r12'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R13 :: 'a
where
  \<open>R13 \<equiv> (''r13'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R14 :: 'a
where
  \<open>R14 \<equiv> (''r14'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R15 :: 'a
where
  \<open>R15 \<equiv> (''r15'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>Definition of 128bit XMM registers\<close>

abbreviation
  XMM0 :: 'a
where
  \<open>XMM0 \<equiv> (''xmm0'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM1 :: 'a
where
  \<open>XMM1 \<equiv> (''xmm1'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM2 :: 'a
where
  \<open>XMM2 \<equiv> (''xmm2'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM3 :: 'a
where
  \<open>XMM3 \<equiv> (''xmm3'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM4 :: 'a
where
  \<open>XMM4 \<equiv> (''xmm4'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM5 :: 'a
where
  \<open>XMM5 \<equiv> (''xmm5'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM6 :: 'a
where
  \<open>XMM6 \<equiv> (''xmm6'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

abbreviation
  XMM7 :: 'a
where
  \<open>XMM7 \<equiv> (''xmm7'' :\<^sub>t imm\<langle>128\<rangle>)\<close>

text \<open>Definition of 256bit YMM registers\<close>

abbreviation
  YMM0 :: 'a
where
  \<open>YMM0 \<equiv> (''ymm0'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM1 :: 'a
where
  \<open>YMM1 \<equiv> (''ymm1'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM2 :: 'a
where
  \<open>YMM2 \<equiv> (''ymm2'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM3 :: 'a
where
  \<open>YMM3 \<equiv> (''ymm3'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM4 :: 'a
where
  \<open>YMM4 \<equiv> (''ymm4'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM5 :: 'a
where
  \<open>YMM5 \<equiv> (''ymm5'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM6 :: 'a
where
  \<open>YMM6 \<equiv> (''ymm6'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

abbreviation
  YMM7 :: 'a
where
  \<open>YMM7 \<equiv> (''ymm7'' :\<^sub>t imm\<langle>256\<rangle>)\<close>

text \<open>Definition of 512bit ZMM registers\<close>

abbreviation
  ZMM0 :: 'a
where
  \<open>ZMM0 \<equiv> (''zmm0'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM1 :: 'a
where
  \<open>ZMM1 \<equiv> (''zmm1'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM2 :: 'a
where
  \<open>ZMM2 \<equiv> (''zmm2'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM3 :: 'a
where
  \<open>ZMM3 \<equiv> (''zmm3'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM4 :: 'a
where
  \<open>ZMM4 \<equiv> (''zmm4'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM5 :: 'a
where
  \<open>ZMM5 \<equiv> (''zmm5'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM6 :: 'a
where
  \<open>ZMM6 \<equiv> (''zmm6'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

abbreviation
  ZMM7 :: 'a
where
  \<open>ZMM7 \<equiv> (''zmm7'' :\<^sub>t imm\<langle>512\<rangle>)\<close>

text \<open>Definition of flags\<close>

abbreviation
  CF :: 'a
where
  \<open>CF \<equiv> (''cf'' :\<^sub>t imm\<langle>1\<rangle>)\<close>

abbreviation
  OF :: 'a
where
  \<open>OF \<equiv> (''of'' :\<^sub>t imm\<langle>1\<rangle>)\<close>

abbreviation
  AF :: 'a
where
  \<open>AF \<equiv> (''af'':\<^sub>t imm\<langle>1\<rangle>)\<close>

abbreviation
  PF :: 'a
where
  \<open>PF \<equiv> (''pf'' :\<^sub>t imm\<langle>1\<rangle>)\<close>

abbreviation
  SF :: 'a
where
  \<open>SF \<equiv> (''sf'' :\<^sub>t imm\<langle>1\<rangle>)\<close>

abbreviation
  ZF :: 'a
where
  \<open>ZF \<equiv> (''zf'' :\<^sub>t imm\<langle>1\<rangle>)\<close>

text \<open>Syntax for virtual registers\<close>

abbreviation
  virtual_reg :: \<open>nat \<Rightarrow> 'a\<close> (\<open>#_\<close>)
where
  \<open>#(x::nat) \<equiv> (fst (register_id x) :\<^sub>t imm\<langle>snd (register_id x)\<rangle>)\<close>

abbreviation
  virual_alt :: \<open>nat \<Rightarrow> 'a\<close> (\<open>V_\<close>)
where
  \<open>V(x::nat) \<equiv> #x\<close>


end

end