theory X86_64
  imports "../../BIL_Syntax"
begin

text \<open>BIR variables are passed down from LLVM IR see here: https://dse.in.tum.de/wp-content/uploads/2022/01/translating_x86_binaries_into_llvm_intermediate_representation.pdf\<close>

context var_syntax
begin

abbreviation
  mem :: 'a
where
  \<open>mem \<equiv> (''mem'' :\<^sub>t mem\<langle>64, 8\<rangle>)\<close>

text \<open>Definition of named (purpose) registers\<close>

abbreviation
  RAX :: 'a
where
  \<open>RAX \<equiv> (''RAX'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RBX :: 'a
where
  \<open>RBX \<equiv> (''RBX'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RCX :: 'a
where
  \<open>RCX \<equiv> (''RCX'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RDX :: 'a
where
  \<open>RDX \<equiv> (''RDX'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RSP :: 'a
where
  \<open>RSP \<equiv> (''RSP'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RBP :: 'a
where
  \<open>RBP \<equiv> (''RBP'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RDI :: 'a
where
  \<open>RDI \<equiv> (''RDI'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  RSI :: 'a
where
  \<open>RSI \<equiv> (''RSI'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>Definition of unnamed (general purpose) registers\<close>

abbreviation
  R8 :: 'a
where
  \<open>R8 \<equiv> (''R8'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R9 :: 'a
where
  \<open>R9 \<equiv> (''R9'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R10 :: 'a
where
  \<open>R10 \<equiv> (''R10'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R11 :: 'a
where
  \<open>R11 \<equiv> (''R11'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R12 :: 'a
where
  \<open>R12 \<equiv> (''R12'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R13 :: 'a
where
  \<open>R13 \<equiv> (''R13'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R14 :: 'a
where
  \<open>R14 \<equiv> (''R14'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

abbreviation
  R15 :: 'a
where
  \<open>R15 \<equiv> (''R15'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

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
  \<open>CF \<equiv> (''CF'' :\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

abbreviation
  OF :: 'a
where
  \<open>OF \<equiv> (''OF'' :\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

abbreviation
  AF :: 'a
where
  \<open>AF \<equiv> (''AF'':\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

abbreviation
  PF :: 'a
where
  \<open>PF \<equiv> (''PF'' :\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

abbreviation
  SF :: 'a
where
  \<open>SF \<equiv> (''SF'' :\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

abbreviation
  ZF :: 'a
where
  \<open>ZF \<equiv> (''ZF'' :\<^sub>t imm\<langle>Suc 0\<rangle>)\<close>

end

end