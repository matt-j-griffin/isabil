theory RiscV_64
  imports "../BIL_Syntax"
begin

text \<open>Architecture size of 32/64/128 bits\<close>

context var_syntax
begin

text \<open>Definition data memory\<close>

abbreviation
  mem :: 'a
where
  \<open>mem \<equiv> (''mem'' :\<^sub>t mem\<langle>64, 8\<rangle>)\<close>

text \<open>Definition of registers\<close>

text \<open>X0 - Hardwired zero (abi: zero)\<close>

abbreviation
  X0 :: 'a
where
  \<open>X0 \<equiv> (''X0'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X1 - Return Address (abi: ra)\<close>

abbreviation
  X1 :: 'a
where
  \<open>X1 \<equiv> (''X1'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X2 - Stack pointer (abi: sp)\<close>

abbreviation
  X2 :: 'a
where
  \<open>X2 \<equiv> (''X2'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X3 - Global pointer (abi: gp)\<close>

abbreviation
  X3 :: 'a
where
  \<open>X3 \<equiv> (''X3'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X4 - Global pointer (abi: tp)\<close>

abbreviation
  X4 :: 'a
where
  \<open>X4 \<equiv> (''X4'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X5 - Temporary register 0 (abi: t0)\<close>

abbreviation
  X5 :: 'a
where
  \<open>X5 \<equiv> (''X5'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X6 - Temporary register 1 (abi: t1)\<close>

abbreviation
  X6 :: 'a
where
  \<open>X6 \<equiv> (''X6'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X7 - Temporary register 2 (abi: t2)\<close>

abbreviation
  X7 :: 'a
where
  \<open>X7 \<equiv> (''X7'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X8 - saved register 0 / frame pointer (abi: s0/fp)\<close>

abbreviation
  X8 :: 'a
where
  \<open>X8 \<equiv> (''X8'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X9 - saved register 1 (abi: s1)\<close>

abbreviation
  X9 :: 'a
where
  \<open>X9 \<equiv> (''X9'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>X10 - function argument 0 / return value 0 (abi: a0)\<close>

abbreviation
  X10 :: 'a
where
  \<open>X10 \<equiv> (''X10'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x11 - function argument 1 / return value 1 (abi: a1)\<close>

abbreviation
  X11 :: 'a
where
  \<open>X11 \<equiv> (''X11'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x12 - function argument 2 (abi: a2)\<close>

abbreviation
  X12 :: 'a
where
  \<open>X12 \<equiv> (''X12'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x13 - function argument 3 (abi: a3)\<close>

abbreviation
  X13 :: 'a
where
  \<open>X13 \<equiv> (''X13'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x14 - function argument 4 (abi: a4)\<close>

abbreviation
  X14 :: 'a
where
  \<open>X14 \<equiv> (''X14'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x15 - function argument 5 (abi: a5)\<close>

abbreviation
  X15 :: 'a
where
  \<open>X15 \<equiv> (''X15'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x16 - function argument 6 (abi: a6)\<close>

abbreviation
  X16 :: 'a
where
  \<open>X16 \<equiv> (''X16'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x17 - function argument 7 (abi: a6)\<close>

abbreviation
  X17 :: 'a
where
  \<open>X17 \<equiv> (''X17'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x18 - saved register 2 (abi: s2)\<close>

abbreviation
  X18 :: 'a
where
  \<open>X18 \<equiv> (''X18'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x19 - saved register 3 (abi: s3)\<close>

abbreviation
  X19 :: 'a
where
  \<open>X19 \<equiv> (''X19'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x20 - saved register 4 (abi: s4)\<close>

abbreviation
  X20 :: 'a
where
  \<open>X20 \<equiv> (''X20'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x21 - saved register 5 (abi: s5)\<close>

abbreviation
  X21 :: 'a
where
  \<open>X21 \<equiv> (''X21'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x22 - saved register 6 (abi: s6)\<close>

abbreviation
  X22 :: 'a
where
  \<open>X22 \<equiv> (''X22'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x23 - saved register 7 (abi: s7)\<close>

abbreviation
  X23 :: 'a
where
  \<open>X23 \<equiv> (''X23'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x24 - saved register 8 (abi: s8)\<close>

abbreviation
  X24 :: 'a
where
  \<open>X24 \<equiv> (''X24'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x25 - saved register 9 (abi: s9)\<close>

abbreviation
  X25 :: 'a
where
  \<open>X25 \<equiv> (''X25'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x26 - saved register 10 (abi: s10)\<close>

abbreviation
  X26 :: 'a
where
  \<open>X26 \<equiv> (''X26'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x27 - saved register 11 (abi: s11)\<close>

abbreviation
  X27 :: 'a
where
  \<open>X27 \<equiv> (''X27'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x28 - temporary register 3 (abi: t3)\<close>

abbreviation
  X28 :: 'a
where
  \<open>X28 \<equiv> (''X28'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x29 - temporary register 4 (abi: t4)\<close>

abbreviation
  X29 :: 'a
where
  \<open>X29 \<equiv> (''X29'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x30 - temporary register 5 (abi: t5)\<close>

abbreviation
  X30 :: 'a
where
  \<open>X30 \<equiv> (''X30'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x31 - temporary register 6 (abi: t6)\<close>

abbreviation
  X31 :: 'a
where
  \<open>X31 \<equiv> (''X31'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

end

end
