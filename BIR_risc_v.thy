theory BIR_risc_v
  imports BIL_Syntax
begin

text \<open>Architecture size of 32/64/128 bits\<close>

consts addr_size :: nat

context var_syntax
begin

text \<open>Definition data memory\<close>

abbreviation
  mem :: 'a
where
  \<open>mem \<equiv> (''mem'' :\<^sub>t mem\<langle>addr_size, 8\<rangle>)\<close>

text \<open>Definition of registers\<close>

text \<open>x0 - Hardwired zero (abi: zero)\<close>

abbreviation
  X0 :: 'a
where
  \<open>X0 \<equiv> (''x0'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x1 - Return Address (abi: ra)\<close>

abbreviation
  X1 :: 'a
where
  \<open>X1 \<equiv> (''x1'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x2 - Stack pointer (abi: sp)\<close>

abbreviation
  X2 :: 'a
where
  \<open>X2 \<equiv> (''x2'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x3 - Global pointer (abi: gp)\<close>

abbreviation
  X3 :: 'a
where
  \<open>X3 \<equiv> (''x3'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x4 - Global pointer (abi: tp)\<close>

abbreviation
  X4 :: 'a
where
  \<open>X4 \<equiv> (''x4'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x5 - Temporary register 0 (abi: t0)\<close>

abbreviation
  X5 :: 'a
where
  \<open>X5 \<equiv> (''x5'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x6 - Temporary register 1 (abi: t1)\<close>

abbreviation
  X6 :: 'a
where
  \<open>X6 \<equiv> (''x6'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x7 - Temporary register 2 (abi: t2)\<close>

abbreviation
  X7 :: 'a
where
  \<open>X7 \<equiv> (''x7'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x8 - saved register 0 / frame pointer (abi: s0/fp)\<close>

abbreviation
  X8 :: 'a
where
  \<open>X8 \<equiv> (''x8'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x9 - saved register 1 (abi: s1)\<close>

abbreviation
  X9 :: 'a
where
  \<open>X9 \<equiv> (''x9'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x10 - function argument 0 / return value 0 (abi: a0)\<close>

abbreviation
  X10 :: 'a
where
  \<open>X10 \<equiv> (''x10'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x11 - function argument 1 / return value 1 (abi: a1)\<close>

abbreviation
  X11 :: 'a
where
  \<open>X11 \<equiv> (''x11'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x12 - function argument 2 (abi: a2)\<close>

abbreviation
  X12 :: 'a
where
  \<open>X12 \<equiv> (''x12'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x13 - function argument 3 (abi: a3)\<close>

abbreviation
  X13 :: 'a
where
  \<open>X13 \<equiv> (''x13'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x14 - function argument 4 (abi: a4)\<close>

abbreviation
  X14 :: 'a
where
  \<open>X14 \<equiv> (''x14'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x15 - function argument 5 (abi: a5)\<close>

abbreviation
  X15 :: 'a
where
  \<open>X15 \<equiv> (''x15'' :\<^sub>t imm\<langle>64\<rangle>)\<close>

text \<open>x16 - function argument 6 (abi: a6)\<close>

abbreviation
  X16 :: 'a
where
  \<open>X16 \<equiv> (''x16'' :\<^sub>t imm\<langle>64\<rangle>)\<close>
(*
17	-	x17	a7	function argument 7	-R
18	-	x18	s2	saved register 2	-E
19	-	x19	s3	saved register 3	-E
20	-	x20	s4	saved register 4	-E
21	-	x21	s5	saved register 5	-E
22	-	x22	s6	saved register 6	-E
23	-	x23	s7	saved register 7	-E
24	-	x24	s8	saved register 8	-E
25	-	x25	s9	saved register 9	-E
26	-	x26	s10	saved register 10	-E
27	-	x27	s11	saved register 11	-E
28	-	x28	t3	temporary register 3	-R
29	-	x29	t4	temporary register 4	-R
30	-	x30	t5	temporary register 5	-R
31	-	x31	t6	temporary register 6	-R
*)
end