theory X86_64_Instructions
  imports "../../OperationalSemantics/Program_Model"
          X86_64
begin

section \<open>x86-64 Instructions\<close>

text \<open>
  Semantics for the most common x86-64 instructions.

  This is an incomplete subset of the x86-64 instructions, anything not on this list can be solved 
  with solve_bil instead.
\<close>

subsubsection \<open>NOP\<close>

abbreviation \<open>nop' sz w \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [] \<rparr>\<close>

subsubsection \<open>JMP\<close>

abbreviation \<open>jmp' sz w imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [jmp (imm \<Colon> 64)] \<rparr>\<close>

subsubsection \<open>CMPQ\<close>

abbreviation \<open>cmpq' sz w lhs rhs tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  (tmp :\<^sub>t imm\<langle>64\<rangle>) := lhs - rhs, CF := lhs lt rhs,
  OF := high:Suc 0[lhs xor rhs && (lhs xor (tmp :\<^sub>t imm\<langle>64\<rangle>))],
  AF := BinOp (16 \<Colon> 64) (LOp Eq) ((16 \<Colon> 64) && ((tmp :\<^sub>t imm\<langle>64\<rangle>) xor (lhs) xor rhs)),
  PF := \<sim> (low:Suc 0[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) (tmp :\<^sub>t imm\<langle>64\<rangle> >> (4 \<Colon> 64) xor tmp :\<^sub>t imm\<langle>64\<rangle>) 
          (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor ''$0'' :\<^sub>t imm\<langle>64\<rangle>) (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (Suc 0 \<Colon> 64) xor ''$1'' :\<^sub>t imm\<langle>64\<rangle>))]),
  SF := high:Suc 0[tmp :\<^sub>t imm\<langle>64\<rangle>], 
  ZF := BinOp (0 \<Colon> 64) (LOp Eq) (tmp :\<^sub>t imm\<langle>64\<rangle>)
]\<rparr>\<close>

subsubsection \<open>RETQ\<close>

abbreviation \<open>retq' sz w tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  (tmp :\<^sub>t imm\<langle>64\<rangle>) := (mem[RSP, el]:u64), RSP := RSP + (8 \<Colon> 64), jmp (tmp :\<^sub>t imm\<langle>64\<rangle>)
]\<rparr>\<close>

subsubsection \<open>XORL\<close>

abbreviation \<open>xorl_self' sz w var \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  var := (0 \<Colon> 64), AF := unknown[''bits'']: imm\<langle>Suc 0\<rangle>, ZF := true, PF := true, OF := false, CF := false,
  SF := false
]\<rparr>\<close>

subsubsection \<open>JAE\<close>

abbreviation \<open>jae' sz w imm \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  IfThen (\<sim> CF) [jmp (imm \<Colon> 64)]
]\<rparr>\<close>

subsubsection \<open>ADDQ\<close>

abbreviation \<open>addq' sz w rd src tmp\<^sub>1 tmp\<^sub>2 \<equiv>  \<lparr>addr = w, size = sz \<Colon> 64, code = [
  tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>),
  tmp\<^sub>2 :\<^sub>t imm\<langle>64\<rangle> := src,
  rd :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>) + (tmp\<^sub>2 :\<^sub>t imm\<langle>64\<rangle>),
  CF := (rd :\<^sub>t imm\<langle>64\<rangle>) lt (tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle>),
  OF := BinOp (high:Suc 0[tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle>]) (LOp Eq) (high:Suc 0[tmp\<^sub>2 :\<^sub>t imm\<langle>64\<rangle>])
        && ((high:Suc 0[tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle>]) || (high:Suc 0[rd :\<^sub>t imm\<langle>64\<rangle>])
        && \<sim> ((high:Suc 0[tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle>]) && (high:Suc 0[rd :\<^sub>t imm\<langle>64\<rangle>]))),
  AF := BinOp (16 \<Colon> 64) (LOp Eq) ((16 \<Colon> 64) && ((rd :\<^sub>t imm\<langle>64\<rangle>) xor (tmp\<^sub>1 :\<^sub>t imm\<langle>64\<rangle>)
          xor (tmp\<^sub>2 :\<^sub>t imm\<langle>64\<rangle>))),
  PF := \<sim> (low:Suc 0[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) ((rd :\<^sub>t imm\<langle>64\<rangle>) >> (4 \<Colon> 64) xor (rd :\<^sub>t imm\<langle>64\<rangle>)) 
                   (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor (''$0'' :\<^sub>t imm\<langle>64\<rangle>)) 
                            (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (Suc 0 \<Colon> 64) xor (''$1'' :\<^sub>t imm\<langle>64\<rangle>)))]),
  SF := (high:Suc 0[rd :\<^sub>t imm\<langle>64\<rangle>]),
  ZF := BinOp (0 \<Colon> 64) (LOp Eq) (rd :\<^sub>t imm\<langle>64\<rangle>)
]\<rparr>\<close>

subsubsection \<open>mov'\<close>

abbreviation \<open>mov' sz w dest src \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  dest := src
]\<rparr>\<close>

subsubsection \<open>SHLQ\<close>

abbreviation \<open>shlq' sz w rd imm tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  tmp :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>), rd :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>) << (imm \<Colon> 64), 
  CF := low:(Suc 0)[tmp :\<^sub>t imm\<langle>64\<rangle> >> (55 \<Colon> 64)], 
  SF := high:(Suc 0)[rd :\<^sub>t imm\<langle>64\<rangle>], 
  ZF := BinOp (0 \<Colon> 64) (LOp Eq) (rd :\<^sub>t imm\<langle>64\<rangle>),
  PF := \<sim> (low:(Suc 0)[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) (rd :\<^sub>t imm\<langle>64\<rangle> >> (4 \<Colon> 64) xor (rd :\<^sub>t imm\<langle>64\<rangle>)) 
                      (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor ''$0'' :\<^sub>t imm\<langle>64\<rangle>) (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (Suc 0 \<Colon> 64) xor ''$1'' :\<^sub>t imm\<langle>64\<rangle>))]),
  AF := (unknown[''bits'']: imm\<langle>Suc 0\<rangle>), OF := (unknown[''bits'']: imm\<langle>Suc 0\<rangle>)
]\<rparr>\<close>


end
