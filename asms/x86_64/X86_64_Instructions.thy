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

abbreviation \<open>cmpq' sz w lhs imm\<^sub>r\<^sub>h\<^sub>s rs\<^sub>r\<^sub>h\<^sub>s tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  (tmp :\<^sub>t imm\<langle>64\<rangle>) := (mem[rs\<^sub>r\<^sub>h\<^sub>s + (imm\<^sub>r\<^sub>h\<^sub>s \<Colon> 64), el]:u64) - lhs, CF := (mem[rs\<^sub>r\<^sub>h\<^sub>s + (imm\<^sub>r\<^sub>h\<^sub>s \<Colon> 64), el]:u64) lt lhs,
  OF := high:1[(mem[rs\<^sub>r\<^sub>h\<^sub>s + (imm\<^sub>r\<^sub>h\<^sub>s \<Colon> 64), el]:u64) xor lhs && ((mem[rs\<^sub>r\<^sub>h\<^sub>s + (imm\<^sub>r\<^sub>h\<^sub>s \<Colon> 64), el]:u64) xor (tmp :\<^sub>t imm\<langle>64\<rangle>))],
  AF := BinOp (16 \<Colon> 64) (LOp Eq) ((16 \<Colon> 64) && ((tmp :\<^sub>t imm\<langle>64\<rangle>) xor (mem[rs\<^sub>r\<^sub>h\<^sub>s + (imm\<^sub>r\<^sub>h\<^sub>s \<Colon> 64), el]:u64) xor lhs)),
  PF := negation (low:1[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) (tmp :\<^sub>t imm\<langle>64\<rangle> >> (4 \<Colon> 64) xor tmp :\<^sub>t imm\<langle>64\<rangle>) 
          (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor ''$0'' :\<^sub>t imm\<langle>64\<rangle>) (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (1 \<Colon> 64) xor ''$1'' :\<^sub>t imm\<langle>64\<rangle>))]),
  SF := high:1[tmp :\<^sub>t imm\<langle>64\<rangle>], 
  ZF := BinOp (0 \<Colon> 64) (LOp Eq) (tmp :\<^sub>t imm\<langle>64\<rangle>)
]\<rparr>\<close>

subsubsection \<open>RETQ\<close>

abbreviation \<open>retq' sz w tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  (tmp :\<^sub>t imm\<langle>64\<rangle>) := (mem[RSP, el]:u64), RSP := RSP + (8 \<Colon> 64), jmp (tmp :\<^sub>t imm\<langle>64\<rangle>)
]\<rparr>\<close>

subsubsection \<open>XORL\<close>

abbreviation \<open>xorl_self' sz w var \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  var := (0 \<Colon> 64), AF := unknown[''bits'']: imm\<langle>1\<rangle>, ZF := true, PF := true, OF := false, CF := false,
  SF := false
]\<rparr>\<close>

subsubsection \<open>JAE\<close>

abbreviation \<open>jae' sz w imm \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  IfThen (negation CF) [jmp (imm \<Colon> 64)]
]\<rparr>\<close>

subsubsection \<open>ADDQ\<close>
(*
abbreviation \<open>addq' sz w imm \<equiv>  \<lparr>addr = w, size = sz \<Colon> 64, code = [
  ''#12582869'' :\<^sub>t imm\<langle>64\<rangle> := RAX, ''#12582868'' :\<^sub>t imm\<langle>64\<rangle> := mem[16312 \<Colon> 64, el]:u64, 
  RAX := RAX + ''#12582868'' :\<^sub>t imm\<langle>64\<rangle>, CF := RAX lt ''#12582869'' :\<^sub>t imm\<langle>64\<rangle>,
        OF :=
        BinOp high:1[''#12582869'' :\<^sub>t imm\<langle>64\<rangle>] (LOp Eq) high:1[''#12582868'' :\<^sub>t imm\<langle>64\<rangle>] &&
        (high:1[''#12582869'' :\<^sub>t imm\<langle>64\<rangle>] || high:1[RAX] && negation (high:1[''#12582869'' :\<^sub>t imm\<langle>64\<rangle>] && high:1[RAX])),
        AF := BinOp (16 \<Colon> 64) (LOp Eq) ((16 \<Colon> 64) && (RAX xor ''#12582869'' :\<^sub>t imm\<langle>64\<rangle> xor ''#12582868'' :\<^sub>t imm\<langle>64\<rangle>)),
        PF :=
        negation
         low:1[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) (RAX >> (4 \<Colon> 64) xor RAX)
                (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor ''$0'' :\<^sub>t imm\<langle>64\<rangle>) (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (1 \<Colon> 64) xor ''$1'' :\<^sub>t imm\<langle>64\<rangle>))],
        SF := high:1[RAX], ZF := BinOp (0 \<Colon> 64) (LOp Eq) RAX
]\<rparr>\<close>*)

subsubsection \<open>mov'\<close>

abbreviation \<open>mov' sz w dest src \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  dest := src
]\<rparr>\<close>

subsubsection \<open>SHLQ\<close>

abbreviation \<open>shlq' sz w rd imm tmp \<equiv> \<lparr>addr = w, size = sz \<Colon> 64, code = [
  tmp :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>), rd :\<^sub>t imm\<langle>64\<rangle> := (rd :\<^sub>t imm\<langle>64\<rangle>) << (imm \<Colon> 64), 
  CF := low:1[tmp :\<^sub>t imm\<langle>64\<rangle> >> (55 \<Colon> 64)], 
  SF := high:1[rd :\<^sub>t imm\<langle>64\<rangle>], 
  ZF := BinOp (0 \<Colon> 64) (LOp Eq) (rd :\<^sub>t imm\<langle>64\<rangle>),
  PF := negation low:1[exp.Let (''$0'' :\<^sub>t imm\<langle>64\<rangle>) (RAX >> (4 \<Colon> 64) xor (rd :\<^sub>t imm\<langle>64\<rangle>)) 
                      (exp.Let (''$1'' :\<^sub>t imm\<langle>64\<rangle>) (''$0'' :\<^sub>t imm\<langle>64\<rangle> >> (2 \<Colon> 64) xor ''$0'' :\<^sub>t imm\<langle>64\<rangle>) (''$1'' :\<^sub>t imm\<langle>64\<rangle> >> (1 \<Colon> 64) xor ''$1'' :\<^sub>t imm\<langle>64\<rangle>))],
  AF := (unknown[''bits'']: imm\<langle>1\<rangle>), OF := (unknown[''bits'']: imm\<langle>1\<rangle>)
]\<rparr>\<close>


end
