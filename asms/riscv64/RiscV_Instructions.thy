theory RiscV_Instructions
  imports IsaBIL.Program_Model
          RiscV_64
begin

section \<open>RISC-V Instructions\<close>

text \<open>
  Semantics for the most common RISC-V instructions.

  This is an incomplete subset of the RISC instructions, anything not on this list can be solved 
  with solve_bil instead.
\<close>

subsubsection \<open>SLLIW\<close>

abbreviation \<open>slli' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) << (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>slliw \<equiv> slli' 4\<close>

subsubsection \<open>SRLIW\<close>

abbreviation \<open>srliw' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) >> (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>srliw \<equiv> srliw' 4\<close>

subsubsection \<open>AND\<close>

abbreviation 
  "and" :: \<open>word \<Rightarrow> var \<Rightarrow> string \<Rightarrow> string \<Rightarrow> insn\<close>
where
  \<open>and w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) && (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

subsubsection \<open>OR\<close>

abbreviation 
  "or" :: \<open>word \<Rightarrow> var \<Rightarrow> string \<Rightarrow> string \<Rightarrow> insn\<close>
where
  \<open>or w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) || (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

subsubsection \<open>ADD\<close>

abbreviation \<open>add w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>
abbreviation \<open>addi' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>addi \<equiv> addi' 4\<close>
abbreviation \<open>caddi \<equiv> addi' 2\<close>
abbreviation \<open>addiw' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)]]] \<rparr>\<close>
abbreviation \<open>addiw \<equiv> addiw' 4\<close>
abbreviation \<open>caddiw \<equiv> addiw' 2\<close>

subsubsection \<open>SUB\<close>

abbreviation \<open>sub' sz w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) - (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>
abbreviation \<open>sub \<equiv> sub' 4\<close>
abbreviation \<open>csub  \<equiv> sub' 2\<close>

subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>

abbreviation \<open>sextw' sz w rd rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>)]])] \<rparr>\<close>
abbreviation \<open>sextw \<equiv> sextw' 4\<close>
abbreviation \<open>csextw \<equiv> sextw' 2\<close>

subsubsection \<open>SD\<close>

abbreviation \<open>sd' sz w rs1 imm rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))] \<rparr>\<close>
abbreviation \<open>sd \<equiv> sd' 4\<close>
abbreviation \<open>csd \<equiv> sd' 2\<close>
abbreviation \<open>sdzero' sz w rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (0 \<Colon> 64))] \<rparr>\<close>
abbreviation \<open>sd0 w rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))] \<rparr>\<close>
abbreviation \<open>sd0zero' sz w rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64 \<leftarrow> (0 \<Colon> 64))] \<rparr>\<close>

subsubsection \<open>AUIPC\<close>

abbreviation \<open>auipc w rd imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>

subsubsection \<open>LI\<close>

abbreviation \<open>li' sz w rd imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>li  \<equiv> li' 4\<close>
abbreviation \<open>cli \<equiv> li' 2\<close>

subsubsection \<open>JAL\<close>

abbreviation \<open>jal w ret target \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<rparr>\<close>

subsubsection \<open>JALR\<close>

abbreviation \<open>jalr' sz w rs1 ret target \<equiv>  \<lparr> addr = w, size = (sz \<Colon> 64), code = [X6 := (ret \<Colon> 64), jmp ((rs1 :\<^sub>t imm\<langle>64\<rangle>) + (target \<Colon> 64))]\<rparr>\<close>
abbreviation \<open>jalr \<equiv> jalr' 4\<close>
abbreviation \<open>cjalr w rs1 ret \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp ((rs1 :\<^sub>t imm\<langle>64\<rangle>))]\<rparr>\<close>

subsubsection \<open>MV\<close>

abbreviation \<open>mv w rd rs1 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>)]\<rparr>\<close>

subsubsection \<open>LW\<close>

abbreviation \<open>lw' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32])]\<rparr>\<close>
abbreviation \<open>lw0' sz w rd rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u32])]\<rparr>\<close>

abbreviation \<open>lw \<equiv> lw' 4\<close>
abbreviation \<open>lw0 \<equiv> lw0' 4\<close>
abbreviation \<open>clw \<equiv> lw' 2\<close>
abbreviation \<open>clw0 \<equiv> lw0' 2\<close>

subsubsection \<open>SW\<close>

abbreviation \<open>sw' sz w rs1 imm rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32 \<leftarrow> (low:32[rs2 :\<^sub>t imm\<langle>64\<rangle>]))]\<rparr>\<close>
abbreviation \<open>sw \<equiv> sw' 4\<close>
abbreviation \<open>sw0' sz w rs1 rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [rs1 :\<^sub>t imm\<langle>64\<rangle>, el]:u32 \<leftarrow> (low:32[rs2 :\<^sub>t imm\<langle>64\<rangle>]))]\<rparr>\<close>
abbreviation \<open>sw0 \<equiv> sw0' 2\<close>
abbreviation \<open>swzero' sz w rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32 \<leftarrow> (0 \<Colon> 32))]\<rparr>\<close>
abbreviation \<open>sw0zero' sz w rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u32 \<leftarrow> (0 \<Colon> 32))]\<rparr>\<close>

subsubsection \<open>BEQ\<close>

abbreviation \<open>beq w tmp rs1 rs2 offset \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [(tmp :\<^sub>t imm\<langle>Suc 0\<rangle>) := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (tmp :\<^sub>t imm\<langle>Suc 0\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>

subsubsection \<open>BEQZ\<close>

abbreviation \<open>beqz' sz w temp rs1 offset \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [temp :\<^sub>t imm\<langle>Suc 0\<rangle> := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64), IfThen (temp :\<^sub>t imm\<langle>Suc 0\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>
abbreviation \<open>beqz \<equiv> beqz' 4\<close>
abbreviation \<open>cbeqz \<equiv> beqz' 2\<close>

subsubsection \<open>LD\<close>

abbreviation \<open>ld' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64)]\<rparr>\<close>
abbreviation \<open>ld \<equiv> ld' 4\<close>
abbreviation \<open>cld \<equiv> ld' 2\<close>

abbreviation \<open>ld0' sz w rd rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64)]\<rparr>\<close>
abbreviation \<open>ld0 \<equiv> ld0' 4\<close>
abbreviation \<open>cld0 \<equiv> ld0' 2\<close>

subsubsection \<open>J\<close>

abbreviation \<open>j w imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [jmp (imm \<Colon> 64)]\<rparr>\<close>

subsubsection \<open>NOP\<close>

abbreviation \<open>nop' sz w \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = []\<rparr>\<close>
abbreviation \<open>nop \<equiv> nop' 2\<close>

subsubsection \<open>LUI\<close>

abbreviation \<open>lui w rd imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>

subsubsection \<open>BGE\<close>

abbreviation \<open>bge w rs1 rs2 temp imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>Suc 0\<rangle> := (rs1 :\<^sub>t imm\<langle>64\<rangle>) le (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (temp :\<^sub>t imm\<langle>Suc 0\<rangle>) [jmp (imm \<Colon> 64)]]\<rparr>\<close>

subsubsection \<open>BNEZ\<close>

abbreviation \<open>bnez w rs1 temp imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>Suc 0\<rangle> := BinOp (BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64)) (LOp Eq) false, IfThen (temp :\<^sub>t imm\<langle>Suc 0\<rangle>) [jmp (imm \<Colon> 64)]]\<rparr>\<close>

subsubsection \<open>BLTU\<close>

abbreviation \<open>bltu' sz w rs1 rs2 temp imm \<equiv>  \<lparr>addr = w, size = sz \<Colon> 64, code = [temp :\<^sub>t imm\<langle>Suc 0\<rangle> := (rs1 :\<^sub>t imm\<langle>64\<rangle>) lt (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (temp :\<^sub>t imm\<langle>Suc 0\<rangle>) [jmp (imm \<Colon> 64)]]\<rparr>\<close>
abbreviation \<open>bltu \<equiv>  bltu' 4\<close>
abbreviation \<open>cbltu \<equiv> bltu' 2\<close>

subsubsection \<open>RET\<close>

abbreviation \<open>ret' sz w \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [jmp X1]\<rparr>\<close>
abbreviation \<open>ret \<equiv> ret' 2\<close>

end
