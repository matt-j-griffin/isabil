theory Instruction_Syntax
  imports Formula_Syntax
begin

record insn = 
  addr :: word
  size :: word
  code :: bil

abbreviation
  no_insn :: insn
where
  \<open>no_insn \<equiv> \<lparr> addr = (0 \<Colon> 0), size = (0 \<Colon> 0), code = Empty \<rparr>\<close>

end