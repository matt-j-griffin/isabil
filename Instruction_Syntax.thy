theory Instruction_Syntax
  imports Formula_Syntax Bitvector_Instance
begin

record insn = 
  addr :: word
  size :: word
  code :: bil


abbreviation
  no_insn :: insn
where
  \<open>no_insn \<equiv> \<lparr> addr = (0 \<Colon> 0), size = (0 \<Colon> 0), code = [] \<rparr>\<close>

end