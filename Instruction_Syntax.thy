theory Instruction_Syntax
  imports Formula_Syntax Bitvector_Instance
begin

record insn =
  addr :: word
  size :: word
  code :: bil


function
  no_insn :: \<open>word \<Rightarrow> insn\<close>
where
  \<open>no_insn (val \<Colon> sz) = \<lparr> addr = (val \<Colon> sz), size = (0 \<Colon> sz), code = [] \<rparr>\<close>
  using wordI apply auto[1]
  by auto
termination by (standard, auto)

type_synonym program = \<open>(variables \<times> word \<times> var)\<close>

end