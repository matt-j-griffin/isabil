theory Type_Syntax
  imports Main
begin

text \<open>The type system of BIL consists of two type families - immediate values, indexed by a bitwidth,
and storagies (aka memories), indexed with address bitwidth and values bitwidth.\<close>

datatype Type =
    Imm nat (\<open>imm\<langle>_\<rangle>\<close>)
  | Mem nat nat (\<open>mem\<langle>_, _\<rangle>\<close>)

class type_syntax =
    fixes type :: \<open>'a \<Rightarrow> Type\<close>
  assumes type_determ: \<open>\<And>v t t'. \<lbrakk>type v = t; type v = t'\<rbrakk> \<Longrightarrow> t' = t\<close>

end