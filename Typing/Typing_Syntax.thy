theory Typing_Syntax
  imports HOL.HOL
begin

class is_ok =
  fixes is_ok :: \<open>'a \<Rightarrow> bool\<close> (\<open>_ is ok\<close> [105] 200)

end
