theory Typing_Typed_Ok
  imports Typing_Type Typing_Context
begin

class typed_ok = (* TODO remove in favour of type_syntax *)
    fixes typed_ok :: \<open>TypingContext \<Rightarrow> 'a \<Rightarrow> Type \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ :: _\<close> 215)
  assumes t_is_ok: \<open>\<And>\<Gamma> a t. \<Gamma> \<turnstile> a :: t \<Longrightarrow> t is ok\<close>

end
