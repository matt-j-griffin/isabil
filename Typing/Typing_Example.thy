theory Typing_Example
  imports Typing
begin

theorem
 \<open>\<not>(\<Gamma> \<turnstile> (Stmt (If foo (Stmt ((x :\<^sub>t imm\<langle>1\<rangle>) := false) Empty) (Stmt ((x :\<^sub>t imm\<langle>32\<rangle>) := (42 \<Colon> 32)) Empty)) bar) is ok)\<close>
  apply clarify
  apply (drule rec_seq_typing_is_okE, clarify)
  apply (drule if_stmt_typing_is_okE)
  apply clarify
  apply (drule one_seq_typing_is_okE)+
  apply (drule move_stmt_typing_is_okE)+
  apply clarify
  apply (drule var_typed_okE)
  apply (drule var_typed_okE)
  apply clarify
  apply (drule set_not_\<Gamma>_is_ok)
  apply simp
  apply simp
  by simp

end