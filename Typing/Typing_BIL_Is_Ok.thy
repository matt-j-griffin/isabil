theory Typing_BIL_Is_Ok
  imports Typing_Exp_Typed_Ok
begin            
(*
fun
  typing_is_ok_stmt :: \<open>TypingContext \<Rightarrow> stmt \<Rightarrow> bool\<close> and
  typing_is_ok_bil :: \<open>TypingContext \<Rightarrow> bil \<Rightarrow> bool\<close>
where
  \<open>typing_is_ok_stmt \<Gamma> (Move (var.Var id' t) e) = ((\<Gamma> \<turnstile> (exp.Var (var.Var id' t)) :: t) \<and> (\<Gamma> \<turnstile> e :: t))\<close> |
  \<open>typing_is_ok_stmt \<Gamma> (Jmp e) = (\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>))\<close> |
  \<open>typing_is_ok_stmt \<Gamma> (CpuExn _) = (\<Gamma> is ok)\<close> |
  \<open>typing_is_ok_stmt \<Gamma> (Special _) = (\<Gamma> is ok)\<close> |
  \<open>typing_is_ok_stmt \<Gamma> (While e seq) = ((typing_is_ok_bil \<Gamma> seq) \<and> (\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>))\<close> |
  \<open>typing_is_ok_stmt \<Gamma> (If e seq\<^sub>1 seq\<^sub>2) = ((typing_is_ok_bil \<Gamma> seq\<^sub>1) \<and> (typing_is_ok_bil \<Gamma> seq\<^sub>2) \<and> (\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>))\<close> |
  \<open>typing_is_ok_bil \<Gamma> [] = True\<close> |
  \<open>typing_is_ok_bil \<Gamma> (stmt # seq) = ((typing_is_ok_stmt \<Gamma> stmt) \<and> (typing_is_ok_bil \<Gamma> seq))\<close>
*)

function
  typing_is_ok_stmt' :: \<open>TypingContext \<Rightarrow> stmt \<Rightarrow> bool\<close> and
  typing_is_ok_bil' :: \<open>TypingContext \<Rightarrow> bil \<Rightarrow> bool\<close>
where
  \<open>typing_is_ok_stmt' \<Gamma> (Move (id' :\<^sub>t t) e) = ((\<Gamma> \<turnstile> ((id' :\<^sub>t t)::exp) :: t) \<and> (\<Gamma> \<turnstile> e :: t))\<close> |
  \<open>typing_is_ok_stmt' \<Gamma> (Jmp e) = (\<exists>sz. (\<Gamma> \<turnstile> e :: imm\<langle>sz\<rangle>))\<close> |
  \<open>typing_is_ok_stmt' \<Gamma> (CpuExn _) = (\<Gamma> is ok)\<close> |
  \<open>typing_is_ok_stmt' \<Gamma> (Special _) = (\<Gamma> is ok)\<close> |
  \<open>typing_is_ok_stmt' \<Gamma> (While e seq) = ((typing_is_ok_bil' \<Gamma> seq) \<and> (\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>))\<close> |
  \<open>typing_is_ok_stmt' \<Gamma> (If e seq\<^sub>1 seq\<^sub>2) = ((typing_is_ok_bil' \<Gamma> seq\<^sub>1) \<and> (typing_is_ok_bil' \<Gamma> seq\<^sub>2) \<and> (\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>))\<close> |
  \<open>typing_is_ok_bil' \<Gamma> [] = True\<close> |
  \<open>typing_is_ok_bil' \<Gamma> (stmt # seq) = ((typing_is_ok_stmt' \<Gamma> stmt) \<and> (typing_is_ok_bil' \<Gamma> seq))\<close>
  apply simp_all
  subgoal for P x 
    apply (rule obj_sumE[of x])
    apply auto
    subgoal for a b
      apply (cases b rule: stmt.exhaust)
      apply simp_all
      using var_exhaust by auto
    subgoal for a b
      apply (cases b)
      by blast+
    .
  .
termination
  apply standard
  apply (relation \<open>case_sum (\<lambda>p. size (snd p)) (\<lambda>p. size_list size (snd p)) <*mlex*> {}\<close>)
  apply (rule wf_mlex, blast)
  by (rule mlex_less, simp)+


class typing_is_ok =
  fixes typing_is_ok :: \<open>TypingContext \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _ is ok\<close> [260, 235] 201)


instantiation stmt :: typing_is_ok
begin

definition
  typing_is_ok_stmt :: \<open>TypingContext \<Rightarrow> stmt \<Rightarrow> bool\<close>
where
  \<open>typing_is_ok_stmt \<equiv> typing_is_ok_stmt'\<close>

instance ..

end

instantiation list :: (typing_is_ok) typing_is_ok
begin

definition
  typing_is_ok_list :: \<open>TypingContext \<Rightarrow> bil \<Rightarrow> bool\<close>
where
  \<open>typing_is_ok_list \<equiv> typing_is_ok_bil'\<close>

instance ..

end

lemma empty_seq_typing_is_ok: 
  assumes \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> ([]::bil) is ok\<close>
  unfolding typing_is_ok_list_def by simp

lemma rec_seq_typing_is_okI: 
    fixes stmt :: stmt
  assumes \<open>\<Gamma> \<turnstile> stmt is ok\<close> and \<open>\<Gamma> \<turnstile> seq is ok\<close>
    shows \<open>\<Gamma> \<turnstile> (stmt # seq) is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma rec_seq_typing_is_okE: 
    fixes stmt :: stmt
  assumes \<open>\<Gamma> \<turnstile> (stmt # seq) is ok\<close>
    shows \<open>\<Gamma> \<turnstile> stmt is ok \<and> \<Gamma> \<turnstile> seq is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma one_seq_typing_is_okI: 
    fixes stmt :: stmt
  assumes \<open>\<Gamma> \<turnstile> stmt is ok\<close>
    shows \<open>\<Gamma> \<turnstile> [stmt] is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma one_seq_typing_is_okE: 
    fixes stmt :: stmt
    assumes \<open>\<Gamma> \<turnstile> [stmt] is ok\<close>
    shows \<open>\<Gamma> \<turnstile> stmt is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

\<comment> \<open>Lemma aliases for the BIL specification\<close>

lemmas T_SEQ_EMPTY = empty_seq_typing_is_ok
lemmas T_SEQ_ONE = one_seq_typing_is_okI
lemmas T_SEQ_REC = rec_seq_typing_is_okI

lemma move_stmt_typing_is_okI:
  assumes \<open>\<Gamma> \<turnstile> ((id' :\<^sub>t t)::exp) :: t\<close> and \<open>\<Gamma> \<turnstile> exp :: t\<close> 
    shows \<open>\<Gamma> \<turnstile> (((id' :\<^sub>t t) := exp)::stmt) is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by simp

lemma move_stmt_typing_is_okE:
  assumes \<open>\<Gamma> \<turnstile> (((id' :\<^sub>t t) := exp)::stmt) is ok\<close> 
    shows \<open>(\<Gamma> \<turnstile> ((id' :\<^sub>t t)::exp) :: t) \<and> (\<Gamma> \<turnstile> exp :: t)\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma jmp_stmt_typing_is_okI:
  assumes \<open>\<Gamma> \<turnstile> exp :: imm\<langle>sz\<rangle>\<close> 
    shows \<open>\<Gamma> \<turnstile> jmp exp is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma jmp_stmt_typing_is_okE:
  assumes \<open>\<Gamma> \<turnstile> jmp exp is ok\<close> 
    shows \<open>\<exists>sz. (\<Gamma> \<turnstile> exp :: imm\<langle>sz\<rangle>)\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma cpuexn_stmt_typing_is_okI:
  assumes \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> cpuexn num is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma cpuexn_stmt_typing_is_okE:
  assumes \<open>\<Gamma> \<turnstile> cpuexn num is ok\<close>
    shows \<open>\<Gamma> is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma special_stmt_typing_is_okI: 
  assumes \<open>\<Gamma> is ok\<close>
    shows \<open>\<Gamma> \<turnstile> special[str] is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by simp

lemma special_stmt_typing_is_okE: 
  assumes \<open>\<Gamma> \<turnstile> special[str] is ok\<close>
    shows \<open>\<Gamma> is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by simp

lemma while_stmt_typing_is_okI: 
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> seq is ok\<close>
    shows \<open>\<Gamma> \<turnstile> while (e) seq is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by simp

lemma while_stmt_typing_is_okE: 
  assumes \<open>\<Gamma> \<turnstile> while (e) seq is ok\<close>
    shows \<open>(\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>) \<and> \<Gamma> \<turnstile> seq is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by simp

lemma if_stmt_typing_is_okI: 
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> seq\<^sub>1 is ok\<close> and \<open>\<Gamma> \<turnstile> seq\<^sub>2 is ok\<close>
    shows \<open>\<Gamma> \<turnstile> if (e) seq\<^sub>1 else seq\<^sub>2 is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma if_stmt_typing_is_okE: 
  assumes \<open>\<Gamma> \<turnstile> if (e) seq\<^sub>1 else seq\<^sub>2 is ok\<close>
    shows \<open>(\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>) \<and> \<Gamma> \<turnstile> seq\<^sub>1 is ok \<and> \<Gamma> \<turnstile> seq\<^sub>2 is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma ifthen_stmt_typing_is_okI:
  assumes \<open>\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>\<close> and \<open>\<Gamma> \<turnstile> seq is ok\<close>
    shows \<open>\<Gamma> \<turnstile> IfThen e seq is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

lemma ifthen_stmt_typing_is_okE:
  assumes \<open>\<Gamma> \<turnstile> IfThen e seq is ok\<close>
    shows \<open>(\<Gamma> \<turnstile> e :: imm\<langle>1\<rangle>) \<and> \<Gamma> \<turnstile> seq is ok\<close>
  using assms unfolding typing_is_ok_list_def typing_is_ok_stmt_def by auto

\<comment> \<open>Lemma aliases for the BIL specification\<close>

lemmas T_MOVE = move_stmt_typing_is_okI
lemmas T_JMP = jmp_stmt_typing_is_okI
lemmas T_CPUEXN = cpuexn_stmt_typing_is_okI
lemmas T_SPECIAL = special_stmt_typing_is_okI
lemmas T_WHILE = while_stmt_typing_is_okI
lemmas T_IF = if_stmt_typing_is_okI
lemmas T_IFTHEN = ifthen_stmt_typing_is_okI

method solve_T_BIL = (
  (rule T_SEQ_EMPTY, solve_TG) |
  (rule T_SEQ_ONE, solve_T_BIL) |
  (rule T_SEQ_REC, solve_T_BIL, solve_T_BIL) |
  (match conclusion in
    \<open>_ \<turnstile> jmp (_ \<Colon> sz) is ok\<close> for sz \<Rightarrow> \<open>rule T_JMP[of _ _ sz], solve_T_WORD\<close>
  \<bar> \<open>_ \<turnstile> (_ := _) is ok\<close> \<Rightarrow> \<open>rule T_MOVE, solve_T_VAR, solve_T_EXP\<close> 
  \<bar> \<open>_ \<turnstile> IfThen _ _ is ok\<close> \<Rightarrow> \<open>rule T_IFTHEN, solve_T_EXP, solve_T_BIL\<close>
  \<bar> _ \<Rightarrow> \<open>succeed\<close>)
)

end