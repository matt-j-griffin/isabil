theory RiscV_Instructions
  imports "../../isabil/extras/Additional_Program_Semantics"
          RiscV_64
begin

subsection \<open>RISC-V Instructions\<close>

text \<open>
  Semantics for the most common RISC-V instructions.

  This is an incomplete subset of the RISC instructions, anything not on this list can be solved 
  with solve_bil instead.
\<close>

context bil_syntax
begin

subsubsection \<open>ADDI\<close>

lemma step_addi:
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) (Stmt (rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)) Empty)\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val + imm) mod 2 ^ 64 \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_addi)

subsubsection \<open>SD\<close>

lemma step_sd:
  assumes decode_sd: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) (Stmt (mem := mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>)) Empty)\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage64 mem' ((mem_addr + imm) mod 2 ^ 64) 64 val), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_sd)

subsubsection \<open>LI\<close>

lemma step_li:
  assumes decode_li: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) (Stmt ((rd :\<^sub>t imm\<langle>64\<rangle>) := (imm \<Colon> 64)) Empty)\<close>
    shows  \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> (imm \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_li)

subsubsection \<open>JAL\<close>

lemma step_jal: 
  assumes decode_jal:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) (Stmt (X1 := (ret \<Colon> 64)) (Stmt (jmp (target \<Colon> 64)) Empty))\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_jal)

subsubsection \<open>MV\<close>

lemma step_mv: 
  assumes decode_mv:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) (Stmt ((rd :\<^sub>t imm\<langle>64\<rangle>) := (rs1 :\<^sub>t imm\<langle>64\<rangle>)) Empty)\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_mv)

subsection \<open>LW\<close>

lemma step_lw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) (Stmt ((rd :\<^sub>t imm\<langle>64\<rangle>) := extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32]) Empty)\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<And>\<Delta>. \<Delta> \<turnstile> extend:64[Val mem'[(mem_addr + imm) mod 2 ^ 64 \<Colon> 64, el]:u32] \<leadsto>* val \<Colon> 64\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-4))
  apply (solve_prog decoder: decode_lw)
  by (rule load)

subsection \<open>BEQZ\<close>

lemma step_beqz:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) (Stmt (temp :\<^sub>t imm\<langle>1\<rangle> := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64)) (Stmt (IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) (Stmt (jmp (offset \<Colon> 64)) Empty)) Empty))\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
proof (cases \<open>cond = 0\<close>)
  case True
  show ?thesis 
    apply (rule disjI1)
    apply (insert assms True, solve_prog decoder: decode_beqz)
    apply simp
    apply solve_exps
    apply solve_bil
    apply (intro conjI disjI1)
    apply solve_exps
    by solve_bil
next
  case False
  show ?thesis 
    apply (rule disjI2)
    apply (insert assms False, solve_prog decoder: decode_beqz)
    apply simp
    apply solve_exps
    apply solve_bil
    apply (intro conjI disjI2)
    apply solve_exps
    by blast+
qed
  
subsection \<open>LD\<close>

lemma step_ld:
  assumes decode_ld: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) (Stmt ((rd :\<^sub>t imm\<langle>64\<rangle>) := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64)) Empty)\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr + imm) mod 18446744073709551616 \<Colon> 64, el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> ptr \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_prog decoder: decode_ld)
  by simp

subsection \<open>J\<close>

lemma step_j:
  assumes decode_j: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) (Stmt (jmp (offset \<Colon> 64)) Empty)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (offset \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_j)

subsection \<open>RISC V auto solver\<close>

method solve_decode uses decoder = (insert decoder, (unfold syntax_simps)?, assumption)[1]

method solve_risc_v uses decoder = (
    (rule step_ld, solve_decode decoder: decoder, (solve_in_var, solve_in_var)?)
  | (rule step_beqz, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_lw, solve_decode decoder: decoder, (solve_in_var, solve_in_var)?)
  | (rule step_mv, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_jal, solve_decode decoder: decoder)
  | (rule step_li, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_sd, solve_decode decoder: decoder, (solve_in_var, solve_in_var, solve_in_var)?)
  | (rule step_addi, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_j, solve_decode decoder: decoder)
)
(*
  \<comment> \<open>If all else fails, use the conventional solver\<close>    
  | solve_prog decoder: decoder
*)

end





end
