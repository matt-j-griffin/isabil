theory RiscV_Instructions
  imports "../../../isabil/OperationalSemantics/Program_Intros"
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
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)] \<rparr>\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_progI decoder: decode_addi)

subsubsection \<open>ADDIW\<close>

subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>

lemma step_sextw: 
  assumes decode_sextw: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [rd := extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>)]]]\<rparr>\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_progI decoder: decode_sextw)

subsubsection \<open>SD\<close>

lemma step_sd:
  assumes decode_sd: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_progI decoder: decode_sd)
  unfolding Val_simp_storage
  by (rule step_exps_store_word64_elI.val.bv_plus.word, standard, solve_typeI)

subsection \<open>AUIPC\<close>

lemma step_auipc:
  assumes decode_auipc: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_progI decoder: decode_auipc)

subsubsection \<open>LI\<close>

lemma step_li:
  assumes decode_li: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_progI decoder: decode_li)

subsubsection \<open>JAL\<close>

lemma step_jal: 
  assumes decode_jal:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_progI decoder: decode_jal)

subsubsection \<open>JALR\<close>
 
lemma step_jalr: 
  assumes decode_jalr:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_progI decoder: decode_jalr)

subsubsection \<open>C.MV\<close>

text \<open>Expansion of add rd, x0, rs2\<close>

lemma step_mv: 
  assumes decode_mv:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>)]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_progI decoder: decode_mv)

subsection \<open>LW\<close>

lemma step_lw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [(rd :\<^sub>t imm\<langle>64\<rangle>) := extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32]]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<And>\<Delta>. \<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_progI decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

subsection \<open>SW\<close>

lemma step_sw: 
  assumes decode_sw:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [mem := mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32 \<leftarrow> low:32[(rs2 :\<^sub>t imm\<langle>64\<rangle>)]]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage32 mem' ((mem_addr + imm) mod 18446744073709551616) 64 (take_bit 32 val)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_progI decoder: decode_sw)
  oops (* store32 *)

  subsection \<open>BEQZ\<close>

lemma step_beqz:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>1\<rangle> := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64), IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
proof (cases \<open>cond = 0\<close>)
  case True
  show ?thesis 
    apply (rule disjI1)
    apply (insert assms(2-), unfold True)
    by (solve_progI decoder: decode_beqz)
next
  case False
  show ?thesis 
    apply (rule disjI2)
    by (insert assms(2-) False, solve_progI decoder: decode_beqz)
qed
  
subsection \<open>LD\<close>

lemma step_ld:
  assumes decode_ld: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64)]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_progI decoder: decode_ld)
  unfolding Val_simp_word by (rule load)

subsection \<open>C.LD\<close>

lemma step_cld:
  assumes decode_cld: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64)]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_progI decoder: decode_cld)
  unfolding Val_simp_word by (rule load)

subsection \<open>J\<close>

lemma step_j:
  assumes decode_j: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [jmp (offset \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (offset \<Colon> 64), var)\<close>
  by (solve_progI decoder: decode_j)

subsection \<open>NOP\<close>

lemma step_nop:
  assumes decode_nop: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = []\<rparr>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_progI decoder: decode_nop)

subsection \<open>LUI\<close>

lemma step_lui:
  assumes decode_lui: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (imm \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_progI decoder: decode_lui)

subsection \<open>BGE\<close>

(* address + offset *)
lemma step_bge_true:
  assumes decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [(ivar :\<^sub>t imm\<langle>1\<rangle>) := (rs1 :\<^sub>t imm\<langle>64\<rangle>) le (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (ivar :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms(2-3), solve_progI decoder: decode_bge)
  unfolding leq by solve_bilI

lemma step_bge_false:
  assumes decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = (address \<Colon> 64), size = (4 \<Colon> 64), code = [(ivar :\<^sub>t imm\<langle>1\<rangle>) := (rs1 :\<^sub>t imm\<langle>64\<rangle>) le (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (ivar :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_progI decoder: decode_bge)


subsection \<open>RISC V auto solver\<close>

method solve_riscvI uses decoder = (
    (rule step_ld, rule decoder, (solve_in_var, solve_in_var)?)
  | (rule step_beqz, rule decoder, solve_in_var?)
  | (rule step_lw, rule decoder, (solve_in_var, solve_in_var)?)
  | (rule step_mv, rule decoder, solve_in_var?)
  | (rule step_jal, rule decoder)
  | (rule step_auipc, rule decoder) \<comment> \<open>step_li\<close>
  | (rule step_sd, rule decoder, (solve_in_var, solve_in_var, solve_in_var)?)
  | (rule step_addi, rule decoder, solve_in_var?)
  | (rule step_j, rule decoder)
  | (rule step_sextw, rule decoder)
)

end

end
