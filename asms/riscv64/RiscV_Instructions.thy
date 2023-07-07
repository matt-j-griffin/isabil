theory RiscV_Instructions
  imports "../../../isabil/extras/Additional_Program_Semantics"
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
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [rd := (BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (AOp Plus) (imm \<Colon> 64))]\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val + imm) mod 2 ^ 64 \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_addi)

subsubsection \<open>ADDIW\<close>

subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>


lemma step_sextw: 
  assumes decode_sextw: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [rd := extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>)]]]\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> take_bit 32 val \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_prog decoder: decode_sextw)
  unfolding xtract.simps apply simp
  apply solve_exps
  unfolding sxtract.simps by simp

subsubsection \<open>SD\<close>

lemma step_sd:
  assumes decode_sd: \<open>\<And>\<Delta> var. (\<Delta>, (address \<Colon> 64), var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage64 mem' ((mem_addr + imm) mod 2 ^ 64) 64 val), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_sd)

subsection \<open>AUIPC\<close>

lemma step_auipc:
  assumes decode_auipc: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [rd := (imm \<Colon> 64)]\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_prog decoder: decode_auipc)

subsubsection \<open>LI\<close>

lemma step_li:
  assumes decode_li: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [rd := (imm \<Colon> 64)]\<close>
    shows \<open>(\<Delta>, address \<Colon> 64, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_prog decoder: decode_li)

subsubsection \<open>JAL\<close>

lemma step_jal: 
  assumes decode_jal:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_jal)

subsubsection \<open>JALR\<close>
 
lemma step_jalr: 
  assumes decode_jalr:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_jalr)

subsubsection \<open>C.MV\<close>

text \<open>Expansion of add rd, x0, rs2\<close>

lemma step_mv: 
  assumes decode_mv:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>)]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog decoder: decode_mv)

subsection \<open>LW\<close>

lemma step_lw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [(rd :\<^sub>t imm\<langle>64\<rangle>) := extend:64[mem[BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (AOp Plus) (imm \<Colon> 64), el]:u32]]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<And>\<Delta>. \<Delta> \<turnstile> extend:64[Val mem'[(mem_addr + imm) mod 2 ^ 64 \<Colon> 64, el]:u32] \<leadsto>* val \<Colon> 64\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((rd :\<^sub>t imm\<langle>64\<rangle>) \<mapsto> (val \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-4))
  apply (solve_prog decoder: decode_lw)
  by (rule load)

subsection \<open>SW\<close>

lemma step_sw: 
  assumes decode_sw:  \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [mem := mem with [BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (AOp Plus) (imm \<Colon> 64), el]:u32 \<leftarrow> low:32[(rs2 :\<^sub>t imm\<langle>64\<rangle>)]]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage32 mem' ((mem_addr + imm) mod 18446744073709551616) (take_bit 32 val)), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_prog decoder: decode_sw)
  unfolding xtract.simps(1)[of val] apply simp
  by solve_exps

subsection \<open>BEQZ\<close>

lemma step_beqz:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [temp :\<^sub>t imm\<langle>1\<rangle> := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64), IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<close>
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
    apply solve_exp
    apply simp
    apply solve_exps
    apply solve_bil
    apply (intro conjI disjI2 impI)
    apply solve_exps
    apply solve_bil
    by blast+
qed
  
subsection \<open>LD\<close>

lemma step_ld:
  assumes decode_ld: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [rd := (mem[BinOp(rs1 :\<^sub>t imm\<langle>64\<rangle>) (AOp Plus) (imm \<Colon> 64), el]:u64)]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr + imm) mod 2 ^ 64 \<Colon> 64, el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_prog decoder: decode_ld)
  by simp

subsection \<open>C.LD\<close>

lemma step_cld:
  assumes decode_cld: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [rd := (mem[BinOp(rs1 :\<^sub>t imm\<langle>64\<rangle>) (AOp Plus) (imm \<Colon> 64), el]:u64)]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr + imm) mod 2 ^ 64 \<Colon> 64, el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  apply (solve_prog decoder: decode_cld)
  by simp

subsection \<open>J\<close>

lemma step_j:
  assumes decode_j: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [jmp (offset \<Colon> 64)]\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (offset \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_j)

subsection \<open>NOP\<close>

lemma step_nop:
  assumes decode_nop: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) []\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_nop)

subsection \<open>LUI\<close>

lemma step_lui:
  assumes decode_lui: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (2 \<Colon> 64) [rd := (imm \<Colon> 64)]\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (imm \<Colon> 64)), (address \<Colon> 64) +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog decoder: decode_lui)

subsection \<open>BGE\<close>

(* address + offset *)
lemma step_bge_true:
  assumes decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [(ivar :\<^sub>t imm\<langle>1\<rangle>) := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Le) (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (ivar :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms, solve_prog decoder: decode_bge)
  apply (intro disjI1 conjI)
  apply (simp_all del: bv_le.simps)
  apply solve_exps
  by solve_bil

lemma step_bge_false:
  assumes decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, address \<Colon> 64, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l make (address \<Colon> 64) (4 \<Colon> 64) [(ivar :\<^sub>t imm\<langle>1\<rangle>) := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Le) (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (ivar :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, (address \<Colon> 64), var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), ((address + 4) mod 18446744073709551616 \<Colon> 64), var)\<close>
  apply (insert assms, solve_prog decoder: decode_bge)
  apply (intro disjI2 conjI)
  apply (simp_all del: bv_le.simps)
  apply solve_exps
  by solve_bil


subsection \<open>RISC V auto solver\<close>

method solve_decode uses decoder = (insert decoder, (unfold syntax_simps)?, assumption)[1]

method solve_risc_v uses decoder = (
    (rule step_ld, solve_decode decoder: decoder, (solve_in_var, solve_in_var)?)
  | (rule step_beqz, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_lw, solve_decode decoder: decoder, (solve_in_var, solve_in_var)?)
  | (rule step_mv, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_jal, solve_decode decoder: decoder)
  | (rule step_auipc, solve_decode decoder: decoder) \<comment> \<open>step_li\<close>
  | (rule step_sd, solve_decode decoder: decoder, (solve_in_var, solve_in_var, solve_in_var)?)
  | (rule step_addi, solve_decode decoder: decoder, solve_in_var?)
  | (rule step_j, solve_decode decoder: decoder)
  | (rule step_sextw, solve_decode decoder: decoder)

  \<comment> \<open>If all else fails, use the conventional solver\<close>    
  | solve_prog decoder: decoder
)

end





end
