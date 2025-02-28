theory RiscV_Instruction_Intros
  imports RiscV_Instructions
          IsaBIL.Program_Intros
          RiscV_64
          "IsaBIL-Ex.Mem64_Intros"
begin

section \<open>RISC-V Instructions\<close>

text \<open>
  Semantics for the most common RISC-V instructions.

  This is an incomplete subset of the RISC instructions, anything not on this list can be solved 
  with solve_bil instead.
\<close>

context bil_syntax
begin

subsubsection \<open>SLLIW\<close>

lemma step_slli':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l slli' sz w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) <<\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: assms(2))

subsubsection \<open>SRLIW\<close>

lemma step_srliw:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l srliw w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: assms(2))

subsubsection \<open>AND\<close>

lemma step_and:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l and w rd rs1 rs2\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) &\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

subsubsection \<open>OR\<close>

lemma step_or:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l or w rd rs1 rs2\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) |\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

subsubsection \<open>ADD\<close>

lemma step_add:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l add w rd rs1 rs2\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, imm \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_addi:
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addi w rd rs1 imm\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_addi add: others)

interpretation step_addiI: exp_val_word_fixed_sz_syntax \<open>\<lambda>e v _ _ . (\<And>\<Delta> pc var rd rs imm. \<lbrakk>
  \<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addi pc rd rs imm;
  (rs :\<^sub>t imm\<langle>64\<rangle>, v) \<in>\<^sub>\<Delta> \<Delta>\<rbrakk>
  \<Longrightarrow> (\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> v +\<^sub>b\<^sub>v (imm \<Colon> 64)), pc +\<^sub>b\<^sub>v (4 \<Colon> 64), var))\<close> 64
  apply standard 
  using step_addi by blast

lemma step_caddi:
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l caddi w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_addi add: assms(2))

subsubsection \<open>ADDIW\<close>

lemma step_addiw':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addiw' sz w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext ((val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) \<sim> hi : 31 \<sim> lo : 0) \<sim> hi : 63 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: assms(2))

subsubsection \<open>SUB\<close>

lemma Val_minus: \<open>Val ((num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)) = (num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)\<close> (* TODO *)
  by (metis bv_minus.simps(1) word_constructor_exp_def)

lemma step_sub':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sub' sz w rd rs1 rs2\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (num1 \<Colon> 64) -\<^sub>b\<^sub>v (num2 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)


subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>

lemma step_sextw':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sextw' sz w rd rs1\<close>
      and others: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext val \<Colon> 64 \<sim> hi : 31 \<sim> lo : 0) \<sim> hi : 63 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: assms(2))

lemmas step_sextw = step_sextw'[where sz = 4]
lemmas step_csextw = step_sextw'[where sz = 2]

subsubsection \<open>SD\<close>

lemma step_sd':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd' sz w rs1 imm rs2\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (val \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemmas step_sd = step_sd'[where sz = 4]
lemmas step_csd = step_sd'[where sz = 2]


lemma step_sdzero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sdzero' sz w rs1 imm\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_sd0:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0 w rs1 rs2\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_sd0zero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0zero' sz w rs1\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (0 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

subsubsection \<open>AUIPC\<close>

lemma step_auipc:
  assumes decode_auipc: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l auipc w rd imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_auipc)

subsubsection \<open>LI\<close>

lemma step_li:
  assumes decode_li: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l li' sz w rd imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_li)

subsubsection \<open>JAL\<close>

lemma step_jal: 
  assumes decode_jal:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jal w retu target\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (retu \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_jal)

subsubsection \<open>JALR\<close>

lemma step_jalr':
  assumes decode_jalr:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jalr' sz w rs1 retu target\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>X6 \<noteq> (rs1 :\<^sub>t imm\<langle>64\<rangle>)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X6 \<mapsto> (retu \<Colon> 64)), ((val \<Colon> 64) +\<^sub>b\<^sub>v (target \<Colon> 64)), var)\<close>
  using assms(2-) apply -
  by (solve_prog_mem64I decoder: decode_jalr add: assms(2))

lemma step_cjalr:
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l cjalr w rs1 retu\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>X1 \<noteq> (rs1 :\<^sub>t imm\<langle>64\<rangle>)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (retu \<Colon> 64)), (val \<Colon> 64), var)\<close>
  using assms(2-) apply -
  by (solve_prog_mem64I decoder: decode add: assms(2))

subsubsection \<open>MV\<close>

lemma step_mv: 
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l mv w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>LW\<close>

lemma step_lw': 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw' sz w rd rs1 imm\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32 \<leadsto>* (val \<Colon> 32)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ext (val \<Colon> 32) \<sim> hi : 63 \<sim> lo : 0), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_lw add: others load)

lemma step_lw0: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw0' sz w rd rs1\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64), el]:u32 \<leadsto>* (val \<Colon> 32)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ext (val \<Colon> 32) \<sim> hi : 63 \<sim> lo : 0), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_lw add: others load)

subsubsection \<open>SW\<close>

lemma step_sw':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw' sz w rs1 imm rs2\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (ext val \<Colon> 64 \<sim> hi : 31 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_sw0': 
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0' sz w rs1 rs2\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (ext val \<Colon> 64 \<sim> hi : 31 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_swzero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l swzero' sz w rs1 imm\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

lemma step_sw0zero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0zero' sz w rs1\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others)

subsubsection \<open>BEQ\<close>

lemma step_beq_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others) 

lemma step_beq_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and neq: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
proof -
  have num_neq: \<open>num1 \<noteq> num2\<close>
    using neq unfolding bv_eq_def by (cases \<open>num1 = num2\<close>, auto)
  show ?thesis
    apply (insert assms(2-) num_neq)
    by (solve_prog_mem64I decoder: decode add: others)
qed

lemma step_beq:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
proof (cases \<open>num1 = num2\<close>)
  case True
  show ?thesis 
    apply (rule disjI1)
    using decode in_vars[unfolded True[symmetric]] by (rule step_beq_true)
next
  case False
  hence neq: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    unfolding bv_eq_def by (cases \<open>num1 = num2\<close>, auto)
  show ?thesis 
    apply (rule disjI2)
    using decode in_vars neq by (rule step_beq_false)
qed

subsubsection \<open>BEQZ\<close>

lemma step_beqz_true:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz' sz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
      and cond: \<open>(cond \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
proof -
  have cond: \<open>cond = 0\<close>
    using cond unfolding bv_eq_def by (cases \<open>cond = 0\<close>, auto)
  show ?thesis
    by (solve_prog_mem64I decoder: decode_beqz add: assms(2)[unfolded cond])
qed

lemma step_beqz_false:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz' sz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
      and cond: \<open>(cond \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
proof -
  have cond: \<open>cond \<noteq> 0\<close>
    using cond unfolding bv_eq_def by (cases \<open>cond = 0\<close>, auto)
  show ?thesis
    by (insert cond, solve_prog_mem64I decoder: decode_beqz add: assms(2))
qed

lemma step_beqz:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz' sz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
proof (cases \<open>(cond \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::val)\<close>)
  case True
  show ?thesis 
    using assms True by (intro disjI1 step_beqz_true)
next
  case False
  hence cond: \<open>(cond \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (false::val)\<close>
    unfolding bv_eq_def by (cases \<open>cond = 0\<close>, auto)
  show ?thesis 
    using assms cond by (intro disjI2 step_beqz_false)
qed
  
subsubsection \<open>LD\<close>

lemma step_ld':  
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld' sz w rd rs1 imm\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others load)

lemma step_ld0':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld0' sz w rd rs1\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode add: others load)

subsubsection \<open>J\<close>

lemma step_j:
  assumes decode_j: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l j w imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (imm \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_j)

subsubsection \<open>NOP\<close>

lemma step_nop':
  assumes decode_nop: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l nop' sz w\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_nop)

subsubsection \<open>LUI\<close>

lemma step_lui:
  assumes decode_lui: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_lui)

subsubsection \<open>BGE\<close>

(* address + offset *)
lemma step_bge_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding leq by (solve_bilI add: others)


lemma step_bge_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding leq by (solve_bilI add: others)

subsubsection \<open>BNEZ\<close>

lemma TODO: \<open>true =\<^sub>b\<^sub>v false = (false::val)\<close>
  unfolding bv_eq_def by simp

lemma step_bnez_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (2 \<Colon> 64)), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding nez TODO by solve_bil_mem64I

lemma step_bnez_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and eq: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding eq bv_eq
  by solve_bil_mem64I

subsubsection \<open>BLTU\<close>

lemma step_bltu'_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu' sz w rs1 rs2 temp offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding nez by (solve_bilI add: others)

lemma step_bltu'_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu' sz w rs1 rs2 temp offset\<close>
      and others: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (sz \<Colon> 64)), var)\<close>
  apply (solve_prog_mem64I decoder: decode add: others)
  unfolding nez by (solve_bilI add: others)

lemma step_bltu':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu' sz w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (sz \<Colon> 64)), var)\<close>
proof (cases \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>)
  case True
  show ?thesis 
    using assms True by (intro disjI1 step_bltu'_true)
next
  case False
  have lt_false: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    using False by (meson bv_simps(45))
  show ?thesis 
    using assms lt_false by (intro disjI2 step_bltu'_false)
qed

subsubsection \<open>RET\<close>

lemma step_ret':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ret' sz w\<close>
      and x1_in_vars: \<open>(X1, return \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, return \<Colon> 64, var)\<close>
  by (solve_prog_mem64I decoder: decode add: x1_in_vars)

end

end
