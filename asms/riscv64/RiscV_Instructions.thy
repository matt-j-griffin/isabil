theory RiscV_Instructions
  imports "../../OperationalSemantics/Program_Intros"
          RiscV_64
          "../../extras/Mem64_Intros"
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

abbreviation \<open>slli' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) << (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>slliw \<equiv> slli' 4\<close>

lemma step_slli':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l slli' sz w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) <<\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

subsubsection \<open>SRLIW\<close>

abbreviation \<open>srliw' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) >> (imm \<Colon> 64)] \<rparr>\<close>
abbreviation \<open>srliw \<equiv> srliw' 4\<close>

lemma step_srliw:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l srliw w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

subsubsection \<open>AND\<close>

abbreviation 
  "and" :: \<open>word \<Rightarrow> var \<Rightarrow> string \<Rightarrow> string \<Rightarrow> insn\<close>
where
  \<open>and w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) && (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

lemma step_and:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l and w rd rs1 rs2\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) &\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

subsubsection \<open>OR\<close>

abbreviation 
  "or" :: \<open>word \<Rightarrow> var \<Rightarrow> string \<Rightarrow> string \<Rightarrow> insn\<close>
where
  \<open>or w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) || (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

lemma step_or:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l or w rd rs1 rs2\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) |\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

subsubsection \<open>ADD\<close>

abbreviation \<open>add w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

lemma step_add:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l add w rd rs1 rs2\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, imm \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

abbreviation \<open>addi w rd rs1 imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)] \<rparr>\<close>

lemma step_addi:
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addi w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode_addi)


interpretation step_addiI: exp_val_word_fixed_sz_syntax \<open>\<lambda>e v _ _ . (\<And>\<Delta> pc var rd rs imm. \<lbrakk>
  \<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addi pc rd rs imm;
  (rs :\<^sub>t imm\<langle>64\<rangle>, v) \<in>\<^sub>\<Delta> \<Delta>\<rbrakk>
  \<Longrightarrow> (\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> v +\<^sub>b\<^sub>v (imm \<Colon> 64)), pc +\<^sub>b\<^sub>v (4 \<Colon> 64), var))\<close> 64
  apply standard 
  using step_addi by blast

abbreviation \<open>caddi w rd rs1 imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)] \<rparr>\<close>

lemma step_caddi:
  assumes decode_addi: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l caddi w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode_addi)


subsubsection \<open>ADDIW\<close>

abbreviation \<open>addiw w rd rs1 imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)]]] \<rparr>\<close>

lemma step_addiw:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addiw w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext ((val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

abbreviation \<open>caddiw w rd rs1 imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64)]]] \<rparr>\<close>


lemma step_caddiw:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l caddiw w rd rs1 imm\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext ((val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>SUB\<close>

abbreviation \<open>sub w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) - (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>
abbreviation \<open>csub w rd rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>) - (rs2 :\<^sub>t imm\<langle>64\<rangle>)] \<rparr>\<close>

lemma Val_minus: \<open>Val ((num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)) = (num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)\<close> (* TODO *)
  by (metis bv_minus.simps(1) word_constructor_exp_def)

lemma step_sub:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sub w rd rs1 rs2\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (num1 \<Colon> 64) -\<^sub>b\<^sub>v (num2 \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

lemma step_csub:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l csub w rd rs1 rs2\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (num1 \<Colon> 64) -\<^sub>b\<^sub>v (num2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode)

subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>

abbreviation \<open>sextw w rd rs1 \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>)]])] \<rparr>\<close>

lemma step_sextw:
  assumes decode_sextw: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sextw w rd rs1\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode_sextw)

abbreviation \<open>csextw w rd rs1 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (extend:64[low:32[(rs1 :\<^sub>t imm\<langle>64\<rangle>)]])] \<rparr>\<close>

lemma step_csextw:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l csextw w rd rs1\<close>
      and \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>SD\<close>

abbreviation \<open>sd' sz w rs1 imm rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))] \<rparr>\<close>
abbreviation \<open>sd \<equiv> sd' 4\<close>
abbreviation \<open>csd \<equiv> sd' 2\<close>

lemma step_sd':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd' sz w rs1 imm rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (val \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

lemmas step_sd = step_sd'[where sz = 4]
lemmas step_csd = step_sd'[where sz = 2]

abbreviation \<open>sdzero' sz w rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64 \<leftarrow> (0 \<Colon> 64))] \<rparr>\<close>

lemma step_sdzero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sdzero' sz w rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

abbreviation \<open>sd0 w rs1 rs2 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64 \<leftarrow> (rs2 :\<^sub>t imm\<langle>64\<rangle>))] \<rparr>\<close>

lemma step_sd0:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0 w rs1 rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)


abbreviation \<open>sd0zero' sz w rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64 \<leftarrow> (0 \<Colon> 64))] \<rparr>\<close>

lemma step_sd0zero':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0zero' sz w rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (0 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>AUIPC\<close>

abbreviation \<open>auipc w rd imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>

lemma step_auipc:
  assumes decode_auipc: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l auipc w rd imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_prog_mem64I decoder: decode_auipc)

subsubsection \<open>LI\<close>

abbreviation \<open>li w rd imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>

lemma step_li:
  assumes decode_li: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l li w rd imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_prog_mem64I decoder: decode_li)

subsubsection \<open>JAL\<close>

abbreviation \<open>jal w ret target \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp (target \<Colon> 64)]\<rparr>\<close>

lemma step_jal: 
  assumes decode_jal:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jal w ret target\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (target \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_jal)

subsubsection \<open>JALR\<close>

abbreviation \<open>jalr' sz w rs1 ret target \<equiv>  \<lparr> addr = w, size = (sz \<Colon> 64), code = [X6 := (ret \<Colon> 64), jmp ((rs1 :\<^sub>t imm\<langle>64\<rangle>) + (target \<Colon> 64))]\<rparr>\<close>
abbreviation \<open>jalr \<equiv> jalr' 4\<close>
abbreviation \<open>cjalr w rs1 ret \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [X1 := (ret \<Colon> 64), jmp ((rs1 :\<^sub>t imm\<langle>64\<rangle>))]\<rparr>\<close>

lemma step_jalr':
  assumes decode_jalr:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jalr' sz w rs1 ret target\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>X6 \<noteq> (rs1 :\<^sub>t imm\<langle>64\<rangle>)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X6 \<mapsto> (ret \<Colon> 64)), ((val \<Colon> 64) +\<^sub>b\<^sub>v (target \<Colon> 64)), var)\<close>
  using assms(2-) apply -
  by (solve_prog_mem64I decoder: decode_jalr)

lemma step_cjalr:
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l cjalr w rs1 ret\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>X1 \<noteq> (rs1 :\<^sub>t imm\<langle>64\<rangle>)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(X1 \<mapsto> (ret \<Colon> 64)), (val \<Colon> 64), var)\<close>
  using assms(2-) apply -
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>MV\<close>

abbreviation \<open>mv w rd rs1 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (rs1 :\<^sub>t imm\<langle>64\<rangle>)]\<rparr>\<close>

lemma step_mv: 
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l mv w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>LW\<close>

abbreviation \<open>lw w rd rs1 imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32])]\<rparr>\<close>

lemma step_lw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw w rd rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

abbreviation \<open>lw0 w rd rs1 \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u32])]\<rparr>\<close>

lemma step_lw0: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw0 w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

abbreviation \<open>clw w rd rs1 imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32])]\<rparr>\<close>

lemma step_clw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l clw w rd rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

abbreviation \<open>clw0 w rd rs1 \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (extend:64[mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u32])]\<rparr>\<close>

lemma step_clw0: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l clw0 w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

subsubsection \<open>SW\<close>

abbreviation \<open>sw' sz w rs1 imm rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32 \<leftarrow> (low:32[rs2 :\<^sub>t imm\<langle>64\<rangle>]))]\<rparr>\<close>
abbreviation \<open>sw \<equiv> sw' 4\<close>

lemma step_sw': 
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw' sz w rs1 imm rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

abbreviation \<open>sw0' sz w rs1 rs2 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [rs1 :\<^sub>t imm\<langle>64\<rangle>, el]:u32 \<leftarrow> (low:32[rs2 :\<^sub>t imm\<langle>64\<rangle>]))]\<rparr>\<close>
abbreviation \<open>sw0 \<equiv> sw0' 2\<close>

lemma step_sw0': 
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0' sz w rs1 rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

abbreviation \<open>swzero' sz w rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u32 \<leftarrow> (0 \<Colon> 32))]\<rparr>\<close>

lemma step_swzero':
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l swzero' sz w rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

abbreviation \<open>sw0zero' sz w rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [mem := (mem with [(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u32 \<leftarrow> (0 \<Colon> 32))]\<rparr>\<close>

lemma step_sw0zero':
  assumes decode:  \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0zero' sz w rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

subsubsection \<open>BEQ\<close>

abbreviation \<open>beq w tmp rs1 rs2 offset \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [(tmp :\<^sub>t imm\<langle>1\<rangle>) := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (tmp :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>

lemma step_beq_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode) 

lemma step_beq_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>num1 \<noteq> num2\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64I decoder: decode)

lemma step_beq:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
proof (cases \<open>num1 = num2\<close>)
  case True
  show ?thesis 
    apply (rule disjI1)
    using decode in_vars[unfolded True[symmetric]] by (rule step_beq_true)
next
  case False
  show ?thesis 
    apply (rule disjI2)
    using decode in_vars False by (rule step_beq_false)
qed

subsubsection \<open>BEQZ\<close>

abbreviation \<open>beqz w temp rs1 offset \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>1\<rangle> := BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64), IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp (offset \<Colon> 64)]]\<rparr>\<close>

lemma step_beqz_true:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>cond = 0\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms(2), unfold assms(3))
  by (solve_prog_mem64I decoder: decode_beqz)
  
lemma step_beqz_false:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>cond \<noteq> 0\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64I decoder: decode_beqz)
  
lemma step_beqz:
  assumes decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>1\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
proof (cases \<open>cond = 0\<close>)
  case True
  show ?thesis 
    using assms True by (intro disjI1 step_beqz_true)
next
  case False
  show ?thesis 
    using assms False by (intro disjI2 step_beqz_false)
qed
  
subsubsection \<open>LD\<close>

abbreviation \<open>ld' sz w rd rs1 imm \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>) + (imm \<Colon> 64), el]:u64)]\<rparr>\<close>
abbreviation \<open>ld \<equiv> ld' 4\<close>
abbreviation \<open>cld \<equiv> ld' 2\<close>

abbreviation \<open>ld0' sz w rd rs1 \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [rd := (mem[(rs1 :\<^sub>t imm\<langle>64\<rangle>), el]:u64)]\<rparr>\<close>
abbreviation \<open>ld0 \<equiv> ld0' 4\<close>
abbreviation \<open>cld0 \<equiv> ld0' 2\<close>

lemma step_ld':  
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld' sz w rd rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode)
  unfolding Val_simp_word by (rule load)

lemma step_ld0':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld0' sz w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64I decoder: decode)
  unfolding Val_simp_word by (rule load)

subsubsection \<open>J\<close>

abbreviation \<open>j w imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [jmp (imm \<Colon> 64)]\<rparr>\<close>

lemma step_j:
  assumes decode_j: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l j w imm\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, (imm \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_j)

subsubsection \<open>NOP\<close>

abbreviation \<open>nop' sz w \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = []\<rparr>\<close>
abbreviation \<open>nop \<equiv> nop' 2\<close>

lemma step_nop':
  assumes decode_nop: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l nop' sz w\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_nop)

subsubsection \<open>LUI\<close>

abbreviation \<open>lui w rd imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)] \<rparr>\<close>

lemma step_lui:
  assumes decode_lui: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64I decoder: decode_lui)

subsubsection \<open>BGE\<close>

abbreviation \<open>bge w rs1 rs2 temp imm \<equiv> \<lparr> addr = w, size = (4 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>1\<rangle> := (rs1 :\<^sub>t imm\<langle>64\<rangle>) le (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp imm \<Colon> 64]]\<rparr>\<close>

(* address + offset *)
lemma step_bge_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I add: leq decoder: decode)

lemma step_bge_false:
  assumes decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I add: leq decoder: decode_bge)

subsubsection \<open>BNEZ\<close>

abbreviation \<open>bnez w rs1 temp imm \<equiv> \<lparr> addr = w, size = (2 \<Colon> 64), code = [temp :\<^sub>t imm\<langle>1\<rangle> := BinOp (BinOp (rs1 :\<^sub>t imm\<langle>64\<rangle>) (LOp Eq) (0 \<Colon> 64)) (LOp Eq) false, IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp (imm \<Colon> 64)]]\<rparr>\<close>

lemma step_bnez_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (2 \<Colon> 64)), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I decoder: decode)

lemma step_bnez_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>(num1 \<Colon> 64) \<noteq>\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::word)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I decoder: decode)

subsubsection \<open>BLTU\<close>

abbreviation \<open>bltu w rs1 rs2 temp imm \<equiv>  \<lparr>addr = w, size = 4 \<Colon> 64, code = [temp :\<^sub>t imm\<langle>1\<rangle> := (rs1 :\<^sub>t imm\<langle>64\<rangle>) lt (rs2 :\<^sub>t imm\<langle>64\<rangle>), IfThen (temp :\<^sub>t imm\<langle>1\<rangle>) [jmp (imm \<Colon> 64)]]\<rparr>\<close>

lemma step_bltu_true:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I decoder: decode add: nez)

lemma step_bltu_false:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (4 \<Colon> 64)), var)\<close>
  by (insert assms(2-3), solve_prog_mem64I decoder: decode add: nez)

lemma step_bltu:
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>1\<rangle> \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>1\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (4 \<Colon> 64)), var)\<close>
proof (cases \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>)
  case True
  show ?thesis 
    using assms True by (intro disjI1 step_bltu_true)
next
  case False
  have lt_false: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
    using False by (meson bv_simps(45))
  show ?thesis 
    using assms lt_false by (intro disjI2 step_bltu_false)
qed
  

subsubsection \<open>RET\<close>

abbreviation \<open>ret' sz w \<equiv> \<lparr> addr = w, size = (sz \<Colon> 64), code = [jmp X1]\<rparr>\<close>
abbreviation \<open>ret \<equiv> ret' 2\<close>

lemma step_ret':
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, w, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ret' sz w\<close>
      and x1_in_vars: \<open>(X1, return \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
    shows \<open>(\<Delta>, w, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, return \<Colon> 64, var)\<close>
  by (insert x1_in_vars, solve_prog_mem64I decoder: decode)


subsection \<open>RISC V auto solver\<close>

method solve_riscvI_scaffold methods solve_bil uses decoder = (
  (rule step_ld', rule decoder, (solve_in_var, solve_in_var)?) | 
  (rule step_beqz, rule decoder, solve_in_var?) | 
  (rule step_lw, rule decoder, (solve_in_var, solve_in_var)?) | 
  (rule step_mv, rule decoder, solve_in_var?) | 
  (rule step_jal, rule decoder) |
  (rule step_jalr', rule decoder, solve_in_var?, simp (no_asm)) | 
  (rule step_auipc, rule decoder) \<comment> \<open>step_li\<close> | 
  (rule step_sd, rule decoder, (solve_in_var, solve_in_var, solve_in_var)?) | 
  (rule step_addi, rule decoder, solve_in_var?) | 
  (rule step_j, rule decoder) | 
  (rule step_sextw, rule decoder) |
  (rule step_addiw, rule decoder, solve_in_var) |
  (rule step_caddiw, rule decoder, solve_in_var) |
  (solve_progI_scaffold solve_bil decoder: decoder)
)


method solve_riscvI uses add decoder = (
  solve_riscvI_scaffold \<open>solve_bil_mem64I add: add\<close> decoder: decoder
)

end

end
