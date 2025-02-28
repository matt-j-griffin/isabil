theory RiscV_Instruction_Elims
  imports RiscV_Instructions
          IsaBIL.Program_Elims
          RiscV_64
          "IsaBIL-Ex.Mem64_Elims"
begin

section \<open>RISC-V Instructions\<close>

text \<open>
  Semantics for the most common RISC-V instructions.

  This is an incomplete subset of the RISC instructions, anything not on this list can be solved 
  with solve_bil instead.
\<close>

(*
ld
*)

context bil_syntax
begin
(*
subsubsection \<open>SLLIW\<close>

lemma step_slli':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l slli' sz w rd rs1 imm\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) <<\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>

  using step var_in apply -
  apply (solve_prog_mem64E decoder: decode)
  apply (erule step_progE)
  apply (rule decode)
  apply solve_bilE

  
  by (insert assms(2-), solve_prog_mem64E decoder: decode)

subsubsection \<open>SRLIW\<close>

lemma step_srliw:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l srliw w rd rs1 imm\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>

  by (insert assms(2-), solve_prog_mem64E decoder: decode)

subsubsection \<open>AND\<close>

lemma step_and:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l and w rd rs1 rs2\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) &\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode)

subsubsection \<open>OR\<close>

lemma step_or:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l or w rd rs1 rs2\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, val2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val1 \<Colon> 64) |\<^sub>b\<^sub>v (val2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode)
*)
subsubsection \<open>ADD\<close>
(*
lemma step_add:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l add w rd rs1 rs2\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, imm \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode)
*)

lemma step_addiE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addi' sz pc rd rs1 imm\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
  obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

(*
subsubsection \<open>ADDIW\<close>

lemma step_addiw:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l addiw w rd rs1 imm\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext ((val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_caddiw:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l caddiw w rd rs1 imm\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext ((val \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

subsubsection \<open>SUB\<close>

lemma Val_minus: \<open>Val ((num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)) = (num1 \<Colon> sz) -\<^sub>b\<^sub>v (num2 \<Colon> sz)\<close> (* TODO *)
  by (metis bv_minus.simps(1) word_constructor_exp_def)

lemma step_sub:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sub w rd rs1 rs2\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (num1 \<Colon> 64) -\<^sub>b\<^sub>v (num2 \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode)

lemma step_csub:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l csub w rd rs1 rs2\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(rs2 :\<^sub>t imm\<langle>64\<rangle>, num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (num1 \<Colon> 64) -\<^sub>b\<^sub>v (num2 \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode)

subsubsection \<open>SEXT.W\<close>

text \<open>Pseudonym for ADDIW when imm = 0.\<close>

lemma step_sextw':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_sextw: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sextw' sz w rd rs1\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (ext (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0) \<sim> hi : 64 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode_sextw)

lemmas step_sextw = step_sextw'[where sz = 4]
lemmas step_csextw = step_sextw'[where sz = 2]
*)
subsubsection \<open>SD\<close>

lemma step_sdE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd' sz pc rs1 imm rs2\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
  obtains (minor) \<open>\<Delta>' = \<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (val \<Colon> 64))\<close>
                  \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

lemmas step_sdE = step_sdE'[where sz = 4]
lemmas step_csdE = step_sdE'[where sz = 2]

lemma step_sdzeroE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sdzero' sz pc rs1 imm\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> 
                  \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
  obtains (minor) \<open>\<Delta>' = \<Delta>(mem \<mapsto> storage_el64 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 64))\<close>
                  \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)


(*
lemma step_sd0:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0 w rs1 rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_sd0zero':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sd0zero' sz w rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el64 mem' (mem_addr \<Colon> 64) (0 \<Colon> 64)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

subsubsection \<open>AUIPC\<close>

lemma step_auipc:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_auipc: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l auipc w rd imm\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> imm \<Colon> 64), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms)
  by (solve_prog_mem64E decoder: decode_auipc)

subsubsection \<open>LI\<close>
*)

lemma step_liE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l li' sz pc rd imm\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> imm \<Colon> 64)\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>

  using major apply -
  by (solve_prog_mem64E decoder: decode)

subsubsection \<open>JAL\<close>

lemma step_jalE: 
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jal pc retu target\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(X1 \<mapsto> (retu \<Colon> 64))\<close> \<open>pc' = (target \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply - 
  by (solve_prog_mem64E decoder: decode)

subsubsection \<open>JALR\<close>

lemma step_jalrE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l jalr' sz pc rs1 retu target\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>rs1 \<noteq> ''X6''\<close>
  obtains (minor) \<open>\<Delta>' = \<Delta>(X6 \<mapsto> (retu \<Colon> 64))\<close> \<open>pc' = ((val \<Colon> 64) +\<^sub>b\<^sub>v (target \<Colon> 64))\<close> \<open>var' = var\<close>

  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

subsubsection \<open>MV\<close>

lemma step_mvE:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l mv pc rd rs1\<close>
      and var_in: \<open>(rs1 :\<^sub>t imm\<langle>64\<rangle>, val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (2 \<Colon> 64)\<close> \<open>var' = var\<close>

  using major apply -
  apply (solve_prog_mem64E decoder: decode add: var_in)
  by simp

subsubsection \<open>LW\<close>

lemma step_lwE: 
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw pc rd rs1 imm\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
  obtains (minor) v where \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32] \<leadsto>* Val v\<close> 
                  \<open>\<Delta>' = \<Delta>(rd \<mapsto> v)\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

(*
lemma step_lw0: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l lw0 w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64E decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

lemma step_clw: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l clw w rd rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64E decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

lemma step_clw0: 
  assumes decode_lw:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l clw0 w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> extend:64[(Val mem')[(mem_addr \<Colon> 64), el]:u32] \<leadsto>* (val \<Colon> 64)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (val \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64E decoder: decode_lw)
  unfolding Val_simp_word by (rule load)

subsubsection \<open>SW\<close>

lemma step_sw':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw' sz w rs1 imm rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_sw0': 
  assumes decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0' sz w rs1 rs2\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), val \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (ext val \<Colon> 64 \<sim> hi : 32 - 1 \<sim> lo : 0)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_swzero':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l swzero' sz w rs1 imm\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' ((mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64)) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_sw0zero':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode:  \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l sw0zero' sz w rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), mem_addr \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>type mem' = mem\<langle>64, 8\<rangle>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(mem \<mapsto> storage_el32 mem' (mem_addr \<Colon> 64) (0 \<Colon> 32)), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

subsubsection \<open>BEQ\<close>

lemma step_beq_true:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode) 

lemma step_beq_false:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>num1 \<noteq> num2\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  apply (insert assms(2-))
  by (solve_prog_mem64E decoder: decode)

lemma step_beq:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beq w temp rs1 rs2 offset\<close>
      and in_vars: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
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
*)
subsubsection \<open>BEQZ\<close>
(*
lemma step_beqz_true:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>cond = 0\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true), (offset \<Colon> 64), var)\<close>
  apply (insert assms(2), unfold assms(3))
  by (solve_prog_mem64E decoder: decode_beqz)
  
lemma step_beqz_false:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_beqz: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz w temp rs1 offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>cond \<noteq> 0\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (insert assms(2-), solve_prog_mem64E decoder: decode_beqz)
*)

lemma step_beqzE:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l beqz' sz pc temp rs1 offset\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), cond \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
  obtains (true) \<open>\<Delta>' = \<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> true)\<close> \<open>pc' = (offset \<Colon> 64)\<close> \<open>var' = var\<close>
      | (false) \<open>\<Delta>' = \<Delta>((temp :\<^sub>t imm\<langle>Suc 0\<rangle>) \<mapsto> false)\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>
  using major var_in apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

subsubsection \<open>LD\<close>

lemma step_ldE':  
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld' sz pc rd rs1 imm\<close>
      and var_in: \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
  obtains (minor) v where \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64) +\<^sub>b\<^sub>v (imm \<Colon> 64), el]:u64 \<leadsto>* (Val v)\<close> \<open>
          \<Delta>' = \<Delta>(rd \<mapsto> v)\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (sz \<Colon> 64)\<close> \<open>var' = var\<close>

  using major apply -
  by (solve_prog_mem64E decoder: decode add: var_in)

  (*
lemma step_ld0':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ld0' sz w rd rs1\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), (mem_addr \<Colon> 64)) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>(mem, mem') \<in>\<^sub>\<Delta> \<Delta>\<close>
      and load: \<open>\<Delta> \<turnstile> (Val mem')[(mem_addr \<Colon> 64), el]:u64 \<leadsto>* (ptr \<Colon> 64)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> ptr \<Colon> 64), w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  apply (insert assms(2-3))
  apply (solve_prog_mem64E decoder: decode)
  unfolding Val_simp_word by (rule load)
*)
subsubsection \<open>J\<close>

lemma step_jE:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l j pc imm\<close>
  obtains (minor) \<open>\<Delta>' = \<Delta>\<close> \<open>pc' = (imm \<Colon> 64)\<close> \<open>var' = var\<close>
  using major apply -
  by (solve_prog_mem64E decoder: decode)

(*
subsubsection \<open>NOP\<close>

lemma step_nop':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_nop: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l nop' sz w\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
   shows R \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>, w +\<^sub>b\<^sub>v (sz \<Colon> 64), var)\<close>
  by (solve_prog_mem64E decoder: decode_nop)

subsubsection \<open>LUI\<close>

lemma step_lui:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_lui: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l \<lparr> addr = w, size = (2 \<Colon> 64), code = [rd := (imm \<Colon> 64)]\<rparr>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(rd \<mapsto> (imm \<Colon> 64)), w +\<^sub>b\<^sub>v (2 \<Colon> 64), var)\<close>
  by (solve_prog_mem64E decoder: decode_lui)

subsubsection \<open>BGE\<close>

(* address + offset *)
lemma step_bge_true:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E add: leq decoder: decode)

lemma step_bge_false:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode_bge: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bge w rs1 rs2 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and leq: \<open>(num1 \<Colon> 64) \<le>\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), w +\<^sub>b\<^sub>v (4 \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E add: leq decoder: decode_bge)

subsubsection \<open>BNEZ\<close>

lemma step_bnez_true:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) =\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::val)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (2 \<Colon> 64)), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E decoder: decode)

lemma step_bnez_false:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bnez w rs1 ivar offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and \<open>(num1 \<Colon> 64) \<noteq>\<^sub>b\<^sub>v (0 \<Colon> 64) = (true::word)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(ivar :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E decoder: decode)

subsubsection \<open>BLTU\<close>

lemma step_bltu_true:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (true::val)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E decoder: decode add: nez)

lemma step_bltu_false:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      and nez: \<open>(num1 \<Colon> 64) <\<^sub>b\<^sub>v (num2 \<Colon> 64) = (false::val)\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (4 \<Colon> 64)), var)\<close>
  by (insert assms(2-3), solve_prog_mem64E decoder: decode add: nez)

lemma step_bltu:
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l bltu w rs1 rs2 temp offset\<close>
      and \<open>((rs1 :\<^sub>t imm\<langle>64\<rangle>), num1 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close> and \<open>((rs2 :\<^sub>t imm\<langle>64\<rangle>), num2 \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>(rd \<mapsto> (val \<Colon> 64) >>\<^sub>b\<^sub>v (imm \<Colon> 64))\<close> \<open>pc' = pc +\<^sub>b\<^sub>v (4 \<Colon> 64)\<close> \<open>var' = var\<close>
 \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> true), (offset \<Colon> 64), var) \<or> (\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>(temp :\<^sub>t imm\<langle>Suc 0\<rangle> \<mapsto> false), (w +\<^sub>b\<^sub>v (4 \<Colon> 64)), var)\<close>
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
*)

subsubsection \<open>RET\<close>

lemma step_retE':
  assumes major: \<open>(\<Delta>, pc, var) \<leadsto>\<^sub>b\<^sub>i\<^sub>l (\<Delta>', pc', var')\<close>
      and decode: \<open>\<And>\<Delta> var. (\<Delta>, pc, var) \<mapsto>\<^sub>b\<^sub>i\<^sub>l ret' sz pc\<close>
      and in_vars: \<open>(X1, return \<Colon> 64) \<in>\<^sub>\<Delta> \<Delta>\<close>
      obtains (minor) \<open>\<Delta>' = \<Delta>\<close> \<open>pc' = (return \<Colon> 64)\<close> \<open>var' = var\<close>

  using major apply -
  by (solve_prog_mem64E decoder: decode add: in_vars)

end

end
