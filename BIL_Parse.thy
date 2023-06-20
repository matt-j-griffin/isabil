theory BIL_Parse   
  imports "OperationalSemantics/Program_Model"
  keywords "BIL" :: thy_decl
       and "BIL_file" :: thy_load
begin

ML_file \<open>ml/common.ml\<close>
ML_file \<open>ml/isabil.ml\<close>
ML_file \<open>ml/bil_parser.ml\<close>
ML_file \<open>ml/bil_adt_parser.ml\<close>

text \<open>BIL Parse, adds commands to parse BIR from strings (with BIR) or from files (with BIR_file)\<close>

ML \<open>

val _ =
    Outer_Syntax.local_theory
      \<^command_keyword>\<open>BIL\<close>
      "Generate a locale from a list of BIL instructions."
      (Parse.name -- Parse.embedded >> uncurry bil_parser)

val _ =
    Outer_Syntax.command
      \<^command_keyword>\<open>BIL_file\<close>
      "Generate a locale from a BIL file."
      (Parse.name -- Resources.parse_file >> (Toplevel.theory o uncurry bil_file_parser))
\<close>

text \<open>Lemmas which tidy the mess left by the parser\<close>

lemmas syntax_simps = var_simps  plus_exp.simps[symmetric]   minus_exp.simps[symmetric]  
    divide_exp.simps[symmetric]  modulo_exp.simps[symmetric] times_exp.simps[symmetric]
    lsr_exp.simps[symmetric]     lsl_exp.simps[symmetric]    asr_exp.simps[symmetric] 
    land_exp.simps[symmetric]    lor_exp.simps[symmetric]    xor_exp.simps[symmetric]
    sdivide_exp.simps[symmetric] smod_exp.simps[symmetric]   negation_exp.simps[symmetric]
    lt_exp.simps[symmetric]      lteq_exp.simps[symmetric]   slt_exp.simps[symmetric]
    slteq_exp.simps[symmetric]   uminus_exp.simps[symmetric]
    
end
