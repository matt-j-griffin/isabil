theory Translator_Code
  imports Parser_Code
begin


text \<open>Lemmas which tidy the mess left by the translator\<close>

lemmas syntax_simps = plus_exp.simps[symmetric]   minus_exp.simps[symmetric]  
    divide_exp.simps[symmetric]  modulo_exp.simps[symmetric] times_exp.simps[symmetric]
    lsr_exp.simps[symmetric]     lsl_exp.simps[symmetric]    asr_exp.simps[symmetric] 
    land_exp.simps[symmetric]    lor_exp.simps[symmetric]    xor_exp.simps[symmetric]
    sdivide_exp.simps[symmetric] smod_exp.simps[symmetric]   negation_exp.simps[symmetric]
    lt_exp.simps[symmetric]      le_exp.simps[symmetric]   slt_exp.simps[symmetric]
    sle_exp.simps[symmetric]   uminus_exp.simps[symmetric]
    BIL_Syntax.not_exp.simps[symmetric] Word_simp insn.defs
    var_constructor_var_def[symmetric] var_constructor_exp_def[symmetric]
    Immediate_simp Val_simp_word Val_simp_storage Val_simp_unknown

ML_file \<open>ml/isabil.ml\<close>


end