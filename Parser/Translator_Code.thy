theory Translator_Code
  imports Parser_Code
begin


text \<open>Lemmas which tidy the mess left by the translator\<close>

lemma bool_simps: \<open>Immediate false = false\<close> \<open>Immediate true = true\<close> \<open>Val false = false\<close> \<open>Val true = true\<close>
  unfolding true_word false_word word_constructor_exp_def by auto

lemmas syntax_simps = plus_exp_def[symmetric]   minus_exp_def[symmetric]  
    divide_exp_def[symmetric]  modulo_exp_def[symmetric] times_exp_def[symmetric]
    lsr_exp_def[symmetric]     lsl_exp_def[symmetric]    asr_exp_def[symmetric] 
    land_exp_def[symmetric]    lor_exp_def[symmetric]    xor_exp_def[symmetric]
    sdivide_exp_def[symmetric] smod_exp_def[symmetric]   negation_exp_def[symmetric]
    lt_exp_def[symmetric]      le_exp_def[symmetric]   slt_exp_def[symmetric]
    sle_exp_def[symmetric]   uminus_exp_def[symmetric]
    BIL_Syntax.not_exp.simps[symmetric] Word_simp insn.defs
    var_constructor_var_def[symmetric] var_constructor_exp_def[symmetric]
    Immediate_simp Val_simp_word Val_simp_storage Val_simp_unknown
    false_word[symmetric] true_word[symmetric] bool_simps
    unknown_constructor_val_def[symmetric]

ML_file \<open>ml/isabil.ML\<close>

end
