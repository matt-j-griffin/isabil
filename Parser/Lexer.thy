theory Lexer
  imports "../OperationalSemantics/Program_Model" 
          "../Prelims/Result" 
          "../Prelims/AST_Prelims"
    
begin

abbreviation \<open>isnt_lbracket x \<equiv> (x \<noteq> CHR ''('')\<close>

function
  lexer :: \<open>string \<Rightarrow> AST\<close>
where
  \<open>lexer str = (
    let 
      tstr = trim str;
      name = takeWhile isnt_lbracket tstr;
      bargstr = dropWhile isnt_lbracket tstr;
      argstr = butlast (tl bargstr)
    in
      Node name (map lexer (split_not_within argstr))
  )\<close>
  by auto
termination apply standard
  apply (rule wf_mlex[of \<open>{}\<close> length])
  apply (auto simp del: split_not_within.simps)
  apply (rule mlex_less)
  subgoal for str xd
    apply (cases str, simp)
    apply (drule length_split_not_within, auto)
    by (smt (verit, ccfv_SIG) One_nat_def diff_Suc_eq_diff_pred diff_is_0_eq' diff_less leD leI le_trans length_append_singleton length_dropWhile_le length_rev linordered_nonzero_semiring_class.zero_le_one zero_less_Suc)
  .

end
