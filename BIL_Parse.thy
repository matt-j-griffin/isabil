theory BIL_Parse
  imports Program_Model
  keywords "BIL" :: thy_decl
       and "BIL_file" :: thy_load
begin

ML_file \<open>ml/common.ml\<close>
ML_file \<open>ml/isabil.ml\<close>
ML_file \<open>ml/bil_parser.ml\<close>
ML_file \<open>ml/bil_adt_parser.ml\<close>

text \<open>BIL Parse, adds commands to parse BIR from strings (with BIR) or from files (with BIR_file)\<close>

lemma \<open>insn.make (0 \<Colon> 0) (0 \<Colon> 0) Empty = no_insn\<close>
  unfolding make_def by auto

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

end
