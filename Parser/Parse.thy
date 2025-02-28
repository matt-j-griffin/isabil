theory Parse   
  imports Translator_Code

  keywords "BIL" :: thy_decl
       and "BIL_file" :: thy_load
       and "defining" "with_subroutines" :: quasi_command
begin

text\<open>
  The attribute ``BIL\_include\_asm'' (default \<copyright>{value "False"}) defines whether to include the 
  original assembly instructions in the generated locale.
\<close>

ML\<open>
  val bil_include_asm = let
    val (bil_include_asm_config, bil_include_asm_setup) =
      Attrib.config_bool (Binding.name "BIL_include_asm") (K false)
  in
    Context.>>(Context.map_theory bil_include_asm_setup);
    bil_include_asm_config
  end
\<close>

ML_file \<open>ml/bil_adt_parser.ML\<close>
(*ML_file \<open>test.ML\<close>*)

text \<open>BIL Parse, adds commands to parse BIR from strings (with BIR) or from files (with BIR_file)\<close>

ML \<open>

val _ =
    Outer_Syntax.local_theory
      \<^command_keyword>\<open>BIL\<close>
      "Generate a locale from a list of BIL instructions."
      ((Parse.embedded -- \<^keyword>\<open>defining\<close> -- Parse.name
          -- Scan.option (\<^keyword>\<open>with_subroutines\<close> -- (Parse.and_list1 Parse.name))) >> 
        (fn (((bil,_),name),wsubs) => 
          let
            val subroutines = Option.getOpt (Option.map snd wsubs, [])
          in 
            bil_parser name bil subroutines
          end
        )
      )

val _ =
    Outer_Syntax.command
      \<^command_keyword>\<open>BIL_file\<close>
      "Generate a locale from a BIL file."
      ((Resources.parse_file -- \<^keyword>\<open>defining\<close> -- Parse.name
          -- Scan.option (\<^keyword>\<open>with_subroutines\<close> -- (Parse.and_list1 Parse.name))) >>
         (fn (((file,_),name),wsubs) =>
           let
             val subroutines = Option.getOpt (Option.map snd wsubs, [])
           in 
             Toplevel.theory (bil_file_parser name file subroutines)
           end
         )
      )
\<close>

end
