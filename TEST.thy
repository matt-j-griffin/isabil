theory TEST
  imports Main
begin

(*if 0 = 1 then true else (error "foo");
*)
ML \<open>
32 + 3;
writeln "any string";
writeln (@{make_string} 1);
val pretty_term = Syntax.pretty_term;
val pwriteln = Pretty.writeln;
pwriteln (pretty_term @{context} @{term "1::nat"});

fun pretty_terms ctxt trms =
  Pretty.block (Pretty.commas (map (pretty_term ctxt) trms));

val show_types_ctxt = Config.put show_types true @{context};
pwriteln (pretty_term show_types_ctxt @{term "(1::nat, x)"});

fun pretty_cterm ctxt ctrm =
  pretty_term ctxt (Thm.term_of ctrm);

fun pretty_cterms ctxt ctrms =
  Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))

fun pretty_thm ctxt thm =
  pretty_term ctxt (Thm.prop_of thm);

pwriteln (pretty_thm @{context} @{thm conjI});

fun pretty_thm_no_vars ctxt thm =
let
val ctxt' = Config.put show_question_marks false ctxt
in
pretty_term ctxt' (Thm.prop_of thm)
end;

pwriteln (pretty_thm_no_vars @{context} @{thm conjI});


\<close>



end