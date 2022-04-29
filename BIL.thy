theory BIL
  imports Program_Model
begin

lemma \<Gamma>_val_type_implies_type_t:
  assumes \<open>\<Gamma> \<turnstile> v :: t\<close>
    shows \<open>type v = t\<close>
  using assms by (induct rule: typing_expression_val_induct, auto)


(* TODO hide consts etc... here *)

end