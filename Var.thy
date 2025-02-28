theory Var
  imports HOL.String 
          "Typing/Typing_Type" 
begin

datatype var = Var (var_name: string) Type

\<comment> \<open>Var Syntax - can be applied to any type\<close>

class var_syntax =
    fixes var_constructor :: \<open>string \<Rightarrow> Type \<Rightarrow> 'a\<close> (infixl \<open>:\<^sub>t\<close> 151)
    assumes var_eq[simp]: \<open>\<And>id t id' t'. (id :\<^sub>t t) = (id' :\<^sub>t t') \<longleftrightarrow> id = id' \<and> t = t'\<close>
begin

lemma var_syntax_exhaust:
  obtains 
    (Var) id t where \<open>var = (id :\<^sub>t t)\<close>
  | (NotVar) \<open>\<forall>id t. var \<noteq> (id :\<^sub>t t)\<close>
  by auto

end

\<comment> \<open>Instantiating var\<close>

instantiation var :: var_syntax
begin

definition 
  var_constructor_var :: \<open>string \<Rightarrow> Type \<Rightarrow> var\<close>
where
  \<open>(id' :\<^sub>t t) \<equiv> Var id' t\<close>

instance
  apply standard
  unfolding var_constructor_var_def 
  subgoal by simp
  .

end

lemma var_exhaust[case_names Var]: 
  fixes var :: var
  obtains (Var) id t where \<open>var = (id :\<^sub>t t)\<close>
  apply (rule var.exhaust)
unfolding var_constructor_var_def by auto

lemma var_name_syntax[simp]: \<open>var_name (name :\<^sub>t t) = name\<close>
  by (simp add: var_constructor_var_def)

end
