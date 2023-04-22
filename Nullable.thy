theory Nullable
  imports Main
begin

class nullable =
  fixes null :: \<open>'a\<close> (\<open>\<bottom>\<close>)

text \<open>Options are nullable if they have to value\<close>

instantiation option :: (type) nullable
begin

definition
  null_option :: \<open>'a option\<close>
where
  \<open>\<bottom> \<equiv> None\<close>

instance ..

end

end