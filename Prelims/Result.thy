theory Result
  imports Main
begin


datatype ('v, 'e) result =  Value (get: 'v) | Error (err: 'e)
(*
primrec
  result_of_option :: \<open>'v option \<Rightarrow> 'e \<Rightarrow> ('v, 'e) result\<close>
where
  \<open>result_of_option (Some x) _ = Value x\<close> |   
  \<open>result_of_option None e = Error e\<close>
*)
find_theorems Value

definition \<open>map_result_value f = map_result f id\<close>

lemma map_result_value_simps[simp,code]: 
  \<open>map_result_value f (Value v) = (Value (f v))\<close>
  \<open>map_result_value f (Error e) = (Error e)\<close>
  unfolding map_result_value_def by auto

definition \<open>map_result_error = map_result id\<close>

lemma map_result_error_simps[simp,code]: 
  \<open>map_result_error f (Value v) = (Value v)\<close>
  \<open>map_result_error f (Error e) = (Error (f e))\<close>
  unfolding map_result_error_def by auto



lemma rel_result_iff:
  "rel_result R1 R2 x y = (case (x, y) of (Error e, Error e') \<Rightarrow> R2 e e'
    | (Value v, Value v') \<Rightarrow> R1 v v'
    | _ \<Rightarrow> False)"
  by (auto split: prod.split result.split)

definition is_error :: "('v, 'e) result \<Rightarrow> bool"
  where [code_post]: "is_error x \<longleftrightarrow> \<not> is_Value x"

lemma is_error_simps [simp]:
  "is_error (Error e)"
  "\<not> is_error (Value x)"
  by (simp_all add: is_error_def)

lemma is_error_code [code]:
  "is_error (Error e) = True"
  "is_error (Value x) = False"
  by simp_all

context
begin



lemma rel_result_unfold:
  "rel_result R1 R2 x y \<longleftrightarrow>
   (is_error x \<longleftrightarrow> is_error y) \<and> (\<not> is_error x \<longrightarrow> \<not> is_error y \<longrightarrow> R1 (get x) (get y)) \<and> (is_error x \<longrightarrow> is_error y \<longrightarrow> R2 (err x) (err y))"
  unfolding rel_result_iff case_prod_beta fst_conv snd_conv
  by (auto split: result.split)
  
qualified primrec bind :: "('v, 'e) result \<Rightarrow> ('v \<Rightarrow> ('u, 'e) result) \<Rightarrow> ('u, 'e) result"
where
  bind_lzero: "bind (Error e) _ = (Error e)"
| bind_lunit: "bind (Value x) f = f x"

end

fun map_result_value2 :: "('v \<Rightarrow> 'u \<Rightarrow> 's) \<Rightarrow> ('v, 'e) result \<Rightarrow> ('u, 'e) result \<Rightarrow> ('s, 'e) result"
where
  "map_result_value2 _ (Error e) _ = (Error e)" |
  "map_result_value2 f (Value v) r = (map_result_value (f v) r)"

lemma map_result_value2_inject:
  assumes \<open>\<And>x. f1 x = f2 x\<close> \<open>v11 = v21\<close> \<open>v12 = v22\<close> 
    shows \<open>map_result_value2 f1 v11 v12 = map_result_value2 f2 v21 v22\<close>
  using assms apply auto
  by presburger

fun map_result_value3 :: "('v \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't) \<Rightarrow> ('v, 'e) result \<Rightarrow> ('u, 'e) result \<Rightarrow> ('s, 'e) result \<Rightarrow> ('t, 'e) result"
where
  "map_result_value3 _ (Error e) _ _ = (Error e)" |
  "map_result_value3 f (Value v) u s  = (map_result_value2 (f v) u s)"

fun map_result_value4 :: "('v \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> 'w) \<Rightarrow> ('v, 'e) result \<Rightarrow> ('u, 'e) result \<Rightarrow> ('s, 'e) result \<Rightarrow> ('t, 'e) result \<Rightarrow> ('w, 'e) result"
where
  "map_result_value4 _ (Error e) _ _ _ = (Error e)" |
  "map_result_value4 f (Value v) u s t  = (map_result_value3 (f v) u s t)"

fun map_result_value5 :: "('v \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'x) \<Rightarrow> ('v, 'e) result \<Rightarrow> ('u, 'e) result \<Rightarrow> ('s, 'e) result \<Rightarrow> ('t, 'e) result \<Rightarrow> ('w, 'e) result \<Rightarrow> ('x, 'e) result"
where
  "map_result_value5 _ (Error e) _ _ _ _ = (Error e)" |
  "map_result_value5 f (Value v) u s t w  = (map_result_value4 (f v) u s t w)"



fun
  flatten_error :: "('v, 'e) result list \<Rightarrow> ('v list, 'e) result"
where
  \<open>flatten_error lst = (if list_all is_Value lst then Value (map get lst) else Error (err (the (find is_error lst))))\<close>


end