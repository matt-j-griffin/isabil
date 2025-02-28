theory Either
  imports Main
begin

datatype ('a, 'b) either = Left (left: 'a) | Right (right: 'b)

text \<open>The `is_left` function returns `True` if the given value is a `Left`-value, `False` otherwise.\<close>

abbreviation \<open>is_left \<equiv> is_Left\<close>

lemma unfold_is_left[simp]: \<open>is_left (Left x) = True\<close> \<open>is_left (Right x) = False\<close>
  by auto

lemmas is_left_simps = unfold_is_left either.disc

text \<open>The `is_right` function returns `True` if the given value is a `Right`-value, `False` otherwise.\<close>

primrec
  is_right :: \<open>('a, 'b) either \<Rightarrow> bool\<close>
  where
  \<open>is_right (Left  _) = False\<close> |
  \<open>is_right (Right _) = True\<close>


lemma is_right[simp]: \<open>\<not>is_right (Left x)\<close> \<open>is_right (Right x)\<close>
  by auto

lemmas is_right_simps = is_right.simps is_right

primrec
  find_left :: \<open>('a, 'b) either \<Rightarrow> 'a option\<close>
where
  \<open>find_left (Left  x) = Some x\<close> |
  \<open>find_left (Right _) = None\<close>

primrec
  find_right :: \<open>('a, 'b) either \<Rightarrow> 'b option\<close>
where
  \<open>find_right (Left  _) = None\<close> |
  \<open>find_right (Right x) = Some x\<close>

abbreviation \<open>map_left P \<equiv> map_either P id\<close>
abbreviation \<open>map_right \<equiv> map_either id\<close>

abbreviation \<open>fold_either \<equiv> rec_either\<close>

thm either.rec[of \<open>\<lambda>_. True\<close> \<open>\<lambda>_. False\<close>]
thm either.rec[of Some \<open>\<lambda>_. None\<close>]
find_theorems fold_either


code_printing
  type_constructor list \<rightharpoonup>
    (SML) "_ list"
    and (OCaml) "_ list"
    and (Haskell) "![(_)]"
    and (Scala) "List[(_)]"
| constant Nil \<rightharpoonup>
    (SML) "[]"
    and (OCaml) "[]"
    and (Haskell) "[]"
    and (Scala) "!Nil"
| class_instance list :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) infix 4 "=="

lemma "[]"
end
