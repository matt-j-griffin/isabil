theory AST_Prelims
  imports Result
begin

abbreviation \<open>is_whitespace x \<equiv> (x = CHR '' '' \<or> x = CHR 0x9 \<or> x = CHR 10 \<or> x = CHR 13)\<close>

definition
  triml :: \<open>string \<Rightarrow> string\<close>
where
  \<open>triml = dropWhile is_whitespace\<close>

lemma triml_empty[simp]: \<open>triml '''' = ''''\<close>
  unfolding triml_def by auto

lemma triml_is_whitespace: \<open>triml str = '''' \<longleftrightarrow> Ball (set str) is_whitespace\<close>
  unfolding triml_def dropWhile_eq_Nil_conv ..

definition
  trimr :: \<open>string \<Rightarrow> string\<close>
where
  \<open>trimr = (rev o triml o rev)\<close>

lemma trimr_empty[simp]: \<open>trimr '''' = ''''\<close>
  unfolding trimr_def by auto

lemma trimr_is_whitespace: \<open>trimr str = '''' \<longleftrightarrow> Ball (set str) is_whitespace\<close>
  unfolding trimr_def by (simp add: triml_is_whitespace)

definition
  trim :: \<open>string \<Rightarrow> string\<close>
where
  \<open>trim = triml o trimr\<close>

declare triml_def[simp]
declare trimr_def[simp]
declare trim_def[simp]

lemma trim_empty[simp]: \<open>trim '''' = ''''\<close>
  unfolding trim_def by auto

lemma ascii_of_ascii_of[simp]: \<open>String.ascii_of (String.ascii_of x) = String.ascii_of x\<close>
  using String.ascii_of_idem by auto




datatype AST = Node string \<open>AST list\<close>


fun 
  insert_hd :: \<open>'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close>
where
  \<open>insert_hd x [] = [[x]]\<close> |
  \<open>insert_hd x (y # ys) = ((x # y) # ys)\<close>

lemma length_insert_hd: \<open>length xs \<le> length (insert_hd x xs)\<close>
  by (induct xs, auto)

function
  split_string :: \<open>string \<Rightarrow> nat \<Rightarrow> string list\<close>
where
  \<open>split_string [] _ = []\<close> |
  \<open>split_string (CHR '','' # cs) 0 = [] # split_string cs 0\<close> |
  \<open>split_string (CHR ''('' # cs) ctr = insert_hd (CHR ''('') (split_string cs (ctr + 1))\<close> |
  \<open>split_string (CHR '')'' # cs) ctr = insert_hd (CHR '')'') (split_string cs (ctr - 1))\<close> |
  \<open>\<lbrakk>c \<noteq> CHR ''(''; c \<noteq> CHR '')''; ctr = 0 \<longrightarrow> c \<noteq> CHR '',''\<rbrakk> \<Longrightarrow> 
    split_string (c # cs) ctr = insert_hd c (split_string cs ctr)\<close>
  subgoal for _ x apply (cases x, auto)
    subgoal for x y by (cases x, auto)
    .
  by auto
termination by lexicographic_order

lemma [code]: 
  \<open>split_string [] ctr = []\<close>
\<open>split_string (c # str) ctr = (
  if (c = CHR '','' \<and> ctr = 0) then [] # split_string str 0
  else if (c = CHR ''('') then insert_hd (CHR ''('') (split_string str (ctr + 1))
  else if (c = CHR '')'') then insert_hd (CHR '')'') (split_string str (ctr - 1))
  else insert_hd c (split_string str ctr))\<close>
  by (auto split: if_split)

fun
  split :: \<open>string \<Rightarrow> string list\<close>
where
  \<open>split s = split_string s 0\<close>

lemma split_empty[simp]: \<open>split [] = []\<close>
  by auto

lemma length_split:
  assumes \<open>xd \<in> set (split xs)\<close>
    shows \<open>length xd \<le> length xs\<close>
using assms unfolding split.simps proof (induction arbitrary: xd rule: split_string.induct[of _ xs 0])
  case (2 cs)
  then show ?case 
    apply auto    
    using le_SucI by presburger
next
  case (3 cs ctr)
  then show ?case 
    apply auto
    apply (cases \<open>split_string cs (Suc ctr)\<close>, auto)
    using le_SucI by presburger
next
  case (4 cs ctr)
  then show ?case 
    apply auto
    apply (cases \<open>split_string cs (ctr - Suc 0)\<close>, auto)
    using le_SucI by presburger
next
  case (5 c ctr cs)
  then show ?case
    apply auto
    apply (cases \<open>split_string cs ctr\<close>, auto)
    using le_SucI apply presburger
    apply (cases \<open>split_string cs ctr\<close>, auto)
    using le_SucI by presburger
qed auto


type_synonym 'v parser_result = \<open>('v, string) result\<close>

abbreviation \<open>ord0 \<equiv> of_char (CHR ''0'')\<close>
abbreviation \<open>ord9 \<equiv> of_char (CHR ''9'')\<close>

text \<open>Converts a char ordinal to a numeric type\<close>

definition
  of_char_ord :: \<open>char \<Rightarrow> ('a::{minus,ord,comm_semiring_1}) parser_result\<close>
where
  \<open>of_char_ord c = (
    let 
      ord = of_char c 
    in
      if (ord < ord0 \<or> ord > ord9)
      then Error (List.append ''Codepoint out of range (48-57): '' [c])
      else Value (ord - ord0)
  )\<close>

lemma of_char_ord_linordered_semidom[simp]: \<open>of_char_ord (CHR ''0'') = Value (0::'a::linordered_semidom)\<close>
  unfolding of_char_ord_def by auto

lemma of_char_ord_nat[simp]:
  \<open>of_char_ord (CHR ''1'') = Value (1::nat)\<close> \<open>of_char_ord (CHR ''2'') = Value (2::nat)\<close>
  \<open>of_char_ord (CHR ''3'') = Value (3::nat)\<close> \<open>of_char_ord (CHR ''4'') = Value (4::nat)\<close>
  \<open>of_char_ord (CHR ''5'') = Value (5::nat)\<close> \<open>of_char_ord (CHR ''6'') = Value (6::nat)\<close>
  \<open>of_char_ord (CHR ''7'') = Value (7::nat)\<close> \<open>of_char_ord (CHR ''8'') = Value (8::nat)\<close>
  \<open>of_char_ord (CHR ''9'') = Value (9::nat)\<close>
  unfolding of_char_ord_def by auto
  
lemma of_char_ord_0_9: \<open>of_char_ord c = Value v \<Longrightarrow> (v::nat) \<in> {0..9}\<close>
  unfolding of_char_ord_def Let_def by (auto split: if_splits)

fun
  nat_of_string  :: \<open>string \<Rightarrow> nat parser_result\<close>
where
  \<open>nat_of_string [] = Error ''Cannot convert empty string to nat''\<close> |
  \<open>nat_of_string [c] = of_char_ord c\<close> |
  \<open>nat_of_string (c # str) = (
    Result.bind (of_char_ord c) (\<lambda>d. map_result_value (\<lambda>m. 10 * d + m) (nat_of_string str))
  )\<close>

fun
  int_of_string  :: \<open>string \<Rightarrow> int parser_result\<close>
where
  \<open>int_of_string [] = Error ''Cannot convert empty string to int''\<close> |
  \<open>int_of_string (c # str) = (
    if c = CHR ''-'' then map_result_value (\<lambda>x. x * -1) (map_result_value of_nat (nat_of_string str))
    else map_result_value of_nat (nat_of_string (c # str))
  )\<close>


lemma length1_cases: obtains (Length) x where \<open>xs = [x]\<close> | (NotLength) \<open>length xs \<noteq> 1\<close>
  by (cases xs, auto)

lemma length2_cases: obtains (Length) x y where \<open>xs = [x, y]\<close> | (NotLength) \<open>length xs \<noteq> 2\<close>
  apply (cases xs, auto)
  subgoal for _ ys
    by (cases ys rule: length1_cases, auto) 
  .

lemma length3_cases: obtains (Length) x y z where \<open>xs = [x, y, z]\<close> | (NotLength) \<open>length xs \<noteq> 3\<close>
  apply (cases xs, auto)
  subgoal for _ ys
    by (cases ys rule: length2_cases, auto) 
  .

lemma length4_cases: obtains (Length) x y z w where \<open>xs = [x, y, z, w]\<close> | (NotLength) \<open>length xs \<noteq> 4\<close>
  apply (cases xs, auto)
  subgoal for _ ys
    by (cases ys rule: length3_cases, auto) 
  .

lemma length5_cases: obtains (Length) x y z w t where \<open>xs = [x, y, z, w, t]\<close> | (NotLength) \<open>length xs \<noteq> 5\<close>
  apply (cases xs, auto)
  subgoal for _ ys
    by (cases ys rule: length4_cases, auto) 
  .

end
