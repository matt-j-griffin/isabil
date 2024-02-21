theory AST_Prelims
  imports Result
begin

abbreviation \<open>TAB \<equiv> CHR 9\<close>
abbreviation \<open>VT \<equiv> CHR 11\<close>
abbreviation \<open>CR \<equiv> CHR 13\<close>
abbreviation \<open>LF \<equiv> CHR 10\<close>

abbreviation \<open>is_whitespace x \<equiv> (x = CHR '' '' \<or> x = TAB \<or> x = LF \<or> x = VT \<or> x = CR)\<close>

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

fun 
  insert_hd :: \<open>'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close>
where
  \<open>insert_hd x [] = [[x]]\<close> |
  \<open>insert_hd x (y # ys) = ((x # y) # ys)\<close>

lemma length_insert_hd: \<open>length xs \<le> length (insert_hd x xs)\<close>
  by (induct xs, auto)


function
  split :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> 'a list list\<close>
where
  \<open>split _ [] = []\<close> |
  \<open>split c (c # str) = [] # split c str\<close> |
  \<open>\<lbrakk>c' \<noteq> c\<rbrakk> \<Longrightarrow> split c (c' # str) = (insert_hd c' (split c str))\<close>
  subgoal for _ x
    apply (cases x, auto)
    subgoal for c str
      by (cases str, auto)
    .
  by auto
termination by lexicographic_order

declare split.simps(2)[simp del]

lemma split_eq_char[simp]: \<open>split c (c # str) = [] # split c str\<close>
  unfolding split.simps by simp

lemma split_neq_char[simp]: 
  assumes \<open>c' \<noteq> c\<close>
    shows \<open>split c (c' # str) = insert_hd c' (split c str)\<close>
  using assms unfolding split.simps by auto

lemma [code]: 
  \<open>split c [] = []\<close>
  \<open>split c (c' # str) = (if (c = c') then [] # split c str else insert_hd c' (split c str))\<close>
  by auto


datatype AST = Node string \<open>AST list\<close>



function
  split_not_within_int :: \<open>string \<Rightarrow> nat \<Rightarrow> string list\<close>
where
  \<open>split_not_within_int [] _ = []\<close> |
  \<open>split_not_within_int (CHR '','' # cs) 0 = [] # split_not_within_int cs 0\<close> |
  \<open>split_not_within_int (CHR ''('' # cs) ctr = insert_hd (CHR ''('') (split_not_within_int cs (ctr + 1))\<close> |
  \<open>split_not_within_int (CHR '')'' # cs) ctr = insert_hd (CHR '')'') (split_not_within_int cs (ctr - 1))\<close> |
  \<open>\<lbrakk>c \<noteq> CHR ''(''; c \<noteq> CHR '')''; ctr = 0 \<longrightarrow> c \<noteq> CHR '',''\<rbrakk> \<Longrightarrow> 
    split_not_within_int (c # cs) ctr = insert_hd c (split_not_within_int cs ctr)\<close>
  subgoal for _ x apply (cases x, auto)
    subgoal for x y by (cases x, auto)
    .
  by auto
termination by lexicographic_order

lemma [code]: 
  \<open>split_not_within_int [] ctr = []\<close>
\<open>split_not_within_int (c # str) ctr = (
  if (c = CHR '','' \<and> ctr = 0) then [] # split_not_within_int str 0
  else if (c = CHR ''('') then insert_hd (CHR ''('') (split_not_within_int str (ctr + 1))
  else if (c = CHR '')'') then insert_hd (CHR '')'') (split_not_within_int str (ctr - 1))
  else insert_hd c (split_not_within_int str ctr))\<close>
  by (auto split: if_split)

fun
  split_not_within :: \<open>string \<Rightarrow> string list\<close>
where
  \<open>split_not_within s = split_not_within_int s 0\<close>

lemma split_empty[simp]: \<open>split_not_within [] = []\<close>
  by auto

lemma length_split_not_within:
  assumes \<open>xd \<in> set (split_not_within xs)\<close>
    shows \<open>length xd \<le> length xs\<close>
using assms unfolding split_not_within.simps proof (induction arbitrary: xd rule: split_not_within_int.induct[of _ xs 0])
  case (2 cs)
  then show ?case 
    apply auto    
    using le_SucI by presburger
next
  case (3 cs ctr)
  then show ?case 
    apply auto
    apply (cases \<open>split_not_within_int cs (Suc ctr)\<close>, auto)
    using le_SucI by presburger
next
  case (4 cs ctr)
  then show ?case 
    apply auto
    apply (cases \<open>split_not_within_int cs (ctr - Suc 0)\<close>, auto)
    using le_SucI by presburger
next
  case (5 c ctr cs)
  then show ?case
    apply auto
    apply (cases \<open>split_not_within_int cs ctr\<close>, auto)
    using le_SucI apply presburger
    apply (cases \<open>split_not_within_int cs ctr\<close>, auto)
    using le_SucI by presburger
qed auto


type_synonym 'v parser_result = \<open>('v, string) result\<close>

abbreviation \<open>ord0 \<equiv> of_char (CHR ''0'')\<close>
abbreviation \<open>ord9 \<equiv> of_char (CHR ''9'')\<close>
abbreviation \<open>orda \<equiv> of_char (CHR ''a'')\<close>
abbreviation \<open>ordA \<equiv> of_char (CHR ''A'')\<close>
abbreviation \<open>ordz \<equiv> of_char (CHR ''z'')\<close>
abbreviation \<open>ordZ \<equiv> of_char (CHR ''Z'')\<close>



text \<open>Converts a char ordinal to a numeric type (with radix)\<close>

definition
  of_char_radix :: \<open>('a::{minus,ord,comm_semiring_1}) \<Rightarrow> char \<Rightarrow>  ('a::{minus,ord,comm_semiring_1}) parser_result\<close>
where
  \<open>of_char_radix radix c  = (
    let 
      ord = of_char c 
    in
      if (radix > 36) then Error (List.append ''Radix out of range (>36): '' [c])
      else if (ord0 \<le> ord \<and> ord \<le> max ord9 radix) then Value (ord - ord0)
      else if (radix > 10 \<and> orda \<le> ord \<and> ord \<le> orda + (radix - 11)) then Value (ord - orda + 10)
      else if (radix > 10 \<and> ordA \<le> ord \<and> ord \<le> ordA + (radix - 11)) then Value (ord - ordA + 10)
      else Error (List.append ''Codepoint out of range for radix: '' [c])
  )\<close>

abbreviation
  of_char_dec :: \<open>char \<Rightarrow> ('a::{minus,ord,comm_semiring_1}) parser_result\<close>
where
  \<open>of_char_dec \<equiv> of_char_radix 10\<close>

lemma of_char_dec_linordered_semidom[simp]: \<open>of_char_dec (CHR ''0'') = Value (0::'a::linordered_semidom)\<close>
  unfolding of_char_radix_def by auto

lemma of_char_dec_nat[simp]:
  \<open>of_char_dec (CHR ''1'') = Value (1::nat)\<close> \<open>of_char_dec (CHR ''2'') = Value (2::nat)\<close>
  \<open>of_char_dec (CHR ''3'') = Value (3::nat)\<close> \<open>of_char_dec (CHR ''4'') = Value (4::nat)\<close>
  \<open>of_char_dec (CHR ''5'') = Value (5::nat)\<close> \<open>of_char_dec (CHR ''6'') = Value (6::nat)\<close>
  \<open>of_char_dec (CHR ''7'') = Value (7::nat)\<close> \<open>of_char_dec (CHR ''8'') = Value (8::nat)\<close>
  \<open>of_char_dec (CHR ''9'') = Value (9::nat)\<close>
  unfolding of_char_radix_def by auto
  
lemma of_char_dec_0_9: \<open>of_char_dec c = Value v \<Longrightarrow> (v::nat) \<in> {0..9}\<close>
  unfolding of_char_radix_def Let_def by (auto split: if_splits)

abbreviation
  of_char_hex :: \<open>char \<Rightarrow> ('a::{minus,ord,comm_semiring_1}) parser_result\<close>
where
  \<open>of_char_hex \<equiv> of_char_radix 16\<close>

lemma of_char_hex_linordered_semidom[simp]: \<open>of_char_hex (CHR ''0'') = Value (0::'a::linordered_semidom)\<close>
  unfolding of_char_radix_def by auto

lemma of_char_hex_nat[simp]:
  \<open>of_char_hex (CHR ''1'') = Value (1::nat)\<close> \<open>of_char_hex (CHR ''2'') = Value (2::nat)\<close>
  \<open>of_char_hex (CHR ''3'') = Value (3::nat)\<close> \<open>of_char_hex (CHR ''4'') = Value (4::nat)\<close>
  \<open>of_char_hex (CHR ''5'') = Value (5::nat)\<close> \<open>of_char_hex (CHR ''6'') = Value (6::nat)\<close>
  \<open>of_char_hex (CHR ''7'') = Value (7::nat)\<close> \<open>of_char_hex (CHR ''8'') = Value (8::nat)\<close>
  \<open>of_char_hex (CHR ''9'') = Value (9::nat)\<close>
  \<open>of_char_hex (CHR ''a'') = Value (10::nat)\<close> \<open>of_char_hex (CHR ''A'') = Value (10::nat)\<close>
  \<open>of_char_hex (CHR ''b'') = Value (11::nat)\<close> \<open>of_char_hex (CHR ''B'') = Value (11::nat)\<close>
  \<open>of_char_hex (CHR ''c'') = Value (12::nat)\<close> \<open>of_char_hex (CHR ''C'') = Value (12::nat)\<close>
  \<open>of_char_hex (CHR ''d'') = Value (13::nat)\<close> \<open>of_char_hex (CHR ''D'') = Value (13::nat)\<close>
  \<open>of_char_hex (CHR ''e'') = Value (14::nat)\<close> \<open>of_char_hex (CHR ''E'') = Value (14::nat)\<close>
  \<open>of_char_hex (CHR ''f'') = Value (15::nat)\<close> \<open>of_char_hex (CHR ''F'') = Value (15::nat)\<close>
  unfolding of_char_radix_def Let_def by auto
  
lemma of_char_hex_0_16: \<open>of_char_hex c = Value v \<Longrightarrow> (v::nat) \<in> {0..15}\<close>
  unfolding of_char_radix_def Let_def by (auto split: if_splits)


fun
  nat_of_string_radix  :: \<open>nat \<Rightarrow> string \<Rightarrow> nat parser_result\<close>
where
  \<open>nat_of_string_radix _ [] = Error ''Cannot convert empty string to nat''\<close> |
  \<open>nat_of_string_radix radix [c] = of_char_radix radix c\<close> |
  \<open>nat_of_string_radix radix (c # str) = (
    Result.bind (of_char_radix radix c) (\<lambda>d. map_result_value (\<lambda>m. (radix ^ length str) * d + m) (nat_of_string_radix radix str))
  )\<close>

abbreviation \<open>nat_of_dec_string \<equiv> nat_of_string_radix 10\<close>
abbreviation \<open>nat_of_hex_string \<equiv> nat_of_string_radix 16\<close>

fun
  int_of_string  :: \<open>string \<Rightarrow> int parser_result\<close>
where
  \<open>int_of_string [] = Error ''Cannot convert empty string to int''\<close> |
  \<open>int_of_string (c # str) = (
    if c = CHR ''-'' then map_result_value (\<lambda>x. x * -1) (map_result_value of_nat (nat_of_dec_string str))
    else map_result_value of_nat (nat_of_dec_string (c # str))
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
