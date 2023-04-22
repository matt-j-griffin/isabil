theory Examples
  imports "../BIL_Parse"
begin

BIL_file hello1 \<open>../ex01.bil.adt\<close>

context hello1
begin


sublocale bil_syntax
  where decode_pred = decode
  .


lemma "\<And>k .decode ((\<Delta>, victim_function_v01, mem)) (make 6442455145 \<Colon> 64 25 \<Colon> 64 (Stmt jmp 6442455824 \<Colon> 64 Empty))"
  unfolding victim_function_v01_180001069 
  using decode_180001069 by blast

end


locale test = bil_syntax +
  assumes decode_1800049C0: \<open>decode_pred (\<Delta>, (6442469824 \<Colon> 64), mem) (make (6442469824 \<Colon> 64) (1 \<Colon> 64) Empty)\<close>

begin

lemma "(\<Delta>, (6442469824 \<Colon> 64), mem) \<mapsto>\<^sub>b\<^sub>i\<^sub>l (make (6442469824 \<Colon> 64) (1 \<Colon> 64) Empty)"
  using decode_1800049C0 .


end

end
