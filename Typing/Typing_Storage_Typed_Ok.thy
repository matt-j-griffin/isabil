theory Typing_Storage_Typed_Ok
  imports Typing_Typed_Ok
          Typing_Word
          Typing_Context
begin

class storage_typed_ok = storage_constructor + typed_ok + word_is_ok +
  assumes storage_typed_diff: \<open>\<And>\<Gamma> v num nat v' sz nat' sz'.
            \<Gamma> \<turnstile> (v[(num \<Colon> nat) \<leftarrow> v', sz]) :: mem\<langle>nat', sz'\<rangle> \<Longrightarrow> nat' = nat \<and> sz' = sz\<close>
      and storage_not_imm: \<open>\<And>\<Gamma> mem w v sz sz'. \<not>(\<Gamma> \<turnstile> mem[w \<leftarrow> v, sz] :: imm\<langle>sz'\<rangle>)\<close>

end
