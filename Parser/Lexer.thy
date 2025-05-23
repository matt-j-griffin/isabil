theory Lexer
  imports "../OperationalSemantics/Program_Model" 
          "../Prelims/Result" 
          "../Prelims/AST_Prelims"
    
begin

abbreviation \<open>isnt_lbracket x \<equiv> (x \<noteq> CHR ''('')\<close>

lemma length_tl_ltE:
  assumes major: \<open>length xs < length (tl ys)\<close>
      and minor: \<open>\<lbrakk>length xs < length ys\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  using major minor by fastforce

lemma length_dropWhile_ltE:
  assumes major: \<open>length xs < length (dropWhile P ys)\<close>
      and minor: \<open>\<lbrakk>length xs < length ys\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  using length_dropWhile_le major minor order.strict_trans2 by blast

lemma length_trim_ltE:
  assumes major: \<open>length xs < length (trim ys)\<close>
      and minor: \<open>\<lbrakk>length xs < length ys\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  apply (rule minor)
  using major unfolding trim_def triml_def trimr_def apply simp
  by (elim length_dropWhile_ltE, unfold length_rev)+

lemma length_butlast_le_ltE:
  assumes major: \<open>length xs \<le> length (butlast ys)\<close>
      and rec: \<open>\<lbrakk>length xs < length ys\<rbrakk> \<Longrightarrow> R\<close>
      and empty: \<open>\<lbrakk>xs = []; ys = []\<rbrakk> \<Longrightarrow> R\<close>
    shows R
proof (cases ys)
  case Nil
  hence \<open>xs = []\<close>
    using major by simp
  thus ?thesis 
    using Nil by (rule empty)
next
  case (Cons a list)
  show ?thesis 
    apply (rule rec)
    using major unfolding length_butlast Cons by simp
qed

function
  if_hd_eq :: \<open>'a \<Rightarrow> ('a list \<Rightarrow> 'c) \<Rightarrow> ('a list \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'c\<close>
where
  \<open>if_hd_eq c P _ (c # cs) = P (c # cs)\<close> |
  \<open>\<lbrakk>c \<noteq> c'\<rbrakk> \<Longrightarrow> if_hd_eq c _ Q (c' # cs) = Q (c' # cs)\<close> |
  \<open>if_hd_eq c _ Q [] = Q []\<close>
  apply auto
  by (metis list.exhaust)
termination by (standard, auto)

function
  lexer :: \<open>string \<Rightarrow> AST\<close>
where
  \<open>lexer str = (
    let 
      tstr = trim str;
      name = (if_hd_eq (CHR ''"'') id (takeWhile isnt_lbracket) tstr);
      bargstr = (if_hd_eq (CHR ''"'') (\<lambda>_. []) (dropWhile isnt_lbracket) tstr);
      argstr = butlast (tl bargstr)
    in
      Node name (map lexer (split_not_within argstr))
  )\<close>
  by auto
termination proof (standard, rule wf_mlex[of \<open>{}\<close> length])
  fix str tstr name bargstr argstr ast assume prems: \<open>tstr = trim str\<close> 
    \<open>name = if_hd_eq CHR 0x22 id (takeWhile isnt_lbracket) tstr\<close> 
    \<open>bargstr = if_hd_eq (CHR ''"'') (\<lambda>_. []) (dropWhile isnt_lbracket) tstr\<close>
    \<open>argstr = butlast (tl bargstr)\<close> and rel: \<open>ast \<in> set (split_not_within argstr)\<close>
  show \<open>(ast, str) \<in> length <*mlex*> {}\<close>
  proof (rule mlex_less) 
    show \<open>length ast < length str\<close>
    proof (cases \<open>trim str\<close>)
      case Nil
      show ?thesis 
        using rel[unfolded prems Nil, simplified] by auto
    next
      case (Cons a list)
      then show ?thesis 
      proof (cases \<open>a = CHR ''"''\<close>)
        case True
        show ?thesis 
          using rel[unfolded prems Cons True, simplified] by auto
      next
        case False
        hence ast: \<open>ast \<in> set (split_not_within (butlast (tl (dropWhile isnt_lbracket (trim str)))))\<close>
          unfolding Cons
          using rel[unfolded prems Cons False, simplified] by auto
        show ?thesis
        proof (cases str)
          case Nil
          thus ?thesis using ast by simp
        next
          case (Cons a list)
          show ?thesis 
          proof (insert ast Cons , drule length_split_not_within , elim length_butlast_le_ltE)
            assume "length ast < length (tl (dropWhile isnt_lbracket (trim str)))"
            thus "length ast < length str"
              by (elim length_tl_ltE length_dropWhile_ltE length_trim_ltE)
          qed simp
        qed
      qed
    qed
  qed
qed standard

end
