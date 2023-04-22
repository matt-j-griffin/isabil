
signature BIL_PARSER =
sig

  val parse_typ: substring -> typ
  val parse_en: substring -> endian
  val parse_exp: substring -> exp
  val parse_stmt: substring -> stmt
  val parse_bil: substring -> bil

end;
