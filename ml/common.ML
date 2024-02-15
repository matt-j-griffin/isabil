fun is_whitespace c = (c = #" " orelse c = #"\t"  orelse c = #"\n")
fun is_lbracket c = c <> #"("
fun is_rbracket c = c <> #")"
fun is_colon c = c <> #":"
fun is_lt c = c <> #"<"
fun is_gt c = c <> #">"

fun splitlr P Q = Substring.splitl P ##> Substring.splitr Q

val trim = fst o snd o splitlr is_whitespace is_whitespace

fun remove_outer str = Substring.slice (str, 1, SOME (Substring.size str - 2))

fun intfromString_forced(s: string) =
    case Int.fromString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ s ^ "' to int.")

val intFromHexString = StringCvt.scanString (LargeInt.scan StringCvt.HEX) o Substring.string

fun intFromHexString_forced(s: substring): int  =
    case intFromHexString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ Substring.string s ^ "' to int.")

fun or_raise (AstParser.Value v) = v
  | or_raise (AstParser.Error e) = raise Fail (Str_Literal.literal_of_asciis (map AstParser.integer_of_char e))
