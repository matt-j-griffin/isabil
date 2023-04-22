fun is_whitespace c = (c = #" " orelse c = #"\t"  orelse c = #"\n")
fun is_comma c = c <> #","
fun is_lbracket c = c <> #"("
fun is_rbracket c = c <> #")"
fun is_colon c = c <> #":"
fun is_lt c = c <> #"<"
fun is_gt c = c <> #">"

fun splitlr P Q = Substring.splitl P ##> Substring.splitr Q

val trim = fst o snd o splitlr is_whitespace is_whitespace

fun remove_outer str = Substring.slice (str, 1, SOME (Substring.size str - 2))

fun find_closing_bracket i (#"("::str) = 1 + find_closing_bracket (i + 1) str
  | find_closing_bracket 0 (#")"::_) = 1
  | find_closing_bracket i (#")"::str) = 1 + find_closing_bracket (i - 1) str
  | find_closing_bracket i (_::str) = 1 + find_closing_bracket i str
  | find_closing_bracket _ [] = raise Fail ("sad")


fun find_comma (#","::_) = 0
  | find_comma (#"("::str) = 
    let 
      val idx = find_closing_bracket 0 str
    in
      1 + idx + find_comma (List.drop (str, idx))
    end
  | find_comma (_::str) = 1 + find_comma str
  | find_comma [] = 0


fun splitXX "" = []
  | splitXX str =     
    let 
      val idx = str |> String.explode |> find_comma
      val (s1, s2) = Substring.splitAt (Substring.full str, idx) ||> Substring.triml 1 ||> trim ||> Substring.string ||> splitXX
    in
      s1::s2
    end

fun intfromString_forced(s: string) =
    case Int.fromString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ s ^ "' to int.")

val intFromHexString = StringCvt.scanString (LargeInt.scan StringCvt.HEX) o Substring.string

fun intFromHexString_forced(s: substring): int  =
    case intFromHexString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ Substring.string s ^ "' to int.")
