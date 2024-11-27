structure Str_Literal =
struct

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ module *)

fun check_ascii (k : IntInf.int) =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o IntInf.toInt o check_ascii;

val ascii_of_char = check_ascii o IntInf.fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure AstParser : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type char
  val integer_of_char : char -> IntInf.int
  datatype int = Int_of_integer of IntInf.int
  type ('a, 'b) result
  type word
  type adtSection
  type 'a ofStringRadixError
  type parseError
  type 'a insn_ext
  val implode : char list -> string
  val get_insns : nat -> adtSection list -> unit insn_ext list
  val nat_of_integer : IntInf.int -> nat
  val integer_of_int : int -> IntInf.int
  val join : string list -> string
  val get_prog_addrs : nat -> adtSection list -> word list
  val get_symbol_table : adtSection list -> (string * nat) list
  val get_original_insn : adtSection list -> (nat * string) list
  val parse_adt_program : string list -> ((adtSection list), parseError) result
  val filter_subroutines : string list -> adtSection list -> adtSection list
  val get_subroutine_addrs : adtSection list -> (string * word list) list
  val parse_error_to_string : parseError -> string
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype char = Chr of IntInf.int;

fun integer_of_char (Chr x) = x;

fun equal_chara c d =
  (((integer_of_char c) : IntInf.int) = (integer_of_char d));

val equal_char = {equal = equal_chara} : char equal;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

datatype int = Int_of_integer of IntInf.int;

datatype ('a, 'b) result = Value of 'a | Error of 'b;

datatype aOp = Plus | Minus | Times | Divide | SDivide | Mod | SMod | And | Or |
  Xor | LShift | RShift | ARShift;

datatype lOp = Eq | Neq | Lt | Le | Slt | Sle;

datatype endian = LittleEndian | BigEndian;

datatype binOp = AOp of aOp | LOp of lOp;

datatype unOp = Neg | Not;

datatype cast = Unsigned | Signed | High | Low;

datatype typea = Imm of nat | Mem of nat * nat;

datatype var = CVar of string * typea;

datatype word = Word of nat * nat;

datatype vala = CUnknown of string * typea | Immediate of word |
  Storage of vala * word * vala * nat;

datatype exp = Val of vala | EVar of var | Load of exp * exp * endian * nat |
  Store of exp * exp * endian * nat * exp | BinOp of exp * binOp * exp |
  UnOp of unOp * exp | Cast of cast * nat * exp | Let of var * exp * exp |
  Ite of exp * exp * exp | Extract of nat * nat * exp | Concat of exp * exp;

datatype stmt = CSpecial of string | CpuExn of int | While of exp * stmt list |
  Move of var * exp | Jmp of exp | If of exp * stmt list * stmt list;

datatype adtInsn = CAdtInsn of nat * stmt list * string;

datatype ast = CNode of string * ast list;

datatype adtFunction = CAdtFunction of nat * string * adtInsn list;

datatype adtSection = CAdtSection of string * adtFunction list;

datatype 'a ofStringRadixError = EmptyString | InvalidRadixa of 'a |
  InvalidCodepointa of char * 'a;

datatype parseError = ParseNatError of nat ofStringRadixError |
  ParseIntError of int ofStringRadixError |
  CParseArgumentError of string * nat * nat | CStringMustBeQuoted of string |
  CParseTagInvalid of string list * string | CTagExistsError of string |
  CInvalidAdtInsn of string list | CInvalidAdtFunction of string list |
  CInvalidAdtSection of string list;

datatype 'a ofCharRadixError = InvalidRadix of 'a |
  InvalidCodepoint of char * 'a;

datatype 'a insn_ext = Insn_ext of word * word * stmt list * 'a;

fun id x = (fn xa => xa) x;

fun suc n = plus_nata n one_nata;

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun nth (x :: xs) n =
  (if equal_nat n zero_nata then x else nth xs (minus_nata n one_nata));

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nat n zero_nata then x :: xs
      else drop (minus_nata n one_nata) xs);

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun null [] = true
  | null (x :: xs) = false;

fun last (x :: xs) = (if null xs then x else last xs);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun bind (Error e) uu = Error e
  | bind (Value x) f = f x;

fun butlast [] = []
  | butlast (x :: xs) = (if null xs then [] else x :: butlast xs);

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun if_hd_eq c uw q [] = q [];

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun takeWhile p [] = []
  | takeWhile p (x :: xs) = (if p x then x :: takeWhile p xs else []);

fun splitOn p (x :: xs) =
  (case dropWhile (fn y => not (p y)) (x :: xs) of [] => []
    | y :: ys => (y :: takeWhile (fn ya => not (p ya)) ys) :: splitOn p ys)
  | splitOn uu [] = [];

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun prefix A_ (x :: xs) (y :: ys) = eq A_ x y andalso prefix A_ xs ys
  | prefix A_ (x :: xs) [] = false
  | prefix A_ [] xs = true;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun get_insn sza (CAdtInsn (num, bil, str)) sz =
  Insn_ext (Word (num, sza), Word (sz, sza), bil, ());

fun size_list x = gen_length zero_nata x;

fun parse_en (CNode (en, ast)) =
  (if ((en : string) = "LittleEndian")
    then (case ast of [] => Value LittleEndian
           | x :: xs =>
             Error (CParseArgumentError
                     ("LittleEndian", zero_nata, size_list (x :: xs))))
    else (if ((en : string) = "BigEndian")
           then (case ast of [] => Value BigEndian
                  | x :: xs =>
                    Error (CParseArgumentError
                            ("BigEndian", zero_nata, size_list (x :: xs))))
           else Error (CParseTagInvalid (["BigEndian", "LittleEndian"], en))));

fun is_error (Value x) = false
  | is_error (Error e) = true;

fun ascii_of c =
  Chr let
        val k = integer_of_char c;
      in
        (if IntInf.< (k, (128 : IntInf.int)) then k
          else IntInf.- (k, (128 : IntInf.int)))
      end;

val char_0x20 : char = Chr (32 : IntInf.int);

val char_0x0D : char = Chr (13 : IntInf.int);

val char_0x0B : char = Chr (11 : IntInf.int);

val char_0x0A : char = Chr (10 : IntInf.int);

val char_0x09 : char = Chr (9 : IntInf.int);

fun triml x =
  dropWhile
    (fn xa =>
      equal_chara xa char_0x20 orelse
        (equal_chara xa char_0x09 orelse
          (equal_chara xa char_0x0A orelse
            (equal_chara xa char_0x0B orelse equal_chara xa char_0x0D))))
    x;

fun trimr x = (rev o triml o rev) x;

fun trim x = (triml o trimr) x;

val char_0x28 : char = Chr (40 : IntInf.int);

val char_0x22 : char = Chr (34 : IntInf.int);

val char_0x2C : char = Chr (44 : IntInf.int);

val char_0x29 : char = Chr (41 : IntInf.int);

fun insert_hd x [] = [[x]]
  | insert_hd x (y :: ys) = (x :: y) :: ys;

fun split_not_within_int (c :: str) ctr =
  (if equal_chara c char_0x2C andalso equal_nat ctr zero_nata
    then [] :: split_not_within_int str zero_nata
    else (if equal_chara c char_0x28
           then insert_hd char_0x28
                  (split_not_within_int str (plus_nata ctr one_nata))
           else (if equal_chara c char_0x29
                  then insert_hd char_0x29
                         (split_not_within_int str (minus_nata ctr one_nata))
                  else insert_hd c (split_not_within_int str ctr))))
  | split_not_within_int [] ctr = [];

fun split_not_within s = split_not_within_int s zero_nata;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun char_of_integer k =
  Chr (if IntInf.<= ((0 : IntInf.int), k) andalso
            IntInf.< (k, (256 : IntInf.int))
        then k else modulo_integer k (256 : IntInf.int));

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun lexer lit =
  let
    val str = explode lit;
    val tstr = trim str;
    val name =
      if_hd_eq char_0x22 id
        (takeWhile ((fn x => not (equal_chara x char_0x28)) o ascii_of)) tstr;
    val bargstr =
      if_hd_eq char_0x22 (fn _ => [])
        (dropWhile ((fn x => not (equal_chara x char_0x28)) o ascii_of)) tstr;
    val argstr = butlast (tl bargstr);
  in
    CNode (implode name, map (lexer o implode) (split_not_within argstr))
  end;

fun get_prog_addr sz (CAdtInsn (num, bil, str)) = Word (num, sz);

fun get_insns_function sza (CAdtFunction (num, str, ast)) =
  let
    val words = map (get_prog_addr sza) ast;
    val addrs = map (fn Word (sz, _) => sz) words;
    val szs =
      map (fn (a, b) => minus_nata b a) (zip addrs (tl addrs @ [zero_nata]));
  in
    map (fn (a, b) => get_insn sza a b) (zip ast szs)
  end;

fun get_insns_section sz (CAdtSection (str, ast)) =
  fold ((fn a => fn b => a @ b) o get_insns_function sz) ast [];

fun get_insns sz ast =
  fold ((fn a => fn b => a @ b) o get_insns_section sz) ast [];

fun is_Value (Value x1) = true
  | is_Value (Error x2) = false;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun get (Value x1) = x1;

fun err (Error x2) = x2;

fun the (SOME x2) = x2;

fun flatten_error lst =
  (if list_all is_Value lst then Value (map get lst)
    else Error (err (the (find is_error lst))));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun map_result_value f (Error e) = Error e
  | map_result_value f (Value v) = Value (f v);

fun map_result_value2 uu (Error e) uv = Error e
  | map_result_value2 f (Value v) r = map_result_value (f v) r;

fun map_result_value3 uu (Error e) uv uw = Error e
  | map_result_value3 f (Value v) u s = map_result_value2 (f v) u s;

fun to_nat_of_string_radix_error (InvalidRadix radix) = InvalidRadixa radix
  | to_nat_of_string_radix_error (InvalidCodepoint (codepoint, radix)) =
    InvalidCodepointa (codepoint, radix);

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if ((k : IntInf.int) = (0 : IntInf.int))
        then ((0 : IntInf.int), (0 : IntInf.int))
        else (if ((l : IntInf.int) = (0 : IntInf.int))
               then ((0 : IntInf.int), k)
               else IntInf.divMod (IntInf.abs k, IntInf.abs l)))
  end;

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun of_nat A_ n =
  (if equal_nat n zero_nata
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
                A_)
    else let
           val (m, q) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val ma =
             times ((times_power o power_monoid_mult o
                      monoid_mult_semiring_numeral o
                      semiring_numeral_semiring_1)
                     A_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1) A_)
                 (Bit0 One))
               (of_nat A_ m);
         in
           (if equal_nat q zero_nata then ma
             else plus ((plus_semigroup_add o semigroup_add_numeral o
                          numeral_semiring_numeral o
                          semiring_numeral_semiring_1)
                         A_)
                    ma (one ((one_numeral o numeral_semiring_numeral o
                               semiring_numeral_semiring_1)
                              A_)))
         end);

fun of_char A_ c =
  of_nat (semiring_1_comm_semiring_1 A_) (nat_of_integer (integer_of_char c));

val char_0x61 : char = Chr (97 : IntInf.int);

val char_0x41 : char = Chr (65 : IntInf.int);

val char_0x39 : char = Chr (57 : IntInf.int);

val char_0x30 : char = Chr (48 : IntInf.int);

fun of_char_radix (A1_, A2_, A3_) radix c =
  let
    val ord = of_char A3_ c;
  in
    (if less A2_
          (numeral
            ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
               semiring_1_comm_semiring_1)
              A3_)
            (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One))))))
          radix
      then Error (InvalidRadix radix)
      else (if less_eq A2_ (of_char A3_ char_0x30) ord andalso
                 less_eq A2_ ord (max A2_ (of_char A3_ char_0x39) radix)
             then Value (minus A1_ ord (of_char A3_ char_0x30))
             else (if less A2_
                        (numeral
                          ((numeral_semiring_numeral o
                             semiring_numeral_semiring_1 o
                             semiring_1_comm_semiring_1)
                            A3_)
                          (Bit0 (Bit1 (Bit0 One))))
                        radix andalso
                        (less_eq A2_ (of_char A3_ char_0x61) ord andalso
                          less_eq A2_ ord
                            (plus ((plus_semigroup_add o semigroup_add_numeral o
                                     numeral_semiring_numeral o
                                     semiring_numeral_semiring_1 o
                                     semiring_1_comm_semiring_1)
                                    A3_)
                              (of_char A3_ char_0x61)
                              (minus A1_ radix
                                (numeral
                                  ((numeral_semiring_numeral o
                                     semiring_numeral_semiring_1 o
                                     semiring_1_comm_semiring_1)
                                    A3_)
                                  (Bit1 (Bit1 (Bit0 One)))))))
                    then Value (plus ((plus_semigroup_add o
semigroup_add_numeral o numeral_semiring_numeral o semiring_numeral_semiring_1 o
semiring_1_comm_semiring_1)
                                       A3_)
                                 (minus A1_ ord (of_char A3_ char_0x61))
                                 (numeral
                                   ((numeral_semiring_numeral o
                                      semiring_numeral_semiring_1 o
                                      semiring_1_comm_semiring_1)
                                     A3_)
                                   (Bit0 (Bit1 (Bit0 One)))))
                    else (if less A2_
                               (numeral
                                 ((numeral_semiring_numeral o
                                    semiring_numeral_semiring_1 o
                                    semiring_1_comm_semiring_1)
                                   A3_)
                                 (Bit0 (Bit1 (Bit0 One))))
                               radix andalso
                               (less_eq A2_ (of_char A3_ char_0x41) ord andalso
                                 less_eq A2_ ord
                                   (plus ((plus_semigroup_add o
    semigroup_add_numeral o numeral_semiring_numeral o
    semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
   A3_)
                                     (of_char A3_ char_0x41)
                                     (minus A1_ radix
                                       (numeral
 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
    semiring_1_comm_semiring_1)
   A3_)
 (Bit1 (Bit1 (Bit0 One)))))))
                           then Value (plus
((plus_semigroup_add o semigroup_add_numeral o numeral_semiring_numeral o
   semiring_numeral_semiring_1 o semiring_1_comm_semiring_1)
  A3_)
(minus A1_ ord (of_char A3_ char_0x41))
(numeral
  ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
     semiring_1_comm_semiring_1)
    A3_)
  (Bit0 (Bit1 (Bit0 One)))))
                           else Error (InvalidCodepoint (c, radix))))))
  end;

fun map_result_error f (Error e) = Error (f e)
  | map_result_error f (Value v) = Value v;

fun power A_ a n =
  (if equal_nat n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun nat_of_string_radix uu [] = Error EmptyString
  | nat_of_string_radix radix [c] =
    map_result_error to_nat_of_string_radix_error
      (of_char_radix (minus_nat, ord_nat, comm_semiring_1_nat) radix c)
  | nat_of_string_radix radix (c :: v :: va) =
    let
      val num_result =
        of_char_radix (minus_nat, ord_nat, comm_semiring_1_nat) radix c;
      val num_resulta =
        map_result_error to_nat_of_string_radix_error num_result;
    in
      bind num_resulta
        (fn d =>
          map_result_value
            (plus_nata
              (times_nata (power power_nat radix (size_list (v :: va))) d))
            (nat_of_string_radix radix (v :: va)))
    end;

fun parse_nat_radix radix (CNode (str, x :: xs)) =
  Error (CParseArgumentError ("nat: " ^ str, zero_nata, size_list (x :: xs)))
  | parse_nat_radix radix (CNode (str, [])) =
    map_result_error ParseNatError (nat_of_string_radix radix (explode str));

fun parse_typ (CNode (typ, ast)) =
  (if ((typ : string) = "Imm")
    then (if equal_nat (size_list ast) one_nata
           then map_result_value Imm
                  (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                    (nth ast zero_nata))
           else Error (CParseArgumentError ("Imm", one_nata, size_list ast)))
    else (if ((typ : string) = "Mem")
           then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
                  then map_result_value2 (fn a => fn b => Mem (a, b))
                         (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                           (nth ast zero_nata))
                         (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                           (nth ast one_nata))
                  else Error (CParseArgumentError
                               ("Mem", nat_of_integer (2 : IntInf.int),
                                 size_list ast)))
           else Error (CParseTagInvalid (["Imm", "Mem"], typ))));

fun size_literal xa = size_list (explode xa);

fun parse_str (CNode (str, x :: xs)) =
  Error (CParseArgumentError ("str: " ^ str, zero_nata, size_list (x :: xs)))
  | parse_str (CNode (str, [])) =
    (if less_eq_nat (nat_of_integer (2 : IntInf.int)) (size_literal str) andalso
          (equal_chara (hd (explode str)) char_0x22 andalso
            equal_chara (last (explode str)) char_0x22)
      then Value (map ascii_of (tl (butlast (explode str))))
      else Error (CStringMustBeQuoted str));

fun parse_var (CNode (var, ast)) =
  (if ((var : string) = "Var")
    then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
           then map_result_value2 (fn a => fn b => CVar (a, b))
                  (map_result_value implode (parse_str (nth ast zero_nata)))
                  (parse_typ (nth ast one_nata))
           else Error (CParseArgumentError
                        ("Var", nat_of_integer (2 : IntInf.int),
                          size_list ast)))
    else Error (CParseTagInvalid (["Var"], var)));

fun map_OfStringRadixError f EmptyString = EmptyString
  | map_OfStringRadixError f (InvalidRadixa x2) = InvalidRadixa (f x2)
  | map_OfStringRadixError f (InvalidCodepointa (x31, x32)) =
    InvalidCodepointa (x31, f x32);

fun integer_of_int (Int_of_integer k) = k;

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun times_int k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

val char_0x2D : char = Chr (45 : IntInf.int);

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun map_result f1 f2 (Value x1) = Value (f1 x1)
  | map_result f1 f2 (Error x2) = Error (f2 x2);

val one_int : int = Int_of_integer (1 : IntInf.int);

fun int_of_string [] = Error EmptyString
  | int_of_string (c :: str) =
    (if equal_chara c char_0x2D
      then map_result_value (fn x => times_int x (uminus_int one_int))
             (map_result int_of_nat (map_OfStringRadixError int_of_nat)
               (nat_of_string_radix (nat_of_integer (10 : IntInf.int)) str))
      else map_result int_of_nat (map_OfStringRadixError int_of_nat)
             (nat_of_string_radix (nat_of_integer (10 : IntInf.int))
               (c :: str)));

fun parse_int (CNode (str, x :: xs)) =
  Error (CParseArgumentError ("int: " ^ str, zero_nata, size_list (x :: xs)))
  | parse_int (CNode (str, [])) =
    map_result_error ParseIntError (int_of_string (explode str));

fun map_result_value4 uu (Error e) uv uw ux = Error e
  | map_result_value4 f (Value v) u s t = map_result_value3 (f v) u s t;

fun map_result_value5 uu (Error e) uv uw ux uy = Error e
  | map_result_value5 f (Value v) u s t w = map_result_value4 (f v) u s t w;

fun parse_exp (CNode (e, ast)) =
  (if ((e : string) = "Var")
    then map_result_value EVar (parse_var (CNode ("Var", ast)))
    else (if ((e : string) = "Store")
           then (if equal_nat (size_list ast) (nat_of_integer (5 : IntInf.int))
                  then map_result_value5
                         (fn a => fn b => fn c => fn d => fn ea =>
                           Store (a, b, c, d, ea))
                         (parse_exp (nth ast zero_nata))
                         (parse_exp (nth ast one_nata))
                         (parse_en (nth ast (nat_of_integer (3 : IntInf.int))))
                         (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                           (nth ast (nat_of_integer (4 : IntInf.int))))
                         (parse_exp (nth ast (nat_of_integer (2 : IntInf.int))))
                  else Error (CParseArgumentError
                               ("Store", nat_of_integer (5 : IntInf.int),
                                 size_list ast)))
           else (if ((e : string) = "Load")
                  then (if equal_nat (size_list ast)
                             (nat_of_integer (4 : IntInf.int))
                         then map_result_value4
                                (fn a => fn b => fn c => fn d =>
                                  Load (a, b, c, d))
                                (parse_exp (nth ast zero_nata))
                                (parse_exp (nth ast one_nata))
                                (parse_en
                                  (nth ast (nat_of_integer (2 : IntInf.int))))
                                (parse_nat_radix
                                  (nat_of_integer (10 : IntInf.int))
                                  (nth ast (nat_of_integer (3 : IntInf.int))))
                         else Error (CParseArgumentError
                                      ("Load", nat_of_integer (4 : IntInf.int),
size_list ast)))
                  else (if ((e : string) = "Let")
                         then (if equal_nat (size_list ast)
                                    (nat_of_integer (3 : IntInf.int))
                                then map_result_value3
                                       (fn a => fn b => fn c => Let (a, b, c))
                                       (parse_var (nth ast zero_nata))
                                       (parse_exp (nth ast one_nata))
                                       (parse_exp
 (nth ast (nat_of_integer (2 : IntInf.int))))
                                else Error (CParseArgumentError
     ("Let", nat_of_integer (3 : IntInf.int), size_list ast)))
                         else (if ((e : string) = "Ite")
                                then (if equal_nat (size_list ast)
   (nat_of_integer (3 : IntInf.int))
                                       then map_result_value3
      (fn a => fn b => fn c => Ite (a, b, c)) (parse_exp (nth ast zero_nata))
      (parse_exp (nth ast one_nata))
      (parse_exp (nth ast (nat_of_integer (2 : IntInf.int))))
                                       else Error
      (CParseArgumentError
        ("Ite", nat_of_integer (3 : IntInf.int), size_list ast)))
                                else (if ((e : string) = "Extract")
                                       then (if equal_nat (size_list ast)
          (nat_of_integer (3 : IntInf.int))
      then map_result_value3 (fn a => fn b => fn c => Extract (a, b, c))
             (parse_nat_radix (nat_of_integer (10 : IntInf.int))
               (nth ast zero_nata))
             (parse_nat_radix (nat_of_integer (10 : IntInf.int))
               (nth ast one_nata))
             (parse_exp (nth ast (nat_of_integer (2 : IntInf.int))))
      else Error (CParseArgumentError
                   ("Extract", nat_of_integer (3 : IntInf.int), size_list ast)))
                                       else (if ((e : string) = "Int")
      then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
             then map_result_value Val
                    (map_result_value Immediate
                      (map_result_value2 (fn a => fn b => Word (a, b))
                        (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                          (nth ast zero_nata))
                        (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                          (nth ast one_nata))))
             else Error (CParseArgumentError
                          ("Int", nat_of_integer (2 : IntInf.int),
                            size_list ast)))
      else (if ((e : string) = "Unknown")
             then (if equal_nat (size_list ast)
                        (nat_of_integer (2 : IntInf.int))
                    then map_result_value Val
                           (map_result_value2 (fn a => fn b => CUnknown (a, b))
                             (map_result_value implode
                               (parse_str (nth ast zero_nata)))
                             (parse_typ (nth ast one_nata)))
                    else Error (CParseArgumentError
                                 ("Unknown", nat_of_integer (2 : IntInf.int),
                                   size_list ast)))
             else (if ((e : string) = "SLE")
                    then (if equal_nat (size_list ast)
                               (nat_of_integer (2 : IntInf.int))
                           then map_result_value2
                                  (fn e_1 => (fn a => BinOp (e_1, LOp Sle, a)))
                                  (parse_exp (nth ast zero_nata))
                                  (parse_exp (nth ast one_nata))
                           else Error (CParseArgumentError
("SLE", nat_of_integer (2 : IntInf.int), size_list ast)))
                    else (if ((e : string) = "SLT")
                           then (if equal_nat (size_list ast)
                                      (nat_of_integer (2 : IntInf.int))
                                  then map_result_value2
 (fn e_1 => (fn a => BinOp (e_1, LOp Slt, a))) (parse_exp (nth ast zero_nata))
 (parse_exp (nth ast one_nata))
                                  else Error
 (CParseArgumentError ("SLT", nat_of_integer (2 : IntInf.int), size_list ast)))
                           else (if ((e : string) = "MINUS")
                                  then (if equal_nat (size_list ast)
     (nat_of_integer (2 : IntInf.int))
 then map_result_value2 (fn e_1 => (fn a => BinOp (e_1, AOp Minus, a)))
        (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
 else Error (CParseArgumentError
              ("MINUS", nat_of_integer (2 : IntInf.int), size_list ast)))
                                  else (if ((e : string) = "TIMES")
 then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
        then map_result_value2 (fn e_1 => (fn a => BinOp (e_1, AOp Times, a)))
               (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
        else Error (CParseArgumentError
                     ("TIMES", nat_of_integer (2 : IntInf.int), size_list ast)))
 else (if ((e : string) = "DIVIDE")
        then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
               then map_result_value2
                      (fn e_1 => (fn a => BinOp (e_1, AOp Divide, a)))
                      (parse_exp (nth ast zero_nata))
                      (parse_exp (nth ast one_nata))
               else Error (CParseArgumentError
                            ("DIVIDE", nat_of_integer (2 : IntInf.int),
                              size_list ast)))
        else (if ((e : string) = "XOR")
               then (if equal_nat (size_list ast)
                          (nat_of_integer (2 : IntInf.int))
                      then map_result_value2
                             (fn e_1 => (fn a => BinOp (e_1, AOp Xor, a)))
                             (parse_exp (nth ast zero_nata))
                             (parse_exp (nth ast one_nata))
                      else Error (CParseArgumentError
                                   ("XOR", nat_of_integer (2 : IntInf.int),
                                     size_list ast)))
               else (if ((e : string) = "OR")
                      then (if equal_nat (size_list ast)
                                 (nat_of_integer (2 : IntInf.int))
                             then map_result_value2
                                    (fn e_1 => (fn a => BinOp (e_1, AOp Or, a)))
                                    (parse_exp (nth ast zero_nata))
                                    (parse_exp (nth ast one_nata))
                             else Error (CParseArgumentError
  ("OR", nat_of_integer (2 : IntInf.int), size_list ast)))
                      else (if ((e : string) = "AND")
                             then (if equal_nat (size_list ast)
(nat_of_integer (2 : IntInf.int))
                                    then map_result_value2
   (fn e_1 => (fn a => BinOp (e_1, AOp And, a))) (parse_exp (nth ast zero_nata))
   (parse_exp (nth ast one_nata))
                                    else Error
   (CParseArgumentError
     ("AND", nat_of_integer (2 : IntInf.int), size_list ast)))
                             else (if ((e : string) = "LT")
                                    then (if equal_nat (size_list ast)
       (nat_of_integer (2 : IntInf.int))
   then map_result_value2 (fn e_1 => (fn a => BinOp (e_1, LOp Lt, a)))
          (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
   else Error (CParseArgumentError
                ("LT", nat_of_integer (2 : IntInf.int), size_list ast)))
                                    else (if ((e : string) = "LE")
   then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
          then map_result_value2 (fn e_1 => (fn a => BinOp (e_1, LOp Le, a)))
                 (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
          else Error (CParseArgumentError
                       ("LE", nat_of_integer (2 : IntInf.int), size_list ast)))
   else (if ((e : string) = "NEQ")
          then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
                 then map_result_value2
                        (fn e_1 => (fn a => BinOp (e_1, LOp Neq, a)))
                        (parse_exp (nth ast zero_nata))
                        (parse_exp (nth ast one_nata))
                 else Error (CParseArgumentError
                              ("NEQ", nat_of_integer (2 : IntInf.int),
                                size_list ast)))
          else (if ((e : string) = "PLUS")
                 then (if equal_nat (size_list ast)
                            (nat_of_integer (2 : IntInf.int))
                        then map_result_value2
                               (fn e_1 => (fn a => BinOp (e_1, AOp Plus, a)))
                               (parse_exp (nth ast zero_nata))
                               (parse_exp (nth ast one_nata))
                        else Error (CParseArgumentError
                                     ("PLUS", nat_of_integer (2 : IntInf.int),
                                       size_list ast)))
                 else (if ((e : string) = "MOD")
                        then (if equal_nat (size_list ast)
                                   (nat_of_integer (2 : IntInf.int))
                               then map_result_value2
                                      (fn e_1 =>
(fn a => BinOp (e_1, AOp Mod, a)))
                                      (parse_exp (nth ast zero_nata))
                                      (parse_exp (nth ast one_nata))
                               else Error (CParseArgumentError
    ("MOD", nat_of_integer (2 : IntInf.int), size_list ast)))
                        else (if ((e : string) = "SMOD")
                               then (if equal_nat (size_list ast)
  (nat_of_integer (2 : IntInf.int))
                                      then map_result_value2
     (fn e_1 => (fn a => BinOp (e_1, AOp SMod, a)))
     (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
                                      else Error
     (CParseArgumentError
       ("SMOD", nat_of_integer (2 : IntInf.int), size_list ast)))
                               else (if ((e : string) = "EQ")
                                      then (if equal_nat (size_list ast)
         (nat_of_integer (2 : IntInf.int))
     then map_result_value2 (fn e_1 => (fn a => BinOp (e_1, LOp Eq, a)))
            (parse_exp (nth ast zero_nata)) (parse_exp (nth ast one_nata))
     else Error (CParseArgumentError
                  ("EQ", nat_of_integer (2 : IntInf.int), size_list ast)))
                                      else (if ((e : string) = "RSHIFT")
     then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
            then map_result_value2
                   (fn e_1 => (fn a => BinOp (e_1, AOp RShift, a)))
                   (parse_exp (nth ast zero_nata))
                   (parse_exp (nth ast one_nata))
            else Error (CParseArgumentError
                         ("RSHIFT", nat_of_integer (2 : IntInf.int),
                           size_list ast)))
     else (if ((e : string) = "ARSHIFT")
            then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
                   then map_result_value2
                          (fn e_1 => (fn a => BinOp (e_1, AOp ARShift, a)))
                          (parse_exp (nth ast zero_nata))
                          (parse_exp (nth ast one_nata))
                   else Error (CParseArgumentError
                                ("ARSHIFT", nat_of_integer (2 : IntInf.int),
                                  size_list ast)))
            else (if ((e : string) = "LSHIFT")
                   then (if equal_nat (size_list ast)
                              (nat_of_integer (2 : IntInf.int))
                          then map_result_value2
                                 (fn e_1 =>
                                   (fn a => BinOp (e_1, AOp LShift, a)))
                                 (parse_exp (nth ast zero_nata))
                                 (parse_exp (nth ast one_nata))
                          else Error (CParseArgumentError
                                       ("LSHIFT",
 nat_of_integer (2 : IntInf.int), size_list ast)))
                   else (if ((e : string) = "LOW")
                          then (if equal_nat (size_list ast)
                                     (nat_of_integer (2 : IntInf.int))
                                 then map_result_value2
(fn a => fn b => Cast (Low, a, b))
(parse_nat_radix (nat_of_integer (10 : IntInf.int)) (nth ast zero_nata))
(parse_exp (nth ast one_nata))
                                 else Error
(CParseArgumentError ("LOW", nat_of_integer (2 : IntInf.int), size_list ast)))
                          else (if ((e : string) = "HIGH")
                                 then (if equal_nat (size_list ast)
    (nat_of_integer (2 : IntInf.int))
then map_result_value2 (fn a => fn b => Cast (High, a, b))
       (parse_nat_radix (nat_of_integer (10 : IntInf.int)) (nth ast zero_nata))
       (parse_exp (nth ast one_nata))
else Error (CParseArgumentError
             ("HIGH", nat_of_integer (2 : IntInf.int), size_list ast)))
                                 else (if ((e : string) = "UNSIGNED")
then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
       then map_result_value2 (fn a => fn b => Cast (Unsigned, a, b))
              (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                (nth ast zero_nata))
              (parse_exp (nth ast one_nata))
       else Error (CParseArgumentError
                    ("UNSIGNED", nat_of_integer (2 : IntInf.int),
                      size_list ast)))
else (if ((e : string) = "SIGNED")
       then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
              then map_result_value2 (fn a => fn b => Cast (Signed, a, b))
                     (parse_nat_radix (nat_of_integer (10 : IntInf.int))
                       (nth ast zero_nata))
                     (parse_exp (nth ast one_nata))
              else Error (CParseArgumentError
                           ("SIGNED", nat_of_integer (2 : IntInf.int),
                             size_list ast)))
       else (if ((e : string) = "Concat")
              then (if equal_nat (size_list ast)
                         (nat_of_integer (2 : IntInf.int))
                     then map_result_value2 (fn a => fn b => Concat (a, b))
                            (parse_exp (nth ast zero_nata))
                            (parse_exp (nth ast one_nata))
                     else Error (CParseArgumentError
                                  ("Concat", nat_of_integer (2 : IntInf.int),
                                    size_list ast)))
              else (if ((e : string) = "NOT")
                     then (if equal_nat (size_list ast) one_nata
                            then map_result_value (fn a => UnOp (Not, a))
                                   (parse_exp (nth ast zero_nata))
                            else Error (CParseArgumentError
 ("NOT", one_nata, size_list ast)))
                     else (if ((e : string) = "NEG")
                            then (if equal_nat (size_list ast) one_nata
                                   then map_result_value (fn a => UnOp (Neg, a))
  (parse_exp (nth ast zero_nata))
                                   else Error
  (CParseArgumentError ("NEG", one_nata, size_list ast)))
                            else Error (CParseTagInvalid
 (["Store", "Load", "Var", "Let", "Int", "Unknown", "NOT", "NEG", "SLE", "SLT",
    "MINUS", "TIMES", "DIVIDE", "XOR", "OR", "AND", "LT", "LE", "NEQ", "PLUS",
    "MOD", "SMOD", "EQ", "RSHIFT", "ARSHIFT", "LSHIFT", "LOW", "HIGH",
    "UNSIGNED", "SIGNED", "Ite", "Concat", "Extract"],
   e)))))))))))))))))))))))))))))))))));

fun parse_bil (CNode (str, ast)) =
  (if ((str : string) = "") then flatten_error (map parse_stmt ast)
    else Error (CTagExistsError str))
and parse_stmt (CNode (stmt, ast)) =
  (if ((stmt : string) = "Move")
    then (if equal_nat (size_list ast) (nat_of_integer (2 : IntInf.int))
           then map_result_value2 (fn a => fn b => Move (a, b))
                  (parse_var (nth ast zero_nata)) (parse_exp (nth ast one_nata))
           else Error (CParseArgumentError
                        ("Move", nat_of_integer (2 : IntInf.int),
                          size_list ast)))
    else (if ((stmt : string) = "Jmp")
           then (if equal_nat (size_list ast) one_nata
                  then map_result_value Jmp (parse_exp (nth ast zero_nata))
                  else Error (CParseArgumentError
                               ("Jmp", one_nata, size_list ast)))
           else (if ((stmt : string) = "CpuExn")
                  then (if equal_nat (size_list ast) one_nata
                         then map_result_value CpuExn
                                (parse_int (nth ast zero_nata))
                         else Error (CParseArgumentError
                                      ("CpuExn", one_nata, size_list ast)))
                  else (if ((stmt : string) = "Special")
                         then (if equal_nat (size_list ast) one_nata
                                then map_result_value CSpecial
                                       (map_result_value implode
 (parse_str (nth ast zero_nata)))
                                else Error (CParseArgumentError
     ("Special", one_nata, size_list ast)))
                         else (if ((stmt : string) = "While")
                                then (if equal_nat (size_list ast)
   (nat_of_integer (2 : IntInf.int))
                                       then map_result_value2
      (fn a => fn b => While (a, b)) (parse_exp (nth ast zero_nata))
      (parse_bil (nth ast one_nata))
                                       else Error
      (CParseArgumentError
        ("While", nat_of_integer (2 : IntInf.int), size_list ast)))
                                else (if ((stmt : string) = "If")
                                       then (if equal_nat (size_list ast)
          (nat_of_integer (3 : IntInf.int))
      then map_result_value3 (fn a => fn b => fn c => If (a, b, c))
             (parse_exp (nth ast zero_nata)) (parse_bil (nth ast one_nata))
             (parse_bil (nth ast (nat_of_integer (2 : IntInf.int))))
      else Error (CParseArgumentError
                   ("If", nat_of_integer (3 : IntInf.int), size_list ast)))
                                       else Error
      (CParseTagInvalid
        (["Move", "Jmp", "CpuExn", "Special", "While", "If"], stmt))))))));

fun splitWhen p (x :: xs) =
  (if p x then [x] :: splitWhen p xs else insert_hd x (splitWhen p xs))
  | splitWhen uu [] = [];

fun join (s :: ss) = s ^ ", " ^ join ss
  | join [] = "";

fun split A_ ca (c :: str) =
  (if eq A_ ca c then [] :: split A_ ca str else insert_hd c (split A_ ca str))
  | split A_ c [] = [];

fun get_prog_addrs_function sz (CAdtFunction (num, str, bil)) =
  map (get_prog_addr sz) bil;

fun get_prog_addrs_section sz (CAdtSection (str, funs)) =
  fold ((fn a => fn b => a @ b) o get_prog_addrs_function sz) funs [];

fun get_prog_addrs sz ast =
  fold ((fn a => fn b => a @ b) o get_prog_addrs_section sz) ast [];

fun is_sub_in_list lst (CAdtFunction (adr, name, ast)) =
  member equal_literal lst name;

val char_0x3A : char = Chr (58 : IntInf.int);

fun parse_adt_insn lines =
  (if equal_nat (size_list lines) (nat_of_integer (2 : IntInf.int)) orelse
        equal_nat (size_list lines) (nat_of_integer (3 : IntInf.int))
    then let
           val linesa =
             (if equal_nat (size_list lines) (nat_of_integer (3 : IntInf.int))
               then drop one_nata lines else lines);
           val headers =
             map trim
               (split equal_char char_0x3A (explode (nth linesa zero_nata)));
         in
           (if less_nat one_nata (size_list headers)
             then let
                    val num =
                      map_result_error ParseNatError
                        (nat_of_string_radix (nat_of_integer (16 : IntInf.int))
                          (nth headers zero_nata));
                  in
                    map_result_value2
                      (fn addr => fn bil =>
                        CAdtInsn (addr, bil, implode (nth headers one_nata)))
                      num ((parse_bil o lexer) (nth linesa one_nata))
                  end
             else Error (CInvalidAdtInsn lines))
         end
    else Error (CInvalidAdtInsn lines));

val char_0x44 : char = Chr (68 : IntInf.int);

val char_0x62 : char = Chr (98 : IntInf.int);

val char_0x63 : char = Chr (99 : IntInf.int);

val char_0x65 : char = Chr (101 : IntInf.int);

val char_0x66 : char = Chr (102 : IntInf.int);

val char_0x69 : char = Chr (105 : IntInf.int);

val char_0x6C : char = Chr (108 : IntInf.int);

val char_0x6D : char = Chr (109 : IntInf.int);

val char_0x6E : char = Chr (110 : IntInf.int);

val char_0x6F : char = Chr (111 : IntInf.int);

val char_0x73 : char = Chr (115 : IntInf.int);

val char_0x74 : char = Chr (116 : IntInf.int);

val char_0x79 : char = Chr (121 : IntInf.int);

fun symbol_table_function (CAdtFunction (address, label, x)) = (label, address);

fun symbol_table_section (CAdtSection (name, funs)) =
  map symbol_table_function funs;

fun get_symbol_table ast =
  fold ((fn a => fn b => a @ b) o symbol_table_section) ast [];

fun get_original_insn_insn (CAdtInsn (num, bil, str)) = (num, str);

fun get_original_insn_function (CAdtFunction (adr, name, ast)) =
  map get_original_insn_insn ast;

fun get_original_insn_section (CAdtSection (str, ast)) =
  fold ((fn a => fn b => a @ b) o get_original_insn_function) ast [];

fun get_original_insn ast =
  fold ((fn a => fn b => a @ b) o get_original_insn_section) ast [];

fun parse_adt_function lines =
  (if less_nat (nat_of_integer (2 : IntInf.int)) (size_list lines)
    then let
           val headers =
             map trim
               (split equal_char char_0x3A (explode (nth lines zero_nata)));
         in
           (if equal_nat (size_list headers) (nat_of_integer (2 : IntInf.int))
             then let
                    val name = tl (butlast (nth headers one_nata));
                    val addr_result =
                      map_result_error ParseNatError
                        (nat_of_string_radix (nat_of_integer (16 : IntInf.int))
                          (nth headers zero_nata));
                    val insn_lines =
                      map explode
                        (drop (nat_of_integer (2 : IntInf.int)) lines);
                    val insn_grouped_lines =
                      splitWhen (fn s => equal_chara (hd s) char_0x28)
                        insn_lines;
                    val insn_results =
                      map parse_adt_insn (map (map implode) insn_grouped_lines);
                    val a = flatten_error insn_results;
                  in
                    map_result_value2
                      (fn addr =>
                        (fn aa => CAdtFunction (addr, implode name, aa)))
                      addr_result a
                  end
             else Error (CInvalidAdtFunction lines))
         end
    else Error (CInvalidAdtFunction lines));

fun parse_adt_section lines =
  (if less_nat one_nata (size_list lines)
    then let
           val section_name =
             trim (drop (size_list
                          [char_0x44, char_0x69, char_0x73, char_0x61,
                            char_0x73, char_0x73, char_0x65, char_0x6D,
                            char_0x62, char_0x6C, char_0x79, char_0x20,
                            char_0x6F, char_0x66, char_0x20, char_0x73,
                            char_0x65, char_0x63, char_0x74, char_0x69,
                            char_0x6F, char_0x6E])
                    (explode (nth lines zero_nata)));
           val function_lines =
             split (equal_list equal_char) []
               (drop (nat_of_integer (2 : IntInf.int)) (map explode lines));
           val function_results =
             map parse_adt_function (map (map implode) function_lines);
           val a = flatten_error function_results;
         in
           map_result_value (fn aa => CAdtSection (implode section_name, aa)) a
         end
    else Error (CInvalidAdtSection lines));

fun parse_adt_program lines =
  let
    val section_lines =
      splitOn
        (prefix equal_char
          [char_0x44, char_0x69, char_0x73, char_0x61, char_0x73, char_0x73,
            char_0x65, char_0x6D, char_0x62, char_0x6C, char_0x79, char_0x20,
            char_0x6F, char_0x66, char_0x20, char_0x73, char_0x65, char_0x63,
            char_0x74, char_0x69, char_0x6F, char_0x6E])
        (map explode lines);
    val a = map parse_adt_section (map (map implode) section_lines);
  in
    flatten_error a
  end;

fun filter_subroutines_section lst (CAdtSection (name, ast)) =
  CAdtSection (name, filter (is_sub_in_list lst) ast);

fun filter_subroutines lst ast = map (filter_subroutines_section lst) ast;

fun get_subroutine_addrs_function (CAdtFunction (adr, name, ast)) =
  (name, map (get_prog_addr (nat_of_integer (64 : IntInf.int))) ast);

fun get_subroutine_addrs_section (CAdtSection (name, ast)) =
  map get_subroutine_addrs_function ast;

fun get_subroutine_addrs ast =
  fold ((fn a => fn b => a @ b) o get_subroutine_addrs_section) ast [];

fun of_string_radix_error_to_string (InvalidCodepointa (c, z)) =
  "Codepoint out of range for radix: " ^ implode [c]
  | of_string_radix_error_to_string (InvalidRadixa z) =
    "The provided radix was too large (max 32)"
  | of_string_radix_error_to_string EmptyString = "Cannot convert empty string";

fun parse_error_to_string (CInvalidAdtSection strs) =
  "Expecting adt section to contain at least two lines: [" ^ join strs ^ "]"
  | parse_error_to_string (CInvalidAdtFunction strs) =
    "Expecting adt function to contain at least two lines: [" ^ join strs ^ "]"
  | parse_error_to_string (CInvalidAdtInsn strs) =
    "Expecting adt insn translation to contain two or three lines: [" ^
      join strs ^
      "]"
  | parse_error_to_string (CTagExistsError str) =
    "Expecting empty string before brackets, received: " ^ str
  | parse_error_to_string (CParseTagInvalid (strs, str)) =
    "Expecting one of [" ^ join strs ^ "], but received: " ^ str
  | parse_error_to_string (CStringMustBeQuoted str) =
    "Expecting string wrapped in quotes, received: " ^ str
  | parse_error_to_string (CParseArgumentError (str, expected, actual)) =
    "Expecting X arguments for \"" ^ str ^ "\", got: Y"
  | parse_error_to_string (ParseIntError ei) =
    of_string_radix_error_to_string ei
  | parse_error_to_string (ParseNatError en) =
    of_string_radix_error_to_string en;

end; (*struct AstParser*)
