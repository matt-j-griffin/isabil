structure Fun : sig
  val id : 'a -> 'a
end = struct

fun id x = (fn xa => xa) x;

end; (*struct Fun*)

structure Product_Type : sig
  val equal_bool : bool -> bool -> bool
end = struct

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

end; (*struct Product_Type*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

end; (*struct Orderings*)

structure Arith : sig
  datatype num = One | Bit0 of num | Bit1 of num
  type int
  type 'a one
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a zero
  val zero : 'a zero -> 'a
  type 'a semigroup_add
  val plus_semigroup_add : 'a semigroup_add -> 'a plus
  type 'a numeral
  val one_numeral : 'a numeral -> 'a one
  val semigroup_add_numeral : 'a numeral -> 'a semigroup_add
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power
  type 'a ab_semigroup_add
  type 'a semigroup_mult
  type 'a semiring
  type 'a mult_zero
  val times_mult_zero : 'a mult_zero -> 'a times
  val zero_mult_zero : 'a mult_zero -> 'a zero
  type 'a monoid_add
  val semigroup_add_monoid_add : 'a monoid_add -> 'a semigroup_add
  val zero_monoid_add : 'a monoid_add -> 'a zero
  type 'a comm_monoid_add
  val ab_semigroup_add_comm_monoid_add :
    'a comm_monoid_add -> 'a ab_semigroup_add
  val monoid_add_comm_monoid_add : 'a comm_monoid_add -> 'a monoid_add
  type 'a semiring_0
  val comm_monoid_add_semiring_0 : 'a semiring_0 -> 'a comm_monoid_add
  val mult_zero_semiring_0 : 'a semiring_0 -> 'a mult_zero
  val semiring_semiring_0 : 'a semiring_0 -> 'a semiring
  type 'a monoid_mult
  type 'a semiring_numeral
  val monoid_mult_semiring_numeral : 'a semiring_numeral -> 'a monoid_mult
  val numeral_semiring_numeral : 'a semiring_numeral -> 'a numeral
  val semiring_semiring_numeral : 'a semiring_numeral -> 'a semiring
  type 'a zero_neq_one
  val one_zero_neq_one : 'a zero_neq_one -> 'a one
  val zero_zero_neq_one : 'a zero_neq_one -> 'a zero
  type 'a semiring_1
  val semiring_numeral_semiring_1 : 'a semiring_1 -> 'a semiring_numeral
  val semiring_0_semiring_1 : 'a semiring_1 -> 'a semiring_0
  val zero_neq_one_semiring_1 : 'a semiring_1 -> 'a zero_neq_one
  val semiring_1_int : int semiring_1
  datatype nat = Zero_nat | Suc of nat
  val plus_nata : nat -> nat -> nat
  val times_nata : nat -> nat -> nat
  type 'a dvd
  val one_nata : nat
  val minus_nata : nat -> nat -> nat
  type 'a minus
  val minus : 'a minus -> 'a -> 'a -> 'a
  val minus_nat : nat minus
  val ord_nat : nat Orderings.ord
  type 'a ab_semigroup_mult
  type 'a comm_semiring
  type 'a comm_semiring_0
  val comm_semiring_comm_semiring_0 : 'a comm_semiring_0 -> 'a comm_semiring
  val semiring_0_comm_semiring_0 : 'a comm_semiring_0 -> 'a semiring_0
  type 'a comm_monoid_mult
  type 'a comm_semiring_1
  val comm_monoid_mult_comm_semiring_1 :
    'a comm_semiring_1 -> 'a comm_monoid_mult
  val comm_semiring_0_comm_semiring_1 : 'a comm_semiring_1 -> 'a comm_semiring_0
  val semiring_1_comm_semiring_1 : 'a comm_semiring_1 -> 'a semiring_1
  val comm_semiring_1_nat : nat comm_semiring_1
  val nat_of_num : num -> nat
  val numeral : 'a numeral -> num -> 'a
  val of_nat : 'a semiring_1 -> nat -> 'a
  val of_bool : 'a zero_neq_one -> bool -> 'a
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

datatype int = Zero_int | Pos of num | Neg of num;

val one_inta : int = Pos One;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One One = Bit0 One;

fun uminus_int (Neg m) = Pos m
  | uminus_int (Pos m) = Neg m
  | uminus_int Zero_int = Zero_int;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun dup (Neg n) = Neg (Bit0 n)
  | dup (Pos n) = Pos (Bit0 n)
  | dup Zero_int = Zero_int;

fun plus_inta (Neg m) (Neg n) = Neg (plus_num m n)
  | plus_inta (Neg m) (Pos n) = sub n m
  | plus_inta (Pos m) (Neg n) = sub m n
  | plus_inta (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_inta Zero_int l = l
  | plus_inta k Zero_int = k
and sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit0 n) = plus_inta (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub (Bit0 m) One = Pos (bitM m)
  | sub One One = Zero_int
and minus_int (Neg m) (Neg n) = sub n m
  | minus_int (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_int (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_int (Pos m) (Pos n) = sub m n
  | minus_int Zero_int l = uminus_int l
  | minus_int k Zero_int = k;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = Zero_int} : int zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  int numeral;

fun times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
  | times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n)
  | times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n))
  | times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n))
  | times_num One n = n
  | times_num m One = m;

fun times_inta (Neg m) (Neg n) = Pos (times_num m n)
  | times_inta (Neg m) (Pos n) = Neg (times_num m n)
  | times_inta (Pos m) (Neg n) = Neg (times_num m n)
  | times_inta (Pos m) (Pos n) = Pos (times_num m n)
  | times_inta Zero_int l = Zero_int
  | times_inta k Zero_int = Zero_int;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

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

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : int semiring;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  int mult_zero;

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

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : int semiring_0;

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

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : int monoid_mult;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : int semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : int semiring_1;

datatype nat = Zero_nat | Suc of nat;

fun plus_nata (Suc m) n = plus_nata m (Suc n)
  | plus_nata Zero_nat n = n;

fun times_nata Zero_nat n = Zero_nat
  | times_nata (Suc m) n = plus_nata n (times_nata m n);

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nata : nat = Suc Zero_nat;

val one_nat = {one = one_nata} : nat one;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nat = {zero = Zero_nat} : nat zero;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun minus_nata (Suc m) (Suc n) = minus_nata m n
  | minus_nata Zero_nat n = Zero_nat
  | minus_nata m Zero_nat = m;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true
and less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat Orderings.ord;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

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

fun nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nata m m)
                          end
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nata m m
                          end
  | nat_of_num One = one_nata;

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

fun of_nat_aux A_ inc Zero_nat i = i
  | of_nat_aux A_ inc (Suc n) i = of_nat_aux A_ inc n (inc i);

fun of_nat A_ n =
  of_nat_aux A_
    (fn i =>
      plus ((plus_semigroup_add o semigroup_add_numeral o
              numeral_semiring_numeral o semiring_numeral_semiring_1)
             A_)
        i (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1)
                 A_)))
    n (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
              A_));

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

end; (*struct Arith*)

structure List : sig
  val rev : 'a list -> 'a list
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val butlast : 'a list -> 'a list
  val tl : 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val dropWhile : ('a -> bool) -> 'a list -> 'a list
  val takeWhile : ('a -> bool) -> 'a list -> 'a list
end = struct

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun null [] = true
  | null (x :: xs) = false;

fun foldr f [] = Fun.id
  | foldr f (x :: xs) = f x o foldr f xs;

fun butlast [] = []
  | butlast (x :: xs) = (if null xs then [] else x :: butlast xs);

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun takeWhile p [] = []
  | takeWhile p (x :: xs) = (if p x then x :: takeWhile p xs else []);

end; (*struct List*)

structure Groups_List : sig
  val horner_sum : 'b Arith.comm_semiring_0 -> ('a -> 'b) -> 'b -> 'a list -> 'b
end = struct

fun horner_sum B_ f a xs =
  List.foldr
    (fn x => fn b =>
      Arith.plus
        ((Arith.plus_semigroup_add o Arith.semigroup_add_monoid_add o
           Arith.monoid_add_comm_monoid_add o Arith.comm_monoid_add_semiring_0 o
           Arith.semiring_0_comm_semiring_0)
          B_)
        (f x)
        (Arith.times
          ((Arith.times_mult_zero o Arith.mult_zero_semiring_0 o
             Arith.semiring_0_comm_semiring_0)
            B_)
          a b))
    xs (Arith.zero
         ((Arith.zero_mult_zero o Arith.mult_zero_semiring_0 o
            Arith.semiring_0_comm_semiring_0)
           B_));

end; (*struct Groups_List*)

structure Str : sig
  datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool
  val equal_char : char -> char -> bool
  val of_char : 'a Arith.comm_semiring_1 -> char -> 'a
end = struct

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun digit0 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x1;

fun digit1 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x2;

fun digit2 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x3;

fun digit3 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x4;

fun digit4 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x5;

fun digit5 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x6;

fun digit6 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x7;

fun digit7 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x8;

fun equal_char (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  Product_Type.equal_bool x1 y1 andalso
    (Product_Type.equal_bool x2 y2 andalso
      (Product_Type.equal_bool x3 y3 andalso
        (Product_Type.equal_bool x4 y4 andalso
          (Product_Type.equal_bool x5 y5 andalso
            (Product_Type.equal_bool x6 y6 andalso
              (Product_Type.equal_bool x7 y7 andalso
                Product_Type.equal_bool x8 y8))))));

fun of_char A_ c =
  Groups_List.horner_sum (Arith.comm_semiring_0_comm_semiring_1 A_)
    (Arith.of_bool
      ((Arith.zero_neq_one_semiring_1 o Arith.semiring_1_comm_semiring_1) A_))
    (Arith.numeral
      ((Arith.numeral_semiring_numeral o Arith.semiring_numeral_semiring_1 o
         Arith.semiring_1_comm_semiring_1)
        A_)
      (Arith.Bit0 Arith.One))
    [digit0 c, digit1 c, digit2 c, digit3 c, digit4 c, digit5 c, digit6 c,
      digit7 c];

end; (*struct Str*)

structure Option : sig
  val bind : 'a option -> ('a -> 'b option) -> 'b option
  val the : 'a option -> 'a
  val map_option : ('a -> 'b) -> 'a option -> 'b option
end = struct

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun the (SOME x2) = x2;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

end; (*struct Option*)

structure Bitvector_Syntax : sig
  datatype word = Word of Arith.nat * Arith.nat
end = struct

datatype word = Word of Arith.nat * Arith.nat;

end; (*struct Bitvector_Syntax*)

structure Type_Syntax : sig
  datatype typea = Imm of Arith.nat | Mem of Arith.nat * Arith.nat
end = struct

datatype typea = Imm of Arith.nat | Mem of Arith.nat * Arith.nat;

end; (*struct Type_Syntax*)

structure BIL_Syntax : sig
  datatype aOp = Plus | Minus | Times | Divide | SDivide | Mod | SMod | And | Or
    | Xor | LShift | RShift | ARShift
  datatype lOp = Eq | Neq | Lt | Le | Slt | Sle
  datatype endian = LittleEndian | BigEndian
  datatype binOp = AOp of aOp | LOp of lOp
  datatype unOp = Neg | Not
  datatype cast = Unsigned | Signed | High | Low
  datatype var = Vara of Str.char list * Type_Syntax.typea
  datatype vala = Immediate of Bitvector_Syntax.word |
    Unknown of Str.char list * Type_Syntax.typea |
    Storage of vala * Bitvector_Syntax.word * vala * Arith.nat
  datatype exp = Val of vala | Var of var |
    Load of exp * exp * endian * Arith.nat |
    Store of exp * exp * endian * Arith.nat * exp | BinOp of exp * binOp * exp |
    UnOp of unOp * exp | Cast of cast * Arith.nat * exp | Let of var * exp * exp
    | Ite of exp * exp * exp | Extract of Arith.nat * Arith.nat * exp |
    Concat of exp * exp
  datatype stmt = Move of var * exp | Jmp of exp | CpuExn of Arith.int |
    Special of Str.char list | While of exp * stmt list |
    If of exp * stmt list * stmt list
end = struct

datatype aOp = Plus | Minus | Times | Divide | SDivide | Mod | SMod | And | Or |
  Xor | LShift | RShift | ARShift;

datatype lOp = Eq | Neq | Lt | Le | Slt | Sle;

datatype endian = LittleEndian | BigEndian;

datatype binOp = AOp of aOp | LOp of lOp;

datatype unOp = Neg | Not;

datatype cast = Unsigned | Signed | High | Low;

datatype var = Vara of Str.char list * Type_Syntax.typea;

datatype vala = Immediate of Bitvector_Syntax.word |
  Unknown of Str.char list * Type_Syntax.typea |
  Storage of vala * Bitvector_Syntax.word * vala * Arith.nat;

datatype exp = Val of vala | Var of var | Load of exp * exp * endian * Arith.nat
  | Store of exp * exp * endian * Arith.nat * exp | BinOp of exp * binOp * exp |
  UnOp of unOp * exp | Cast of cast * Arith.nat * exp | Let of var * exp * exp |
  Ite of exp * exp * exp | Extract of Arith.nat * Arith.nat * exp |
  Concat of exp * exp;

datatype stmt = Move of var * exp | Jmp of exp | CpuExn of Arith.int |
  Special of Str.char list | While of exp * stmt list |
  If of exp * stmt list * stmt list;

end; (*struct BIL_Syntax*)

structure ADT_Lexer : sig
  type ast
  val parse_string : Str.char list -> BIL_Syntax.stmt list
end = struct

datatype ast = Node of Str.char list * ast list;

fun triml x =
  List.dropWhile
    (fn xa =>
      Str.equal_char xa
        (Str.Chara
          (false, false, false, false, false, true, false, false)) orelse
        Str.equal_char xa
          (Str.Chara (true, false, false, true, false, false, false, false)))
    x;

fun trimr x = (List.rev o triml o List.rev) x;

fun trim x = (triml o trimr) x;

fun insert_hd x [] = [[x]]
  | insert_hd x (y :: ys) = (x :: y) :: ys;

fun split_string [] uu = []
  | split_string
    (Str.Chara (false, false, true, true, false, true, false, false) :: cs)
    Arith.Zero_nat = [] :: split_string cs Arith.Zero_nat
  | split_string
    (Str.Chara (false, false, false, true, false, true, false, false) :: cs) ctr
    = insert_hd
        (Str.Chara (false, false, false, true, false, true, false, false))
        (split_string cs (Arith.plus_nata ctr Arith.one_nata))
  | split_string
    (Str.Chara (true, false, false, true, false, true, false, false) :: cs) ctr
    = insert_hd
        (Str.Chara (true, false, false, true, false, true, false, false))
        (split_string cs (Arith.minus_nata ctr Arith.one_nata));

fun split s = split_string s Arith.Zero_nat;

fun lexer str =
  let
    val tstr = trim str;
    val name =
      List.takeWhile
        (fn x =>
          not (Str.equal_char x
                (Str.Chara
                  (false, false, false, true, false, true, false, false))))
        tstr;
    val bargstr =
      List.dropWhile
        (fn x =>
          not (Str.equal_char x
                (Str.Chara
                  (false, false, false, true, false, true, false, false))))
        tstr;
    val argstr = List.butlast (List.tl bargstr);
  in
    Node (name, List.map lexer (split argstr))
  end;

fun parse_en
  (Node ([Str.Chara (false, false, true, true, false, false, true, false),
           Str.Chara (true, false, false, true, false, true, true, false),
           Str.Chara (false, false, true, false, true, true, true, false),
           Str.Chara (false, false, true, false, true, true, true, false),
           Str.Chara (false, false, true, true, false, true, true, false),
           Str.Chara (true, false, true, false, false, true, true, false),
           Str.Chara (true, false, true, false, false, false, true, false),
           Str.Chara (false, true, true, true, false, true, true, false),
           Str.Chara (false, false, true, false, false, true, true, false),
           Str.Chara (true, false, false, true, false, true, true, false),
           Str.Chara (true, false, false, false, false, true, true, false),
           Str.Chara (false, true, true, true, false, true, true, false)],
          []))
  = BIL_Syntax.LittleEndian
  | parse_en
    (Node ([Str.Chara (false, true, false, false, false, false, true, false),
             Str.Chara (true, false, false, true, false, true, true, false),
             Str.Chara (true, true, true, false, false, true, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (false, true, true, true, false, true, true, false),
             Str.Chara (false, false, true, false, false, true, true, false),
             Str.Chara (true, false, false, true, false, true, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (false, true, true, true, false, true, true, false)],
            []))
    = BIL_Syntax.BigEndian;

fun of_char_ord (A1_, A2_, A3_) c =
  let
    val ord = Str.of_char A3_ c;
  in
    (if Orderings.less A2_ ord
          (Str.of_char A3_
            (Str.Chara
              (false, false, false, false, true, true, false, false))) orelse
          Orderings.less A2_
            (Str.of_char A3_
              (Str.Chara (true, false, false, true, true, true, false, false)))
            ord
      then NONE
      else SOME (Arith.minus A1_ ord
                  (Str.of_char A3_
                    (Str.Chara
                      (false, false, false, false, true, true, false, false)))))
  end;

fun nat_of_string [] = NONE
  | nat_of_string [c] =
    of_char_ord (Arith.minus_nat, Arith.ord_nat, Arith.comm_semiring_1_nat) c
  | nat_of_string (c :: v :: va) =
    Option.bind
      (of_char_ord (Arith.minus_nat, Arith.ord_nat, Arith.comm_semiring_1_nat)
        c)
      (fn d =>
        Option.map_option
          (Arith.plus_nata
            (Arith.times_nata
              (Arith.nat_of_num
                (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))
              d))
          (nat_of_string (v :: va)));

fun parse_nat (Node (str, [])) = Option.the (nat_of_string str)
  | parse_nat (Node (str, x :: xs)) = (raise Fail "undefined");

fun parse_typ
  (Node ([Str.Chara (true, false, false, true, false, false, true, false),
           Str.Chara (true, false, true, true, false, true, true, false),
           Str.Chara (true, false, true, true, false, true, true, false)],
          [sz]))
  = Type_Syntax.Imm (parse_nat sz)
  | parse_typ
    (Node ([Str.Chara (true, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, true, true, false),
             Str.Chara (true, false, true, true, false, true, true, false)],
            [sz_a_d_d_r, sz_m_e_m]))
    = Type_Syntax.Mem (parse_nat sz_a_d_d_r, parse_nat sz_m_e_m);

fun parse_str (Node (str, [])) = str
  | parse_str (Node (str, x :: xs)) = (raise Fail "undefined");

fun parse_var
  (Node ([Str.Chara (false, true, true, false, true, false, true, false),
           Str.Chara (true, false, false, false, false, true, true, false),
           Str.Chara (false, true, false, false, true, true, true, false)],
          [str, typ]))
  = BIL_Syntax.Vara (parse_str str, parse_typ typ);

fun parse_exp
  (Node ([Str.Chara (true, true, false, false, true, false, true, false),
           Str.Chara (false, false, true, false, true, true, true, false),
           Str.Chara (true, true, true, true, false, true, true, false),
           Str.Chara (false, true, false, false, true, true, true, false),
           Str.Chara (true, false, true, false, false, true, true, false)],
          [e_1, e_2, en, sz, e_3]))
  = BIL_Syntax.Store
      (parse_exp e_1, parse_exp e_2, parse_en en, parse_nat sz, parse_exp e_3)
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, true, true, true, false, true, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (false, false, true, false, false, true, true, false)],
            [e_1, e_2, en, sz]))
    = BIL_Syntax.Load (parse_exp e_1, parse_exp e_2, parse_en en, parse_nat sz)
  | parse_exp
    (Node ([Str.Chara (false, true, true, false, true, false, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (false, true, false, false, true, true, true, false)],
            asts))
    = BIL_Syntax.Var
        (parse_var
          (Node ([Str.Chara
                    (false, true, true, false, true, false, true, false),
                   Str.Chara
                     (true, false, false, false, false, true, true, false),
                   Str.Chara
                     (false, true, false, false, true, true, true, false)],
                  asts)))
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, true, true, false),
             Str.Chara (false, false, true, false, true, true, true, false)],
            [var, e_1, e_2]))
    = BIL_Syntax.Let (parse_var var, parse_exp e_1, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, true, false, true, true, false),
             Str.Chara (false, false, true, false, true, true, true, false)],
            [num, sz]))
    = BIL_Syntax.Val
        (BIL_Syntax.Immediate
          (Bitvector_Syntax.Word (parse_nat num, parse_nat sz)))
  | parse_exp
    (Node ([Str.Chara (true, false, true, false, true, false, true, false),
             Str.Chara (false, true, true, true, false, true, true, false),
             Str.Chara (true, true, false, true, false, true, true, false),
             Str.Chara (false, true, true, true, false, true, true, false),
             Str.Chara (true, true, true, true, false, true, true, false),
             Str.Chara (true, true, true, false, true, true, true, false),
             Str.Chara (false, true, true, true, false, true, true, false)],
            [str, t]))
    = BIL_Syntax.Val (BIL_Syntax.Unknown (parse_str str, parse_typ t))
  | parse_exp
    (Node ([Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, true, true, true, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e]))
    = BIL_Syntax.UnOp (BIL_Syntax.Not, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (true, true, true, false, false, false, true, false)],
            [e]))
    = BIL_Syntax.UnOp (BIL_Syntax.Neg, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Sle, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Slt, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, true, true, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, true, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Minus, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, false, true, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (true, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Times, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, false, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, false, true, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, false, true, false, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Divide, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, false, true, true, false, true, false),
             Str.Chara (true, true, true, true, false, false, true, false),
             Str.Chara (false, true, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Xor, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, true, true, true, false, false, true, false),
             Str.Chara (false, true, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Or, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, false, false, false, false, true, false),
             Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (false, false, true, false, false, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.And, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Lt, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Le, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (true, false, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Neq, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, false, false, true, false, true, false),
             Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, true, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.Plus, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (true, false, false, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.LOp BIL_Syntax.Eq, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, true, false, false, true, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, false, true, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, false, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.RShift, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, false, false, false, false, true, false),
             Str.Chara (false, true, false, false, true, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, false, true, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, false, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.ARShift, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, false, true, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, false, false, false, true, false),
             Str.Chara (false, false, true, false, true, false, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.BinOp
        (parse_exp e_1, BIL_Syntax.AOp BIL_Syntax.LShift, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (false, false, true, true, false, false, true, false),
             Str.Chara (true, true, true, true, false, false, true, false),
             Str.Chara (true, true, true, false, true, false, true, false)],
            [num, e]))
    = BIL_Syntax.Cast (BIL_Syntax.Low, parse_nat num, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (false, false, false, true, false, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (true, true, true, false, false, false, true, false),
             Str.Chara (false, false, false, true, false, false, true, false)],
            [num, e]))
    = BIL_Syntax.Cast (BIL_Syntax.High, parse_nat num, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (true, false, true, false, true, false, true, false),
             Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (true, true, true, false, false, false, true, false),
             Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (false, false, true, false, false, false, true, false)],
            [num, e]))
    = BIL_Syntax.Cast (BIL_Syntax.Unsigned, parse_nat num, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (true, true, true, false, false, false, true, false),
             Str.Chara (false, true, true, true, false, false, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (false, false, true, false, false, false, true, false)],
            [num, e]))
    = BIL_Syntax.Cast (BIL_Syntax.Signed, parse_nat num, parse_exp e)
  | parse_exp
    (Node ([Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, false, true, false, true, true, true, false),
             Str.Chara (true, false, true, false, false, true, true, false)],
            [e_1, e_2, e_3]))
    = BIL_Syntax.Ite (parse_exp e_1, parse_exp e_2, parse_exp e_3)
  | parse_exp
    (Node ([Str.Chara (true, true, false, false, false, false, true, false),
             Str.Chara (true, true, true, true, false, true, true, false),
             Str.Chara (false, true, true, true, false, true, true, false),
             Str.Chara (true, true, false, false, false, true, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (false, false, true, false, true, true, true, false)],
            [e_1, e_2]))
    = BIL_Syntax.Concat (parse_exp e_1, parse_exp e_2)
  | parse_exp
    (Node ([Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (false, false, false, true, true, true, true, false),
             Str.Chara (false, false, true, false, true, true, true, false),
             Str.Chara (false, true, false, false, true, true, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (true, true, false, false, false, true, true, false),
             Str.Chara (false, false, true, false, true, true, true, false)],
            [sz_1, sz_2, e]))
    = BIL_Syntax.Extract (parse_nat sz_1, parse_nat sz_2, parse_exp e);

fun parse_bil (Node ([], ast)) = List.map parse_stmt ast
  | parse_bil (Node (x :: xs, uu)) = (raise Fail "undefined")
and parse_stmt
  (Node ([Str.Chara (true, false, true, true, false, false, true, false),
           Str.Chara (true, true, true, true, false, true, true, false),
           Str.Chara (false, true, true, false, true, true, true, false),
           Str.Chara (true, false, true, false, false, true, true, false)],
          [var, e]))
  = BIL_Syntax.Move (parse_var var, parse_exp e)
  | parse_stmt
    (Node ([Str.Chara (false, true, false, true, false, false, true, false),
             Str.Chara (true, false, true, true, false, true, true, false),
             Str.Chara (false, false, false, false, true, true, true, false)],
            [e]))
    = BIL_Syntax.Jmp (parse_exp e)
  | parse_stmt
    (Node ([Str.Chara (true, true, false, false, false, false, true, false),
             Str.Chara (false, false, false, false, true, true, true, false),
             Str.Chara (true, false, true, false, true, true, true, false),
             Str.Chara (true, false, true, false, false, false, true, false),
             Str.Chara (false, false, false, true, true, true, true, false),
             Str.Chara (false, true, true, true, false, true, true, false)],
            [num]))
    = BIL_Syntax.CpuExn (Arith.of_nat Arith.semiring_1_int (parse_nat num))
  | parse_stmt
    (Node ([Str.Chara (true, true, false, false, true, false, true, false),
             Str.Chara (false, false, false, false, true, true, true, false),
             Str.Chara (true, false, true, false, false, true, true, false),
             Str.Chara (true, true, false, false, false, true, true, false),
             Str.Chara (true, false, false, true, false, true, true, false),
             Str.Chara (true, false, false, false, false, true, true, false),
             Str.Chara (false, false, true, true, false, true, true, false)],
            [str]))
    = BIL_Syntax.Special (parse_str str)
  | parse_stmt
    (Node ([Str.Chara (true, true, true, false, true, false, true, false),
             Str.Chara (false, false, false, true, false, true, true, false),
             Str.Chara (true, false, false, true, false, true, true, false),
             Str.Chara (false, false, true, true, false, true, true, false),
             Str.Chara (true, false, true, false, false, true, true, false)],
            [e_1, bil]))
    = BIL_Syntax.While (parse_exp e_1, parse_bil bil)
  | parse_stmt
    (Node ([Str.Chara (true, false, false, true, false, false, true, false),
             Str.Chara (false, true, true, false, false, true, true, false)],
            [e_1, bil_2, bil_3]))
    = BIL_Syntax.If (parse_exp e_1, parse_bil bil_2, parse_bil bil_3);

fun parse_string x = (parse_bil o lexer) x;

end; (*struct ADT_Lexer*)
