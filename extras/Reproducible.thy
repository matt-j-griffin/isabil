theory Reproducible
  imports Main
begin

locale Example1 = 
  fixes x :: int
begin

lemma Lemma1: "x \<noteq> 4" sorry

end


locale Example2 = 
  fixes y :: int
begin

sublocale l1: Example1 y 
  .

end


consts z :: int

interpretation l2: Example2 z .

thm l2.l1.Lemma1


context Example1
begin

lemma Lemma2: "x \<noteq> 7" sorry

end






end