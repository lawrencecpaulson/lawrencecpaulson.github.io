theory Fibonacci_Newbie
  imports Main
begin

fun fib :: "nat \<Rightarrow> nat" where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

lemma fib_positive: "fib (Suc n) > 0"
  by (induction n rule: fib.induct, auto)

lemma fib_add: "fib (Suc (n + k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  by (induction n rule: fib.induct, auto simp: add_mult_distrib2)

lemma coprime_fib_Suc: "coprime (fib n) (fib (Suc n))"
proof (induction n rule: fib.induct)
next
  case (3 n)
  then show ?case
    by (metis coprime_def dvd_add_left_iff fib.simps(3))
qed auto

end
