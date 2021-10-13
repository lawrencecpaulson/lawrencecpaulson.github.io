section \<open>Fib and Gcd commute\<close>

theory Fibonacci
  imports "HOL-Computational_Algebra.Primes"
begin

text \<open>A few proofs of laws taken from Graham et al. @{cite "concrete-math"}.\<close>

subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat" where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

lemma fib_positive: "fib (Suc n) > 0"
  by (induction n rule: fib.induct) auto

subsection \<open>Fib and gcd commute\<close>

lemma fib_add: "fib (n + Suc k) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  by (induction n rule: fib.induct) (auto simp: distrib_left)

lemma coprime_fib_Suc: "coprime (fib n) (fib (Suc n))"
proof (induction n rule: fib.induct)
  case (3 x)
  then show ?case
    by (metis coprime_iff_gcd_eq_1 fib.simps(3) gcd.commute gcd_add1)
qed auto

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
proof (cases m)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  have "gcd (fib m) (fib (n + m))
           = gcd (fib k * fib n) (fib (Suc k))"
    by (metis Suc fib_add gcd.commute gcd_add_mult mult.commute)
  also have "\<dots> = gcd (fib n) (fib (Suc k))"
    using coprime_commute coprime_fib_Suc gcd_mult_left_left_cancel by blast
  also have "\<dots> = gcd (fib m) (fib n)"
    using Suc by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gcd_fib_diff: "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)" if "m \<le> n"
proof -
  have "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib (n - m + m))"
    by (simp add: gcd_fib_add)
  also from \<open>m \<le> n\<close> have "n - m + m = n"
    by simp
  finally show ?thesis .
qed

lemma gcd_fib_mod: "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" if "0 < m"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof -
    have "n mod m = (if n < m then n else (n - m) mod m)"
      by (rule mod_if)
    also have "gcd (fib m) (fib \<dots>) = gcd (fib m) (fib n)"
      using gcd_fib_diff less.IH that by fastforce
    finally show ?thesis .
  qed
qed

theorem fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
proof (induction m n rule: gcd_nat_induct)
  case (step m n)
  then show ?case
    by (metis gcd.commute gcd_fib_mod gcd_red_nat)
qed auto

end
