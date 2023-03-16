theory Binomial_Coeffs
imports Complex_Main "HOL-Number_Theory.Fib"
begin


text\<open>The binomial coefficients arise in the binomial theorem.
They are the elements of Pascal's triangle and satisfy a great many mathematical identities.
Below, we examine some of these. The theory @{theory "HOL.Binomial"}
contains basic definitions and proofs, including the binomial theorem itself:

@{thm[display]binomial[no_vars]}

Many textbooks on discrete mathematics cover binomial coefficients.
Information about them is widely available on the Internet,
including Wikipedia and the lecture course notes available here:

@{text "http://www.cs.columbia.edu/~cs4205/files/CM4.pdf"}

Hint: it follows from the binomial theorem,
which is available under the name @{thm[source]binomial}.
\<close>
lemma choose_row_sum: "(\<Sum>k\<le>n. n choose k) = 2^n"
  using binomial [of 1 "1" n] by (simp add: numeral_2_eq_2)

text\<open>the following two theorems concern sums of binomial coefficients.\<close>
lemma sum_choose_lower:
    "(\<Sum>k\<le>n. (r+k) choose k) = Suc (r+n) choose n"
  by (induction n) auto

lemma sum_choose_upper:
    "(\<Sum>k\<le>n. k choose m) = Suc n choose Suc m"
  by (induction n) auto

lemma sum_choose_diagonal:
  assumes "m\<le>n"
    shows "(\<Sum>k\<le>m. (n-k) choose (m-k)) = Suc n choose m"
proof -
  have "(\<Sum>k\<le>m. (n-k) choose (m-k)) = (\<Sum>k\<le>m. (n-m+k) choose k)"
    using sum.atLeastAtMost_rev [of "\<lambda>k. (n - k) choose (m - k)" 0 m]
    by (simp add: atMost_atLeast0 \<open>m\<le>n\<close>)
  also have "\<dots> = Suc (n-m+m) choose m"
    by (rule sum_choose_lower)
  also have "\<dots> = Suc n choose m" using assms
    by simp
  finally show ?thesis . 
qed

text\<open>The identity $\binom{n}{m} \binom{m}{k} = \binom{n}{k} \binom{n-k}{m-k}$ is straightforward.
But the need to show the necessary divisibility properties complicates the Isabelle proof.
The key result we need is already available as @{thm[source]binomial_fact_lemma}:
@{thm[display]binomial_fact_lemma[no_vars]}

\<close>
lemma fact_fact_dvd_fact_m:
    fixes k::nat
    shows "k \<le> n \<Longrightarrow> fact k * fact (n - k) dvd fact n"
  by (metis binomial_fact_lemma dvd_def of_nat_fact of_nat_mult)

lemma fact_fact_dvd_fact:
    fixes k::nat
    shows "fact k * fact n dvd fact (n + k)"
  by (metis fact_fact_dvd_fact_m diff_add_inverse2 le_add2)

text\<open>Now the identity $\binom{n}{m} \binom{m}{k} = \binom{n}{k} \binom{n-k}{m-k}$ can be
proved by expressing binomial coefficients in terms of factorials:

The equational calculation is still short, but each step requires some justification.
\<close>

lemma choose_mult_lemma:
  "((m + r + k) choose (m + k)) * ((m + k) choose k) = ((m + r + k) choose k) * ((m + r) choose m)"
  (is "?lhs = _")
proof -
  have "?lhs =
      fact (m + r + k) div (fact (m + k) * fact (m + r - m)) * (fact (m + k) div (fact k * fact m))"
    by (simp add: binomial_altdef_nat)
  also have "\<dots> = fact (m + r + k) * fact (m + k) div
                 (fact (m + k) * fact (m + r - m) * (fact k * fact m))"
    by (metis add_implies_diff add_le_mono1 choose_dvd diff_cancel2 div_mult_div_if_dvd le_add1 le_add2)
  also have "\<dots> = fact (m + r + k) div (fact r * (fact k * fact m))"
    by (auto simp: algebra_simps fact_fact_dvd_fact)
  also have "\<dots> = (fact (m + r + k) * fact (m + r)) div (fact r * (fact k * fact m) * fact (m + r))"
    by simp
  also have "\<dots> =
      (fact (m + r + k) div (fact k * fact (m + r)) * (fact (m + r) div (fact r * fact m)))"
    by (smt (verit) Binomial.fact_fact_dvd_fact div_mult_div_if_dvd mult.assoc mult.commute)
  finally show ?thesis
    by (simp add: binomial_altdef_nat mult.commute)
qed

text\<open>
The formulation given above uses addition instead of subtraction,
which tends to complicate proofs about the natural numbers.
Now that the hard work has been done, establish the identity in its conventional form.
\<close>
text \<open>The "Subset of a Subset" identity.\<close>
lemma choose_mult:
  "k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (n choose m) * (m choose k) = (n choose k) * ((n - k) choose (m - k))"
  using choose_mult_lemma [of "m-k" "n-m" k] by simp

text \<open>the following theorem, which relates to a weighted sum of a row of Pascal's triangle.
It involves arithmetic on type @{typ real} as well as @{typ nat}, so the function @{const real}
is implicitly inserted at multiple points.
\<close>

(*Concrete Mathematics, 5.18: "this formula is easily verified by induction on m"*)
lemma choose_row_sum_weighted:
  "(\<Sum>k\<le>m. (r choose k) * (r/2 - k)) = (Suc m)/2 * (r choose (Suc m))"
proof (induction m)
  case 0 show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "r < Suc m")
    case True
    then show ?thesis
      by (simp add: Suc binomial_eq_0)
  next
    case False
    then have "(1 + real m) * (r choose Suc m) + (r choose Suc m) * (r - (2 + real m * 2)) 
             = real (r - Suc m) * (r choose Suc m)"
      by (smt (verit, best) left_diff_distrib mult_of_nat_commute not_less of_nat_Suc of_nat_diff)
    moreover have "(2 + real m) * (r choose Suc (Suc m)) = (r - Suc m) * (r choose Suc m)"
      using binomial_absorption[of "Suc m" r] 
      by (smt (verit, ccfv_SIG) binomial_absorb_comp of_nat_Suc of_nat_add of_nat_mult)
    ultimately show ?thesis
      by (simp add: Suc left_diff_distrib mult.assoc)
  qed
qed

lemma sum_drop_zero: "(\<Sum>k\<le>Suc n. if 0<k then (f (k - 1)) else 0) = (\<Sum>j\<le>n. f j)"
  by (induction n) auto

lemma sum_choose_drop_zero:
  "(\<Sum>k\<le>Suc n. if k = 0 then 0 else (Suc n - k) choose (k - 1)) =
    (\<Sum>j\<le>n. (n-j) choose j)"
  by (rule trans [OF sum.cong sum_drop_zero]) auto

lemma ne_diagonal_fib:
   "(\<Sum>k\<le>n. (n-k) choose k) = fib (Suc n)"
proof (induction n rule: fib.induct)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case (3 n)
  have "(\<Sum>k\<le>Suc n. Suc (Suc n) - k choose k) =
        (\<Sum>k\<le>Suc n. (Suc n - k choose k) + (if k=0 then 0 else (Suc n - k choose (k - 1))))"
    by (rule sum.cong) (simp_all add: choose_reduce_nat)
  also have "\<dots> = (\<Sum>k\<le>Suc n. Suc n - k choose k) +
                   (\<Sum>k\<le>Suc n. if k=0 then 0 else (Suc n - k choose (k - 1)))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>k\<le>Suc n. Suc n - k choose k) + (\<Sum>j\<le>n. n - j choose j)"
    by (metis sum_choose_drop_zero)
  finally show ?case using 3
    by simp
qed

text \<open>
\emph{Remark}: choose your induction rule with care.
The precise statement of the induction formula is also important.
Some of the proofs are best done using calculational reasoning.
\<close>

end
