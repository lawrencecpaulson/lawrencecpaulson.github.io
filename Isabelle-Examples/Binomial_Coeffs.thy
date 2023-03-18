theory Binomial_Coeffs
imports Complex_Main "HOL-Number_Theory.Fib"
begin

lemma choose_row_sum: "(\<Sum>k\<le>n. n choose k) = 2^n"
  using binomial [of 1 "1" n] by (simp add: numeral_2_eq_2)

text\<open>sums of binomial coefficients.\<close>
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

lemma choose_mult_lemma:
  "((m+r+k) choose (m+k)) * ((m+k) choose k) = ((m+r+k) choose k) * ((m+r) choose m)"
  (is "?lhs = _")
proof -
  have "?lhs =
      fact(m+r+k) div (fact(m+k) * fact(m+r-m)) * (fact(m+k) div (fact k * fact m))"
    by (simp add: binomial_altdef_nat)
  also have "\<dots> = fact(m+r+k) * fact(m+k) div
                 (fact(m+k) * fact(m+r-m) * (fact k * fact m))"
    by (metis add_implies_diff add_le_mono1 choose_dvd diff_cancel2 div_mult_div_if_dvd
        le_add1 le_add2)
  also have "\<dots> = fact(m+r+k) div (fact r * (fact k * fact m))"
    by (auto simp: algebra_simps fact_fact_dvd_fact)
  also have "\<dots> = (fact(m+r+k) * fact(m+r)) div (fact r * (fact k * fact m) * fact(m+r))"
    by simp
  also have "\<dots> =
      (fact(m+r+k) div (fact k * fact(m+r)) * (fact(m+r) div (fact r * fact m)))"
    by (smt (verit) fact_fact_dvd_fact div_mult_div_if_dvd mult.assoc mult.commute)
  finally show ?thesis
    by (simp add: binomial_altdef_nat mult.commute)
qed

text \<open>The "Subset of a Subset" identity.\<close>
lemma choose_mult:
  "k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (n choose m) * (m choose k) = (n choose k) * ((n - k) choose (m - k))"
  using choose_mult_lemma [of "m-k" "n-m" k] by simp


text \<open>Concrete Mathematics, 5.18: "this formula is easily verified by induction on m"\<close>
lemma choose_row_sum_weighted:
  "(\<Sum>k\<le>m. (r choose k) * (r/2 - k)) = (Suc m)/2 * (r choose (Suc m))"
proof (induction m)
  case 0 show ?case by simp
next
  case (Suc m)
  have "(\<Sum>k\<le>Suc m. real (r choose k) * (r/2 - k)) 
      = ((r choose Suc m) * (r/2 - (Suc m))) + (Suc m) / 2 * (r choose Suc m)"
    by (simp add: Suc)
  also have "\<dots> = (r choose Suc m) * (real r - (Suc m)) / 2"
    by (simp add: field_simps)
  also have "\<dots> = Suc (Suc m) / 2 * (r choose Suc (Suc m))"
  proof (cases "r \<ge> Suc m")
    case True with binomial_absorb_comp[of r "Suc m"] show ?thesis
      by (metis binomial_absorption mult.commute of_nat_diff of_nat_mult times_divide_eq_left)
  qed (simp add: binomial_eq_0)
  finally show ?case .
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

end
