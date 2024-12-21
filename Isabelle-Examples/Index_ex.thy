section \<open>Holiday exercises: the greatest prime power divisor\<close>

theory Index_ex
  imports "HOL-Computational_Algebra.Primes"

begin

lemma primepow_divides_prod:
  fixes p::nat
  assumes "prime p" "(p^k) dvd (m * n)"
  shows "\<exists>i j. (p^i) dvd m \<and> (p^j) dvd n \<and> k = i + j"
  sorry

lemma maximum_index:
  fixes n::nat
  assumes "n > 0" "2 \<le> p"
  shows "\<exists>k. p^k dvd n \<and> (\<forall>l>k. \<not> p^l dvd n)"
  sorry

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index p n 
    \<equiv> if p \<le> 1 \<or> n = 0 then 0 else card {j. 1 \<le> j \<and> p^j dvd n}"

proposition pow_divides_index:
  "p^k dvd n \<longleftrightarrow> n = 0 \<or> p = 1 \<or> k \<le> index p n"
  sorry

corollary le_index:
  "k \<le> index p n \<longleftrightarrow> (n = 0 \<or> p = 1 \<longrightarrow> k = 0) \<and> p^k dvd n"
  sorry

corollary exp_index_divides: "p^(index p n) dvd n"
  sorry

lemma index_trivial_bound: "index p n \<le> n"
  sorry

proposition index_mult:
  assumes "prime p" "m > 0" "n > 0"
  shows "index p (m * n) = index p m + index p n"
  sorry

corollary index_exp:
  assumes "prime p"
  shows "index p (n^k) = k * index p n"
  sorry

end
