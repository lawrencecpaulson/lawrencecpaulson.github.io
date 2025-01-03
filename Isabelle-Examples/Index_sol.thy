theory Index_sol
  imports "HOL-Computational_Algebra.Primes"

begin

lemma primepow_divides_prod:
  fixes p::nat
  assumes "prime p" "(p^k) dvd (m * n)"
  shows "\<exists>i j. (p^i) dvd m \<and> (p^j) dvd n \<and> k = i + j"
  using assms prime_elem_power_dvd_prod by blast

lemma maximum_index:
  fixes n::nat
  assumes "n > 0" "2 \<le> p"
  shows "\<exists>k. p^k dvd n \<and> (\<forall>l>k. \<not> p^l dvd n)"
proof
  let ?K = "{k. p^k dvd n}"
  have "\<exists>x. p ^ x dvd n"
    by (metis one_dvd power_0)
  then have "?K \<noteq> {}"
    by auto
  moreover
  have "\<And>m. p ^ m dvd n \<Longrightarrow> m \<le> n"
    by (meson assms dvd_imp_le le_trans self_le_ge2_pow)
  then have "{k. p^k dvd n} \<subseteq> {..n}"
    by auto
  then have "finite ?K"
    using finite_subset by blast
  ultimately
  show "p^Max ?K dvd n \<and> (\<forall>l> Max ?K. \<not> p^l dvd n)"
    using Max_in by auto
qed

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index p n 
    \<equiv> if p \<le> 1 \<or> n = 0 then 0 else card {j. 1 \<le> j \<and> p^j dvd n}"

proposition pow_divides_index:
  "p^k dvd n \<longleftrightarrow> n = 0 \<or> p = 1 \<or> k \<le> index p n"
proof (cases "n = 0 \<or> p < 2")
  case True
  then show ?thesis
    by (force simp: index_def)
next
  case False
  then obtain a where "p^a dvd n \<and> (\<forall>l>a. \<not> p^l dvd n)"
    using maximum_index [of n p] False by auto
  then have "p^k dvd n \<longleftrightarrow> k \<le> a" for k
    by (meson le_less_linear power_le_dvd)
  moreover have "{j. 1 \<le> j \<and> j \<le> a} = {1..a}"
    by auto
  ultimately show ?thesis
    using False by (simp add: index_def)
qed

corollary le_index:
  "k \<le> index p n \<longleftrightarrow> (n = 0 \<or> p = 1 \<longrightarrow> k = 0) \<and> p^k dvd n"
  using index_def pow_divides_index by fastforce

corollary exp_index_divides: "p^(index p n) dvd n"
  by (simp add: pow_divides_index)

lemma index_trivial_bound: "index p n \<le> n"
proof (cases "p \<le> 1 \<or> n = 0")
  case True
  then show ?thesis
    by (simp add: index_def)
next
  case False
  have "index p n \<le> p^(index p n)"
    using False by auto
  also have "\<dots> \<le> n"
    using False dvd_imp_le exp_index_divides by auto
  finally show ?thesis .
qed

proposition index_mult:
  assumes "prime p" "m > 0" "n > 0"
  shows "index p (m * n) = index p m + index p n"
proof (rule order_antisym)
  have "p \<ge> 2"
    by (simp add: \<open>prime p\<close> prime_ge_2_nat)
  then obtain i j where "p^i dvd m" "p^j dvd n" "index p (m * n) = i + j"
    using assms(1) exp_index_divides primepow_divides_prod by meson
  then show "index p (m * n) \<le> index p m + index p n"
    using assms pow_divides_index by auto
  show "index p m + index p n \<le> index p (m * n)"
    using assms by (auto simp: le_index power_add exp_index_divides mult_dvd_mono)
qed

corollary index_exp:
  assumes "prime p"
  shows "index p (n^k) = k * index p n"
proof (cases "n = 0")
  case True
  then show ?thesis
    by (auto simp: index_def)
next
  case False
  show ?thesis
  proof (induction k)
    case 0
    with assms show ?case
      by (auto simp: index_def)
  next
    case (Suc k)
    then show ?case
      using False assms index_mult by auto
  qed
qed

end
