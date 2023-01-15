theory Sqrt2_Irrational imports
  Complex_Main
   
begin

proposition "sqrt 2 \<notin> \<rat>"
proof
  define R where "R \<equiv> {n. n > 0 \<and> real n * sqrt 2 \<in> \<nat>}"
  define k where "k \<equiv> Inf R"
  assume "sqrt 2 \<in> \<rat>"
  then obtain p q where "q\<noteq>0" "real p / real q = \<bar>sqrt 2\<bar>"
    by (metis Rats_abs_nat_div_natE)
  then have "R \<noteq> {}"
    by (simp add: R_def field_simps) (metis of_nat_in_Nats)
  then have "k \<in> R"
    by (simp add: Inf_nat_def1 k_def)
  then have kR: "real k * sqrt 2 \<in> \<nat>" and "k > 0"
    by (auto simp add: R_def)
  define x where "x \<equiv> real k * (sqrt 2 - 1)"
  have "x \<in> \<nat>"
    using \<open>0 < k\<close> by (simp add: kR right_diff_distrib' x_def)
  then obtain k' where k': "x = real k'"
    using Nats_cases by blast
  have "k' > 0"
    using \<open>0 < k\<close> k' of_nat_eq_0_iff x_def by fastforce
  have "real k' * sqrt 2 = 2 * k - k * sqrt 2"
    by (simp add: x_def algebra_simps flip: k')
  moreover have "real k' * sqrt 2 \<ge> 0"
    by simp
  ultimately have "real k' * sqrt 2 \<in> \<nat>"
    by (simp add: kR)
  with R_def \<open>0 < k'\<close> have "k' \<in> R"
    by blast
  have "x < real k"
    by (simp add: \<open>0 < k\<close> sqrt2_less_2 x_def)
  then have "k' < k"
    by (simp add: k')
  then show False
    using \<open>k' \<in> R\<close> k_def linorder_not_less wellorder_Inf_le1 by auto
qed

end
