theory Cbrt23_Irrational 
  imports Complex_Main
   
begin

lemma cuberoot_irrational:
  defines "x \<equiv> root 3 2 + root 3 3"
  shows "x \<notin> \<rat>"
proof
  assume "x \<in> \<rat>"
  moreover
  have "root 3 8 = 2" "root 3 27 = 3"
    by auto
  then have xcubed: "x^3 = 5 + 3 * x * root 3 6"
    by (simp add: x_def algebra_simps eval_nat_numeral flip: real_root_mult)
  ultimately have Q: "5 + 3 * x * root 3 6 \<in> \<rat>"
    by (metis Rats_power \<open>x \<in> \<rat>\<close>)
  have "root 3 6 \<notin> \<rat>"
  proof 
    assume "root 3 6 \<in> \<rat>"
    then obtain a b where "a / b = root 3 6" and cop: "coprime a b" "b\<noteq>0"
      by (smt (verit, best) Rats_cases')
    then have "(a/b)^3 = 6"
      by auto
    then have eq: "a^3 = 2*3 * b^3" 
      using of_int_eq_iff by (fastforce simp: divide_simps \<open>b\<noteq>0\<close>)
    then have p: "2 dvd a"
      by (metis coprime_left_2_iff_odd coprime_power_right_iff dvd_triv_left mult.assoc)
    then obtain c where "a = 2*c"
      by blast
    with eq have "2 dvd b"
      by (simp add: eval_nat_numeral) (metis even_mult_iff even_numeral odd_numeral)
    with p and cop show False
      by fastforce
  qed
  moreover have "3*x \<in> \<rat> - {0}"
    using xcubed  by (force simp: \<open>x \<in> \<rat>\<close>)
  ultimately have "3 * x * root 3 6 \<notin> \<rat>"
    using Rats_divide by force
  with Q show False
    by (metis Rats_diff Rats_number_of add.commute add_uminus_conv_diff diff_add_cancel)
qed

end
