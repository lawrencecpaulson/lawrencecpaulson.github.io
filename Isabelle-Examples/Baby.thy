section \<open>Baby examples\<close>

theory Baby 
  imports "HOL-Library.Sum_of_Squares" 
          "HOL-Decision_Procs.Approximation"
          "HOL-Analysis.Analysis"

begin

text \<open>a simplification rule for powers\<close>
thm power_Suc

text \<open>Kevin Buzzard's examples\<close>
lemma
  fixes x::real
  shows "(x+y)*(x+2*y)*(x+3*y) = x^3 + 6*x^2*y + 11*x*y^2 + 6*y^3"
  by (simp add: algebra_simps eval_nat_numeral)

lemma "sqrt 2 + sqrt 3 < sqrt 10"
proof -
  have "(sqrt 2 + sqrt 3)^2 < (sqrt 10)^2"
  proof (simp add: algebra_simps eval_nat_numeral)
    have "(2 * (sqrt 2 * sqrt 3))^2 < 5 ^ 2"
      by (simp add: algebra_simps eval_nat_numeral)
    then show "2 * (sqrt 2 * sqrt 3) < 5"
      by (smt (verit, best) power_mono)
  qed
  then show ?thesis
    by (simp add: real_less_rsqrt)
qed

lemma "sqrt 2 + sqrt 3 < sqrt 10"
  by (approximation 10)

lemma "x \<in> {0.999..1.001} \<Longrightarrow> \<bar>pi - 4 * arctan x\<bar> < 0.0021"
  by (approximation 20)

lemma "3.141592635389 < pi"
  by (approximation 30)

lemma
  fixes a::real
  shows "(a*b + b * c + c*a)^3 \<le> (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c*a + a^2)"
  by sos

lemma "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain q::rat where "sqrt 2 = of_rat q"
    using Rats_cases by blast
  then have "q^2 = 2"
    by (metis abs_numeral of_rat_eq_iff of_rat_numeral_eq of_rat_power power2_eq_square 
              real_sqrt_mult_self)
  then obtain m n where "coprime m n" "q = of_int m / of_int n"
    by (metis Fract_of_int_quotient Rat_cases)
  then have "of_int m ^ 2 / of_int n ^ 2 = (2::rat)"
    by (metis \<open>q\<^sup>2 = 2\<close> power_divide)
  then have 2: "of_int m ^ 2 = (2::rat) * of_int n ^ 2"
    by (metis division_ring_divide_zero double_eq_0_iff mult_2_right mult_zero_right 
              nonzero_divide_eq_eq)
  then have "2 dvd m"
    by (metis (mono_tags, lifting) even_mult_iff even_numeral of_int_eq_iff of_int_mult 
              of_int_numeral power2_eq_square)
  then obtain r where "m = 2*r"
    by blast
  then have "2 dvd n"
    by (smt (verit) "2" \<open>even m\<close> dvdE even_mult_iff mult.left_commute mult_cancel_left of_int_1 
            of_int_add of_int_eq_iff of_int_mult one_add_one power2_eq_square)
  then show False
    using \<open>coprime m n\<close> \<open>m = 2 * r\<close> by simp
qed

subsection \<open>Material for a later post, about descriptions\<close>


lemma 
  fixes \<B> :: "'a::metric_space set set" and L :: "nat list set"
  assumes "\<S> \<subseteq> {ball x r | x r. r>0}" and "L \<noteq> {}"
  shows "P \<S> L"
proof -
  have "\<And>B. B \<in> \<S> \<Longrightarrow> \<exists>x. \<exists>r>0. B = ball x r"
    using assms by blast
  then obtain centre rad where rad: "\<And>B. B \<in> \<S> \<Longrightarrow> rad B > 0" 
                         and centre: "\<And>B. B \<in> \<S> \<Longrightarrow> B = ball (centre B) (rad B)"
    by metis
  define infrad where "infrad \<equiv> Inf (rad ` \<S>)"
  have "infrad \<le> rad B" if "B \<in> \<S>" for B
    by (smt (verit, best) bdd_below.I cINF_lower image_iff infrad_def rad that)

  have "\<exists>B \<in> \<S>. rad B = infrad" if "finite \<S>" "\<S> \<noteq> {}"
    by (smt (verit) empty_is_image finite_imageI finite_less_Inf_iff imageE infrad_def that)

  define minl where "minl = Inf (length ` L)"
  obtain l0 where  "l0 \<in> L" "length l0 = minl"
    by (metis Inf_nat_def1 empty_is_image imageE minl_def \<open>L \<noteq> {}\<close>)
  then have "length l0 \<le> length l" if "l \<in> L" for l
    by (simp add: cINF_lower minl_def that)

  show ?thesis 
    sorry
qed




end
