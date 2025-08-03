section \<open>Definite and finite improper integrals\<close>

theory Improper_Integral 
  imports "HOL-Analysis.Analysis"

begin

lemma "((\<lambda>x. 1 / sqrt(1-x\<^sup>2)) has_integral pi) {-1..1}"
proof -
  have D: "(arcsin has_vector_derivative 1 / sqrt (1 - x\<^sup>2)) (at x)"
    if "- 1 < x" "x < 1" for x
    unfolding has_real_derivative_iff_has_vector_derivative [symmetric]
    by (rule refl derivative_eq_intros | use that in \<open>simp add: divide_simps\<close>)+
  show ?thesis
    using fundamental_theorem_of_calculus_interior [OF _ continuous_on_arcsin' D]
    by auto
qed

lemma "((\<lambda>x. 1 / sqrt x) has_integral 2) {0..1}"
proof -
  define f where "f \<equiv> \<lambda>x. 2 * sqrt x"
  have "(f has_vector_derivative 1 / sqrt x) (at x)"
    if "0 < x" "x < 1" for x
    unfolding f_def has_real_derivative_iff_has_vector_derivative [symmetric]
    by (rule refl derivative_eq_intros | use that in \<open>simp add: divide_simps\<close>)+
  moreover
  have "continuous_on {0..1} f"
    by (simp add: continuous_on_mult continuous_on_real_sqrt f_def)
  ultimately
  have "((\<lambda>x. 1 / sqrt x) has_integral (f 1 - f 0)) {0..1}"
    by (intro fundamental_theorem_of_calculus_interior) auto
  moreover
  have "f 0 = 0"  "f 1 = 2"
    unfolding f_def by auto
  ultimately show ?thesis 
    by auto
qed


lemma power2_gt_1_iff: "x\<^sup>2 > 1 \<longleftrightarrow> x < (-1 :: 'a :: linordered_idom) \<or> x > 1"
  using power2_ge_1_iff [of x] power2_eq_1_iff [of x] by auto

text \<open>As above but not using @{term arcsin}, so continuity issues\<close>
lemma "((\<lambda>x. 1 / sqrt(1-x\<^sup>2)) has_integral pi) {-1..1}"
proof -
  note one_ereal_def [simp] power2_eq_1_iff [simp] power2_gt_1_iff [simp]
  define f where "f \<equiv> \<lambda>x. arctan (x / sqrt(1 - x\<^sup>2))"
  have "(f has_real_derivative 1 / sqrt (1 - x\<^sup>2)) (at x)"
    if "- 1 < ereal x" "ereal x < 1" for x
    unfolding f_def has_real_derivative_iff_has_vector_derivative [symmetric]
    apply (rule refl derivative_eq_intros | use that in force)+
    apply (simp add: power2_eq_square divide_simps)
    done
  moreover
  have "isCont (\<lambda>x. 1 / sqrt (1 - x\<^sup>2)) x"
    if "- 1 < ereal x" "ereal x < 1" for x
    using that by (intro continuous_intros) auto
  moreover
  have "AE x in lborel. - 1 < ereal x \<longrightarrow> ereal x < 1 \<longrightarrow> 0 \<le> 1 / sqrt (1 - x\<^sup>2)"
    by (auto simp: square_le_1)
  moreover
  have "(f \<longlongrightarrow> - pi / 2) (at_right (- 1))"  "(f \<longlongrightarrow> pi / 2) (at_left 1)"
    unfolding f_def by real_asymp+
  then have "((f \<circ> real_of_ereal) \<longlongrightarrow> - pi / 2) (at_right (- 1))"
    "((f \<circ> real_of_ereal) \<longlongrightarrow> pi / 2) (at_left 1)"
    by (simp_all add: ereal_tendsto_simps1)
  ultimately have 
    "set_integrable lborel {-1<..<1} (\<lambda>x. 1 / sqrt (1 - x\<^sup>2))"
    "(LBINT x=-1..1. 1 / sqrt (1 - x\<^sup>2)) = pi"
    using interval_integral_FTC_nonneg [of "-1" 1 f "\<lambda>x. 1 / sqrt (1 - x\<^sup>2)" "-pi/2" "pi/2"]
    by auto
  moreover have "einterval (- 1) 1 = {-1<..<1}"
    by (auto simp: einterval_def)
  ultimately show ?thesis
    unfolding has_integral_integrable_integral integral_open_interval_real interval_lebesgue_integral_def
    by (simp add: integrable_on_Icc_iff_Ioo set_borel_integral_eq_integral)
qed



(*TRY THIS*)
thm interval_integral_Icc_approx_integrable

text \<open>This lemma packages up a reference to @{thm[source]monotone_convergence_increasing}}\<close>
lemma has_integral_to_inf:
  fixes h ::"real \<Rightarrow> real"
  assumes int: "\<And>y::real. h integrable_on {a..y}"
    and lim: "((\<lambda>y. integral {a..y} h) \<longlongrightarrow> l) at_top"
    and nonneg: "\<And>y. y \<ge> a \<Longrightarrow> h y \<ge> 0"
  shows "(h has_integral l) {a..}"
proof -
  have ge: "integral {a..y} h \<ge> 0" for y
    by (meson Henstock_Kurzweil_Integration.integral_nonneg atLeastAtMost_iff int nonneg)
  then have "l \<ge> 0"
    using tendsto_lowerbound [OF lim] by simp 
  have "mono (\<lambda>y. integral {a..y} h)"
    by (simp add: int integral_subset_le monoI nonneg)
  then have int_le_l: "integral {a..y} h \<le> l" for y
    using order_tendstoD [OF lim, of "integral {a..y} h"]
    by (smt (verit) eventually_at_top_linorder monotoneD nle_le)
  define f where "f \<equiv> \<lambda>n x. if x \<in> {a..of_nat n} then h x else 0"
  have has_integral_f: "\<And>n. (f n has_integral (integral {a..of_nat n} h)) {a..}"
    unfolding f_def
    by (metis (no_types, lifting) ext Icc_subset_Ici_iff order.refl
        has_integral_restrict int integrable_integral)

  have integral_f: "integral {a..} (f n) = (if n \<ge> a then integral {a..of_nat n} h else 0)" for n
    by (meson atLeastAtMost_iff f_def has_integral_f has_integral_iff has_integral_is_0 order_trans)
  have *: "h integrable_on {a..} \<and> (\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> integral {a..} h"
  proof (intro monotone_convergence_increasing allI ballI)
    fix n
    show "f n integrable_on {a..}"
      using has_integral_f by blast
  next
    fix n x
    show "f n x \<le> f (Suc n) x" using nonneg by (auto simp: f_def)
  next
    fix x :: real assume x: "x \<in> {a..}"
    have "eventually (\<lambda>n. real n \<ge> x) at_top"
      by (simp add: eventually_nat_real)
    with x have "eventually (\<lambda>n. f n x = h x) at_top"
      by (simp add: eventually_mono f_def)
    thus "(\<lambda>n. f n x) \<longlonglongrightarrow> h x" by (simp add: tendsto_eventually)
  next
    have "norm (integral {a..} (f n)) \<le> l" for n
      by (simp add: \<open>0 \<le> l\<close> ge int_le_l integral_f)
    thus "bounded (range(\<lambda>k. integral {a..} (f k)))"
      by (metis (no_types, lifting) boundedI rangeE)
  qed
  have "eventually (\<lambda>n. integral {a..n} h = integral {a..} (f n)) at_top"
    by (metis (mono_tags, lifting) eventuallyI has_integral_f integral_unique)
  moreover have "((\<lambda>y. integral {a..y} h) \<circ> real) \<longlonglongrightarrow> l"
    unfolding tendsto_compose_filtermap
    using filterlim_def filterlim_real_sequentially lim tendsto_mono by blast
  ultimately have "(\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> l"
    by (force intro: Lim_transform_eventually)
  then show ?thesis
    using "*" LIMSEQ_unique by blast
qed

text \<open>example\<close>
lemma "((\<lambda>x::real. 1 / x\<^sup>2) has_integral 1) {1..}"  (is "(?g has_integral _) _")
proof (intro has_integral_to_inf)
  fix y
  show "?g integrable_on {1..y}"
    by (intro integrable_continuous_interval continuous_intros) auto
next
  have D: "((\<lambda>x. -1/x) has_vector_derivative ?g x) (at x within {1..y})"
    if "1 \<le> x" for x y
    unfolding  has_real_derivative_iff_has_vector_derivative [symmetric]
    apply (rule refl derivative_eq_intros | use that in force)+
    apply (simp add: power2_eq_square divide_simps)
    done
  then have "(?g has_integral -1/y - (-1)) {1..y}" if "y > 1" for y
    using fundamental_theorem_of_calculus [of 1 y "\<lambda>x. -1/x"] that by auto
  then have "\<forall>\<^sub>F y in at_top. integral {1..y} ?g = 1-1/y"
    using eventually_at_top_dense by force
  moreover have "((\<lambda>y::real. 1-1/y) \<longlongrightarrow> 1) at_top"
    by real_asymp
  ultimately show "((\<lambda>y. integral {1..y} ?g) \<longlongrightarrow> 1) at_top"
    by (simp add: filterlim_cong)
qed auto

thm has_integral_exp_minus_to_infinity
lemma has_integral_exp_minus_to_infinity:
  assumes "a > 0"
  shows   "((\<lambda>x::real. exp (-a*x)) has_integral exp (-a*c)/a) {c..}"
proof (intro has_integral_to_inf integrable_continuous_interval continuous_intros)
  have "((\<lambda>x. exp (-a*x)) has_integral (-exp (-a*y)/a - (-exp (-a*c)/a))) {c..y}"
    if "y \<ge> c" for y
    using that \<open>a > 0\<close>
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: derivative_eq_intros
               simp flip: has_real_derivative_iff_has_vector_derivative)    
  then have "\<forall>\<^sub>F y in at_top. integral {c..y} (\<lambda>x. exp (-a*x)) = -exp (-a*y)/a + exp (-a*c)/a"
    using eventually_at_top_linorder[of
        "\<lambda>y. integral {c..y} (\<lambda>x. exp (-a*x)) = -exp (-a*y)/a + exp (-a*c)/a"]
    by auto
  moreover have "((\<lambda>y::real. -exp (-a*y)/a + exp (-a*c)/a) \<longlongrightarrow> exp (-a*c)/a) at_top"
    using \<open>a > 0\<close> by real_asymp
  ultimately show "((\<lambda>y. integral {c..y} (\<lambda>x. exp (-a*x))) \<longlongrightarrow> exp (-a*c)/a) at_top"
    by (simp add: filterlim_cong)
qed auto

thm has_integral_powr_to_inf
lemma has_integral_powr_to_inf:
  fixes a e :: real
  assumes "e < -1" "a > 0"
  shows   "((\<lambda>x. x powr e) has_integral -(a powr (e+1)) / (e+1)) {a..}"
proof (intro has_integral_to_inf integrable_continuous_interval continuous_intros)
  define F where "F \<equiv> \<lambda>x. x powr (e+1) / (e+1)"
  have "((\<lambda>x. x powr e) has_integral (F y - F a)) {a..y}" if "y \<ge> a" for y
    unfolding F_def using assms
    by (intro fundamental_theorem_of_calculus that)
       (auto intro!: derivative_eq_intros
               simp flip: has_real_derivative_iff_has_vector_derivative)
  then have "\<forall>\<^sub>F y in at_top. integral {a..y} (\<lambda>x. x powr e) = F y - F a"
    by (meson eventually_at_top_linorderI integral_unique)
  moreover have "((\<lambda>y::real. F y - F a) \<longlongrightarrow> - F a) at_top"
    using assms unfolding F_def by real_asymp
  ultimately show "((\<lambda>y. integral {a..y} (\<lambda>x. x powr e)) 
              \<longlongrightarrow> - (a powr (e+1)) / (e+1)) at_top"
    by (simp add: F_def filterlim_cong)
qed (use assms in auto)

end
