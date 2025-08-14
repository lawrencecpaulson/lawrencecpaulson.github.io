section \<open>Definite and finite improper integrals\<close>

theory Improper_Integral 
  imports "HOL-Analysis.Analysis"

begin

subsection \<open>Examples for Part I\<close>

text \<open>In both of these, the antiderivative is continuous, but the integrand diverges at an endpoint\<close>

lemma "((\<lambda>x. 1 / sqrt(1-x\<^sup>2)) has_integral pi) {-1..1}"
proof -
  have "(arcsin has_real_derivative 1 / sqrt (1-x\<^sup>2)) (at x)"
    if "- 1 < x" "x < 1" for x 
    by (rule refl derivative_eq_intros | use that in \<open>simp add: divide_simps\<close>)+
  then show ?thesis
    using fundamental_theorem_of_calculus_interior [OF _ continuous_on_arcsin']
    by (auto simp: has_real_derivative_iff_has_vector_derivative)
qed

lemma "((\<lambda>x. 1 / sqrt x) has_integral 2) {0..1}"
proof -
  define f where "f \<equiv> \<lambda>x. 2 * sqrt x"
  have "(f has_real_derivative 1 / sqrt x) (at x)"
    if "0 < x" "x < 1" for x
    unfolding f_def
    by (rule refl derivative_eq_intros | use that in \<open>simp add: divide_simps\<close>)+
  moreover
  have "continuous_on {0..1} f"
    by (simp add: continuous_on_mult continuous_on_real_sqrt f_def)
  ultimately
  have "((\<lambda>x. 1 / sqrt x) has_integral (f 1 - f 0)) {0..1}"
    by (intro fundamental_theorem_of_calculus_interior)
       (auto simp: has_real_derivative_iff_has_vector_derivative)
  then show ?thesis 
    by (auto simp: f_def)
qed

subsection \<open>Examples for Part II\<close>
text \<open>We switch to Lebesgue integration\<close>

lemma power2_gt_1_iff: "x\<^sup>2 > 1 \<longleftrightarrow> x < (-1 :: 'a :: linordered_idom) \<or> x > 1"
  using power2_ge_1_iff [of x] power2_eq_1_iff [of x] by auto

text \<open>Handling a discontinuous antiderivative. Actually the same
  problem as the first, but not using @{term arcsin}.
  The given antiderivative comes from WolframAlpha\<close>
lemma "set_integrable lborel {-1<..<1} (\<lambda>x. 1 / sqrt (1-x\<^sup>2))"
      "(LBINT x=-1..1. 1 / sqrt (1-x\<^sup>2)) = pi"
proof -
  note one_ereal_def [simp] power2_eq_1_iff [simp] power2_gt_1_iff [simp]
  define f where "f \<equiv> \<lambda>x. arctan (x / sqrt(1-x\<^sup>2))"
  have "(f has_real_derivative 1 / sqrt (1-x\<^sup>2)) (at x)"
    if "- 1 < ereal x" "ereal x < 1" for x
    unfolding f_def 
    apply (rule refl derivative_eq_intros | use that in force)+
    apply (simp add: power2_eq_square divide_simps)
    done
  moreover
  have "isCont (\<lambda>x. 1 / sqrt (1-x\<^sup>2)) x"
    if "- 1 < ereal x" "ereal x < 1" for x
    using that by (intro continuous_intros) auto
  moreover
  have "AE x in lborel. - 1 < ereal x \<longrightarrow> ereal x < 1 \<longrightarrow> 0 \<le> 1 / sqrt (1-x\<^sup>2)"
    by (auto simp: square_le_1)
  moreover
  have "(f \<longlongrightarrow> - pi/2) (at_right (- 1))"  "(f \<longlongrightarrow> pi/2) (at_left 1)"
    unfolding f_def by real_asymp+
  then have "((f \<circ> real_of_ereal) \<longlongrightarrow> - pi/2) (at_right (- 1))"
    "((f \<circ> real_of_ereal) \<longlongrightarrow> pi/2) (at_left 1)"
    by (simp_all add: ereal_tendsto_simps1)
  ultimately show 
    "set_integrable lborel {-1<..<1} (\<lambda>x. 1 / sqrt (1-x\<^sup>2))"
    "(LBINT x=-1..1. 1 / sqrt (1-x\<^sup>2)) = pi"
    using interval_integral_FTC_nonneg [of "-1" 1 f "\<lambda>x. 1 / sqrt (1-x\<^sup>2)" "-pi/2" "pi/2"]
    by auto
qed

text \<open>Infinite endpoints, nonnegative integrand\<close>
lemma
  defines "f' \<equiv> \<lambda>t. 1 / (t\<^sup>2+1)"
  shows
    "set_integrable lborel (einterval (-\<infinity>) \<infinity>) f'"
    "(LBINT t=-\<infinity>..\<infinity>. f' t) = pi"
proof -
  have "(arctan has_real_derivative f' t) (at t)" for t
    unfolding f'_def 
    by (rule derivative_eq_intros | force simp: divide_simps)+
  moreover
  have "isCont f' x" for x
    unfolding f'_def
    by (intro continuous_intros) (auto simp: add_nonneg_eq_0_iff) 
  moreover
  have "((arctan \<circ> real_of_ereal) \<longlongrightarrow> -pi/2) (at_right (-\<infinity>))"
       "((arctan \<circ> real_of_ereal) \<longlongrightarrow> pi/2) (at_left \<infinity>)"
    by (simp add: ereal_tendsto_simps1, real_asymp)+
  ultimately show "set_integrable lborel (einterval (-\<infinity>) \<infinity>) f'"
    "interval_lebesgue_integral lborel (-\<infinity>) \<infinity> f' = pi"
    using interval_integral_FTC_nonneg [of "-\<infinity>" \<infinity> arctan]
    by (auto simp: f'_def)
qed 

text \<open>Infinite endpoints, mixed-sign integrand\<close>
lemma
  defines "f' \<equiv> \<lambda>t. exp(-t)*cos(t)"
  shows "(LBINT t=0..\<infinity>. f' t) = 1/2"
proof -
  define f where "f \<equiv> \<lambda>t::real. exp(-t)*(sin(t) - cos(t))/2"
  have "(LBINT t=0..\<infinity>. f' t) = 0 - (- 1/2)"
  proof (intro interval_integral_FTC_integrable)
    fix t
    show "(f has_vector_derivative f' t) (at t)"
      unfolding f_def f'_def has_real_derivative_iff_has_vector_derivative [symmetric]
      by (rule derivative_eq_intros | force simp: field_simps)+
    show "isCont f' t"
      unfolding f'_def by (intro continuous_intros)
    have "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>t. exp(-t))"
    proof (rule interval_integral_FTC_nonneg)
      show "((\<lambda>t. -exp(-t)) has_real_derivative exp(-t)) (at t)" for t
        unfolding f_def f'_def has_real_derivative_iff_has_vector_derivative [symmetric]
        by (rule derivative_eq_intros | force simp: field_simps)+
      have "(((\<lambda>t. -exp (-t)) \<circ> real_of_ereal) \<longlongrightarrow> -1) (at_right (ereal 0))"
        by (simp add: ereal_tendsto_simps1, real_asymp)
      then show "(((\<lambda>t. -exp (-t)) \<circ> real_of_ereal) \<longlongrightarrow> -1) (at_right 0)"
        by (simp add: zero_ereal_def)
      show "(((\<lambda>t. - exp (- t)) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left \<infinity>)"
        by (simp add: ereal_tendsto_simps1 f_def, real_asymp)
    qed auto
    moreover have "set_borel_measurable lborel (einterval 0 \<infinity>) f'"
      using borel_measurable_continuous_on_indicator 
      by (simp add: f'_def set_borel_measurable_def)
    moreover have "\<And>t. \<bar>f' t\<bar> \<le> exp(-t)"
      by (simp add: f'_def abs_mult)
    ultimately show "set_integrable lborel (einterval 0 \<infinity>) f'"
      by (metis (mono_tags, lifting) abs_exp_cancel always_eventually
          real_norm_def set_integrable_bound set_integrable_bound)
    have "((f \<circ> real_of_ereal) \<longlongrightarrow> -1/2) (at_right (ereal 0))"
         "((f \<circ> real_of_ereal) \<longlongrightarrow> 0)   (at_left \<infinity>)"
      by (simp add: ereal_tendsto_simps1 f_def, real_asymp)+
    have "((f \<circ> real_of_ereal) \<longlongrightarrow> -1/2) (at_right (ereal 0))"
      by (simp add: ereal_tendsto_simps1 f_def, real_asymp)
    then show "((f \<circ> real_of_ereal) \<longlongrightarrow> -1/2) (at_right 0)"
      by (simp add: zero_ereal_def)
    show "((f \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left \<infinity>)"
      by (simp add: ereal_tendsto_simps1 f_def, real_asymp)
  qed auto
  then show ?thesis
    by simp
qed 

end
