section \<open>A tricky example of proving a lower bound\<close>

theory Ln_lower_bound imports
  "HOL-Analysis.Analysis" "HOL-Decision_Procs.Approximation"  "HOL-Real_Asymp.Real_Asymp" 
   
begin

(*example: prove this lower bound of x*ln(x) for all x>0.
It's not differentiable at 0. It is continuous at 0, but that's nontrivial to prove.
And you've got a problem if you think it's not even DEFINED at 0. (It is, of course.)*)

(*The derivative of x * ln(x) is ln(x)+1. It's zero at 1/e and the minimum value is -1/e.
[minimum = -0.3678794412, [x = 0.3678794412]]
*)

text \<open>Thanks to Manuel Eberl\<close>

(*real_asymp proves ((\<lambda>x. x * ln x) \<longlongrightarrow> 0 * ln 0) (at_right 0)*)

lemma continuous_at_0: "continuous (at_right 0) (\<lambda>x::real. x * ln x)"
  unfolding continuous_within by real_asymp

lemma continuous_nonneg: 
  fixes x::real
  assumes "x \<ge> 0"
  shows "continuous (at x within {0..}) (\<lambda>x. x * ln x)"
proof (cases "x = 0")
  case True with continuous_at_0 show ?thesis
    by (force simp add: continuous_within_topological less_eq_real_def)
qed (auto intro!: continuous_intros)

lemma continuous_on_x_ln: "continuous_on {0..} (\<lambda>x::real. x * ln x)"
  unfolding continuous_on_eq_continuous_within
  using continuous_nonneg by blast

lemma xln_deriv:
  fixes x::real
  assumes "x > 0"
  shows "((\<lambda>u. u * ln(u)) has_real_derivative ln x + 1) (at x)"
  by (rule derivative_eq_intros refl | use assms in force)+

theorem x_ln_lowerbound:
  fixes x::real
  assumes "x > 0"
  shows "x * ln(x) \<ge> -1 / exp 1"
proof -
  define xmin::real where "xmin \<equiv> 1 / exp 1"
  have "xmin > 0"
    by (auto simp: xmin_def)
  have eq: "-1 / exp 1 = xmin * ln(xmin)"
    using assms by (simp add: xmin_def ln_div)
  have "x * ln(x) > xmin * ln(xmin)" if "x < xmin"
  proof (intro DERIV_neg_imp_decreasing_open [OF that] exI conjI)
    fix u :: real
    assume "x < u" and "u < xmin" 
    then have "ln u + 1 < ln 1"
      unfolding xmin_def
      by (smt (verit, del_insts) assms exp_diff exp_less_cancel_iff exp_ln_iff)
    then show "ln u + 1 < 0"
      by simp
  next
    show "continuous_on {x..xmin} (\<lambda>u. u * ln u)"
      using continuous_on_x_ln continuous_on_subset assms by fastforce
  qed (use assms xln_deriv in auto)
  moreover
  have "x * ln(x) > xmin * ln(xmin)" if "x > xmin"
  proof (intro DERIV_pos_imp_increasing_open [OF that] exI conjI)
    fix u
    assume "x > u" and "u > xmin" 
    then show "ln u + 1 > 0"
      by (smt (verit, del_insts) \<open>0 < xmin\<close> exp_minus inverse_eq_divide 
          ln_less_cancel_iff ln_unique xmin_def)
  next
    show "continuous_on {xmin..x} (\<lambda>u. u * ln u)"
      using continuous_on_x_ln continuous_on_subset xmin_def by fastforce
  qed (use \<open>0 < xmin\<close> xln_deriv in auto)
  ultimately show ?thesis
    using eq by fastforce
qed


corollary
  fixes x::real
  assumes "x > 0"
  shows "x * ln(x) \<ge> -0.36787944117144233"  (is "_ \<ge> ?rhs")
proof -
  have "(-1::real) / exp 1 \<ge> ?rhs"
    by (approximation 60)
  with x_ln_lowerbound show ?thesis
    using assms by force
qed

end


