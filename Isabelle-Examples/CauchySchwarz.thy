theory CauchySchwarz imports "HOL-Analysis.Analysis"
begin

text \<open>Remark: the predicate @{term concave_on} is now to be found in the standard analysis library, 
as is indeed much of the material below.\<close>

lemma ln_concave: "concave_on {0<..} ln"
  unfolding concave_on_def
  by (rule f''_ge0_imp_convex derivative_eq_intros | simp)+

lemma powr_convex:
  assumes "p \<ge> 1" shows "convex_on {0<..} (\<lambda>x. x powr p)"
  using assms
  by (intro f''_ge0_imp_convex derivative_eq_intros | simp)+

lemma Youngs_inequality_0:
  fixes a::real
  assumes "0 \<le> \<alpha>" "0 \<le> \<beta>" "\<alpha>+\<beta> = 1" "a>0" "b>0"
  shows "a powr \<alpha> * b powr \<beta> \<le> \<alpha>*a + \<beta>*b"
proof -
  have "\<alpha> * ln a + \<beta> * ln b \<le> ln (\<alpha> * a + \<beta> * b)"
    using assms ln_concave by (simp add: concave_on_iff)
  moreover have "0 < \<alpha> * a + \<beta> * b"
    using assms by (smt (verit) mult_pos_pos split_mult_pos_le)
  ultimately show ?thesis
    using assms by (simp add: powr_def mult_exp_exp flip: ln_ge_iff)
qed

lemma Youngs_inequality:
  fixes p::real
  assumes "p>1" "q>1" "1/p + 1/q = 1" "a\<ge>0" "b\<ge>0"
  shows "a * b \<le> a powr p / p + b powr q / q"
proof (cases "a=0 \<or> b=0")
  case False
  then show ?thesis
  using Youngs_inequality_0 [of "1/p" "1/q" "a powr p" "b powr q"] assms
  by (simp add: powr_powr)
qed (use assms in auto)

lemma Cauchy_Schwarz_ineq_sum:
  fixes a :: "'a \<Rightarrow> 'b::linordered_field"
  shows "(\<Sum>i\<in>I. a i * b i)\<^sup>2 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) * (\<Sum>i\<in>I. (b i)\<^sup>2)"
proof (cases "(\<Sum>i\<in>I. (b i)\<^sup>2) > 0")
  case False
  then consider "\<And>i. i\<in>I \<Longrightarrow> b i = 0" | "infinite I"
    by (metis (mono_tags, lifting) sum_pos2 zero_le_power2 zero_less_power2)
  thus ?thesis
    by fastforce
next
  case True
  define r where "r \<equiv> (\<Sum>i\<in>I. a i * b i) / (\<Sum>i\<in>I. (b i)\<^sup>2)"
  have "0 \<le> (\<Sum>i\<in>I. (a i - r * b i)\<^sup>2)"
    by (simp add: sum_nonneg)
  also have "... = (\<Sum>i\<in>I. (a i)\<^sup>2) - 2 * r * (\<Sum>i\<in>I. a i * b i) + r\<^sup>2 * (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: algebra_simps power2_eq_square sum_distrib_left flip: sum.distrib)
  also have "\<dots> = (\<Sum>i\<in>I. (a i)\<^sup>2) - ((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: r_def power2_eq_square)
  finally have "0 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) - ((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2)" .
  hence "((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2) \<le> (\<Sum>i\<in>I. (a i)\<^sup>2)"
    by (simp add: le_diff_eq)
  thus "((\<Sum>i\<in>I. a i * b i))\<^sup>2 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) * (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: pos_divide_le_eq True)
qed

lemma "\<exists>f'. ((\<lambda>x. x^3 + x\<^sup>2) has_real_derivative f' x) (at x) \<and> P (\<lambda>x. f' x)"
  apply (rule exI conjI derivative_eq_intros | simp)+
  oops

lemma "x > 0 \<Longrightarrow> \<exists>f'. ((\<lambda>x. (x\<^sup>2 - 1) * ln x) has_real_derivative f' x) (at x) \<and> P (\<lambda>x. f' x)"
  apply (rule exI conjI derivative_eq_intros | simp)+
  oops

lemma "\<exists>f'. ((\<lambda>x. (sin x)\<^sup>2 + (cos x)\<^sup>2) has_real_derivative f' x) (at x) \<and> P (\<lambda>x. f' x)"
  apply (rule exI conjI derivative_eq_intros | simp)+
  oops

end
