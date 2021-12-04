theory Calculus
  imports Complex_Main
begin

theorem mvt:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes "a < b"
    and contf: "continuous_on {a..b} \<phi>"
    and derf: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> (\<phi> has_derivative \<phi>' x) (at x)"
  obtains \<xi> where "a < \<xi>" "\<xi> < b" "\<phi> b - \<phi> a = (\<phi>' \<xi>) (b-a)"
proof -
  define f where "f \<equiv> \<lambda>x. \<phi> x - (\<phi> b - \<phi> a) / (b-a) * x"
  have "\<exists>\<xi>. a < \<xi> \<and> \<xi> < b \<and> (\<lambda>y. \<phi>' \<xi> y - (\<phi> b - \<phi> a) / (b-a) * y) = (\<lambda>v. 0)"
  proof (intro Rolle_deriv[OF \<open>a < b\<close>])
    fix x
    assume x: "a < x" "x < b"
    show "(f has_derivative (\<lambda>y. \<phi>' x y - (\<phi> b - \<phi> a) / (b-a) * y)) (at x)"
      unfolding f_def by (intro derivative_intros derf x)
  next
    show "f a = f b"
      using assms by (simp add: f_def field_simps)
  next
    show "continuous_on {a..b} f"
      unfolding f_def by (intro continuous_intros assms)
  qed
  then show ?thesis
    by (smt (verit, ccfv_SIG) pos_le_divide_eq pos_less_divide_eq that)
qed

end
