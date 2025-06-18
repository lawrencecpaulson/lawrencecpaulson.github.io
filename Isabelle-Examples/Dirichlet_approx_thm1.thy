theory Dirichlet_approx_thm1

imports "Complex_Main" "HOL-Library.FuncSet"

begin

lemma floor_eq_imp_diff_1: "\<lfloor>x\<rfloor> = \<lfloor>y\<rfloor> \<Longrightarrow> \<bar>x-y\<bar> < 1"
  unfolding floor_eq_iff by linarith

theorem Dirichlet_approx:
  fixes \<theta>::real and N::nat
  assumes "N > 0" 
  obtains h k where "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
proof -
  define Y where "Y \<equiv> (\<lambda>k::nat. {k/N..< Suc k/N}) ` {..<N}"
  have caY: "card Y \<le> N" "finite Y"
    unfolding Y_def using card_image_le by force+
  define f where "f \<equiv> \<lambda>j. let k = nat \<lfloor>frac (j*\<theta>) * N\<rfloor> in {k/N ..< Suc k/N}"
  have "nat \<lfloor>x * N\<rfloor> < N" if "0 \<le> x" "x < 1" for x::real
    using that assms floor_less_iff nat_less_iff by fastforce
  then have "f \<in> {..N} \<rightarrow> Y"
    unfolding f_def Let_def Y_def Pi_iff image_iff Ico_eq_Ico
    using frac_ge_0 frac_lt_1 by blast
  then have "\<not> inj_on f {..N}"
    using \<open>finite Y\<close> caY card_inj by fastforce
  then obtain c d where cd: "c\<noteq>d" "c \<in> {..N}" "d \<in> {..N}" and eq: "f c = f d"
    by (auto simp: inj_on_def)
  with assms have "\<bar>frac (d*\<theta>) - frac (c*\<theta>)\<bar> < 1 / N"
    by (auto simp: f_def left_diff_distrib pos_less_divide_eq Ico_eq_Ico abs_if 
        dest!: floor_eq_imp_diff_1 split: if_splits)
  with cd obtain a b::nat where *: "a<b" "b\<le>N" "\<bar>frac (b*\<theta>) - frac (a*\<theta>)\<bar> < 1/N"
    by (metis abs_minus_commute atMost_iff linorder_cases)
  let ?k = "b-a" and ?h = "\<lfloor>b*\<theta>\<rfloor> - \<lfloor>a*\<theta>\<rfloor>"
  show ?thesis
  proof
    have "frac (b*\<theta>) - frac (a*\<theta>) = ?k*\<theta> - ?h"
      using \<open>a < b\<close> by (simp add: frac_def left_diff_distrib)
    with * show "\<bar>of_int ?k * \<theta> - ?h\<bar> < 1/N"
      by (metis of_int_of_nat_eq)
  qed (use * in auto)
qed

end
