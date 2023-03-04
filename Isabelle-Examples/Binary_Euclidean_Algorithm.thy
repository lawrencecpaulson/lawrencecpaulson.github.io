theory Binary_Euclidean_Algorithm 
  imports "HOL-Computational_Algebra.Primes" 
begin

subsection \<open>The binary GCD algorithm\<close>

inductive_set  bgcd :: "(nat \<times> nat \<times> nat) set" where
  bgcdZero: "(u, 0, u) \<in> bgcd"
| bgcdEven: "\<lbrakk> (u, v, g) \<in> bgcd \<rbrakk> \<Longrightarrow> (2*u, 2*v, 2*g) \<in> bgcd"
| bgcdOdd:  "\<lbrakk> (u, v, g) \<in> bgcd; \<not> 2 dvd v \<rbrakk> \<Longrightarrow> (2*u, v, g) \<in> bgcd"
| bgcdStep: "\<lbrakk> (u - v, v, g) \<in> bgcd; v \<le> u \<rbrakk> \<Longrightarrow> (u, v, g) \<in> bgcd"
| bgcdSwap: "\<lbrakk> (v, u, g) \<in> bgcd \<rbrakk> \<Longrightarrow> (u, v, g) \<in> bgcd"

subsection \<open>Proving that the algorithm is correct\<close>

text \<open>Show that the bgcd of @{text x} und @{text y} is
really a divisor of both numbers\<close>
lemma bgcd_divides: "(x,y,g) \<in> bgcd \<Longrightarrow> g dvd x \<and> g dvd y"
proof (induct rule: bgcd.induct)
  case (bgcdStep u v g)
  with dvd_diffD show ?case
    by blast
qed auto

text \<open>The bgcd of @{text x} und @{text y} really is the greatest common divisor
 of both numbers, with respect to the divides relation.\<close>
lemma bgcd_greatest:
  "(x,y,g) \<in> bgcd \<Longrightarrow> d dvd x \<Longrightarrow> d dvd y \<Longrightarrow> d dvd g"
proof (induct arbitrary: d rule: bgcd.induct)
  case (bgcdEven u v g d) 
  show ?case
    proof (cases "2 dvd d") 
      case True thus ?thesis using bgcdEven by (force simp add: dvd_def) 
    next
      case False
      thus ?thesis using bgcdEven
        by (simp add: coprime_dvd_mult_right_iff)
    qed
next
  case (bgcdOdd u v g d)
  hence "coprime d 2"
    by fastforce
  thus ?case using bgcdOdd
    by (simp add: coprime_dvd_mult_right_iff)
qed auto

subsection \<open>Proving uniqueness and existence\<close>

text \<open>despite its apparent non-determinism, the relation @{text bgcd} is deterministic 
  and therefore defines a function\<close>
lemma bgcd_unique: 
  "(x,y,g) \<in> bgcd \<Longrightarrow> (x,y,g') \<in> bgcd \<Longrightarrow> g = g'"
  by (meson bgcd_divides bgcd_greatest gcd_nat.strict_iff_not)

lemma bgcd_defined_aux: "a+b \<le> n \<Longrightarrow> \<exists>g. (a, b, g) \<in> bgcd"
proof (induction n arbitrary: a b rule: less_induct)
  case (less n a b)
  show ?case
  proof (cases b)
    case 0
    thus ?thesis by (metis bgcdZero) 
  next
    case (Suc b')
    then have *: "a + b' < n"
      using Suc_le_eq add_Suc_right less.prems by presburger
    show ?thesis
    proof (cases "b \<le> a")
      case True
      thus ?thesis
        by (metis bgcd.simps le_add1 le_add_diff_inverse less.IH [OF *])
    next
      case False
      then show ?thesis
        by (metis less.IH [OF *] Suc Suc_leI bgcd.simps le_add_diff_inverse 
            less_add_same_cancel2 nle_le zero_less_iff_neq_zero)
    qed
  qed
qed

theorem bgcd_defined: "\<exists>!g. (a, b, g) \<in> bgcd"
  using bgcd_defined_aux bgcd_unique by auto

text \<open>Alternative proof suggested by YawarRaza7349\<close>
lemma "a+b = n \<Longrightarrow> \<exists>g. (a, b, g) \<in> bgcd"
proof (induction n arbitrary: a b rule: less_induct)
  case (less n a b)
  then show ?case
  proof (cases "b \<le> a")
    case True
    with less obtain g where "(a-b, b, g) \<in> bgcd"
      by (metis add_cancel_right_right bgcd.simps le_add1 le_add_diff_inverse nat_less_le)
    thus ?thesis
      using True bgcd.bgcdStep by blast
  next
    case False
    with less show ?thesis
      by (metis bgcd.simps le_add_diff_inverse less_add_same_cancel2 nle_le zero_less_iff_neq_zero)
  qed
qed

end 

