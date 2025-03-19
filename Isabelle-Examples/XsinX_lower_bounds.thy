theory XsinX_lower_bounds
  imports
    "HOL-Analysis.Analysis"
    "HOL-Decision_Procs.Approximation"
    "HOL-Real_Asymp.Real_Asymp"

begin
(*
Find and prove a lowerbound for \<lambda>x. x*sin(1/x) for all x.
The function continuous on the reals and differentiable everywhere except zero.
We first need some preliminary results
*)

section\<open>Preliminaries\<close>
subsection\<open>Splitting reals\<close>
(*Occasionally helpful to reduce a periodic problem to one in a fixed interval*)
lemma real_splits:
  fixes x d ::real
  assumes "d > 0"
  shows "x - d * floor (x/d) \<ge> 0"
    and "x - d * floor (x/d) < d"
proof-
  let ?res = "x - d * real_of_int \<lfloor>x / d\<rfloor>"
  show "0 \<le> ?res" by simp (metis assms floor_divide_lower mult.commute)
  show "?res < d"
  proof-
    have "?res < d \<longleftrightarrow> (x / d) < (1+floor(x/d))"
      using assms by (simp add:field_split_simps)
    also have "\<dots> \<longleftrightarrow> True" using floor_less_iff by fastforce
    finally show "?res < d" by simp
  qed
qed

lemma real_div_split_coi:
  fixes x offset :: real
  assumes "d > 0"
  obtains k :: int and res ::real where
    "x = res + d*real_of_int k" "res \<in> {offset..<offset+d}"
proof
  let ?k = "floor ((x-offset)/d)"
  let ?res = "x - d*?k"
  show "x = ?res + d*?k" by auto
  show "?res \<in> {offset..<offset+d}"
    using real_splits[OF assms, of "x-offset"] by simp
qed

lemma real_div_split_oci:
  fixes x offset :: real
  assumes "d > 0"
  obtains k :: int and res ::real where
    "x = res + d*real_of_int k" "res \<in> {offset<..offset+d}"
proof
  let ?kraw = "floor ((x-offset)/d)"
  let ?resraw = "x - d*?kraw"
  let ?k = "if ?resraw = offset then ?kraw - 1 else ?kraw"
  and ?res = "if ?resraw = offset then ?resraw+d else ?resraw"
  show "x = ?res + d*real_of_int ?k"
    by (simp add: algebra_simps)
  show "?res \<in> {offset<..offset + d}"
    using real_splits[OF assms, of "x-offset"] by simp
qed

lemma real_div_split0:
  fixes x :: real
  assumes "d > 0"
  obtains k :: int and res ::real where "x = res + d*real_of_int k" "0 \<le> res" "res < d"
  using real_div_split_coi[where ?d = d and ?offset = 0 and ?x = x and ?thesis = thesis, OF assms]
  by simp

subsection\<open>Characterizations on the arguments of bounded cosine\<close>

lemma cos_greater_iff:
  assumes "t \<in> {-1..1}" 
  shows "cos x > (t::real) \<longleftrightarrow> (\<exists>k::int. x \<in> {2*pi*k - arccos t<..<2*pi*k + arccos t})" 
    (is "_ = ?r")
proof(intro iffI)
  obtain res k where k: "x = res + 2*pi*real_of_int k" and res: "res \<in> {-pi<..pi}"
    using real_div_split_oci[of "2*pi" x "-pi" thesis] by (auto simp: algebra_simps)
  hence kbounds: "2*pi*k - pi < x" "x \<le> 2*pi*k + pi" by auto
  define pres where "pres = abs res"
  hence presbd: "0 \<le> pres" "pres \<le> pi" using res by auto
  have "cos x > t \<longleftrightarrow> cos res > t" using k cos_periodic_int by (simp add: mult.commute add.commute)
  also have "\<dots> \<longleftrightarrow> cos pres > t" unfolding pres_def by simp
  also have "\<dots> \<longleftrightarrow> pres < arccos t" using presbd arccos_less_arccos[of t "cos pres"] arccos_cos[of pres]
    assms cos_monotone_0_pi[of pres "arccos t"] arccos_ubound[of t] by auto
  also have "\<dots> \<longleftrightarrow> res \<in> {- arccos t<..<arccos t}" by (auto simp: pres_def)
  finally have equiv: "cos x > t \<longleftrightarrow> res \<in> {-arccos t<..<arccos t}" .
  {
    then show "t < cos x \<Longrightarrow> ?r"
      using k by (auto intro: exI[of _ k])
  }
  {
    assume "?r"
    then obtain k'::int where k': "2*pi*k' - arccos t < x" "x < 2*pi*k' + arccos t" by auto
    hence k'bds:  "2*pi*k' - pi < x" "x < 2*pi*k' + pi" using arccos_lbound arccos_ubound assms by fastforce+
    have "k' = k"
    proof(cases k' k rule: linorder_cases)
      case less
      have "2 * pi * real_of_int k - pi < 2 * pi * real_of_int k' + pi" using kbounds(1) k'bds(2) by linarith
      hence "2 * pi * k < 2 * pi * (k' + 1)" by (auto simp: algebra_simps)
      with less show ?thesis by simp
    next
      case greater
      have "2 * pi * real_of_int k' - pi < 2 * pi * real_of_int k + pi" using kbounds(2) k'bds(1) by linarith
      hence "2 * pi * k' < 2 * pi * (k + 1)" by (auto simp: algebra_simps)
      with greater show ?thesis by simp
    qed
    then show "t < cos x" by (intro equiv[THEN iffD2]) (use res k k' in auto)
  }
qed

lemma cos_geq_iff: 
  assumes "t \<in> {-1..1}"
  shows "cos x \<ge> (t::real) \<longleftrightarrow> (\<exists>k::int. x \<in> {2*pi*k - arccos t..2*pi*k + arccos t})"
  (is "_ = ?r")
proof(cases "cos x = t"; intro iffI)
  case True
  from cos_eq_arccos_Ex[THEN iffD1, OF True] obtain k where
    k: "x = arccos t + 2 * real_of_int k * pi \<or> x = - arccos t + 2 * real_of_int k * pi" by auto
  then show "\<exists>xa. x \<in> {2 * pi * real_of_int xa - arccos t..2 * pi * real_of_int xa + arccos t}"
    using assms by (auto intro!: exI[of _ k] arccos_lbound)
  show "t \<le> cos x" using True by simp
next
  case False
  {
    have [intro]: "\<exists>v. u \<in> {a v<..<b v} \<Longrightarrow> \<exists>v . u\<in>{a v .. b v}" for u :: "_::preorder" and a b
      using less_le_not_le by auto
    assume "t \<le> cos x"
    with False have "t < cos x" by simp
    with cos_greater_iff[OF assms, of x, THEN iffD1]
    show ?r by (auto simp del: greaterThanLessThan_iff atLeastAtMost_iff)
  }
  assume ?r
  then obtain k where "2 * pi * real_of_int k - arccos t \<le> x" "x \<le> 2 * pi * real_of_int k + arccos t"
    by auto
  with False have "2 * pi * real_of_int k - arccos t < x"
    apply (cases "2 * pi * real_of_int k - arccos t = x")
    using cos_periodic_int[of "-arccos t" k] assms by (auto simp: algebra_simps)
  moreover have "x < 2 * pi * real_of_int k + arccos t"
    apply (cases "x = 2 * pi * real_of_int k + arccos t")
    using \<open>x \<le> 2 * pi * real_of_int k + arccos t\<close>
      False cos_periodic_int[of "arccos t" k] assms by (auto simp: algebra_simps)
  ultimately have "t < cos x" using cos_greater_iff[of t x, THEN iffD2, OF assms]
    by auto
  then show "t \<le> cos x" by simp
qed

(*We only need the lemmas below, not the other two above -
They can be proven directly, like cos_greater_iff,
but for varieties sake and because i had already written the above, this remains here *)
lemma cos_less_iff:
  assumes "t \<in> {-1..1}"
  shows "cos x < (t::real) \<longleftrightarrow> (\<exists>k::int. x \<in> {pi * (2*k) + arccos t<..<pi*(2*(k+1)) - arccos t})"
  (is "_ = ?r")
proof-
  have "(\<not> (cos x < t)) = (t \<le> cos x)" by auto
  also have "\<dots> =  (\<exists>k::int. x \<in> {2*pi*k - arccos t..2*pi*k + arccos t})"
    using assms by (fact cos_geq_iff)
  also have "\<dots> = (\<not> ( ?r))"
  proof (safe)
    fix k l assume asm: "x \<in> {2 * pi * real_of_int k - arccos t..2 * pi * real_of_int k + arccos t}"
      "x \<in> {pi * (2 * real_of_int l) + arccos t<..<pi * (2 * (real_of_int l + 1)) - arccos t}"
    hence "2 * pi * real_of_int k - arccos t < pi * (2 * (real_of_int l + 1)) - arccos t" by (auto simp: algebra_simps)
    hence "k \<le> l" by auto
    have "pi * (2 * real_of_int l) + arccos t < x" using asm by auto
    also have "\<dots> \<le> 2 * pi * real_of_int k + arccos t" using asm by simp
    finally have "l < k" by simp
    with \<open>k \<le> l\<close> show False by simp
  next
    assume asm: "\<nexists>xa. x \<in> {pi * (2 * real_of_int xa) + arccos t<..<pi * (2 * (real_of_int xa + 1)) - arccos t}"
    moreover obtain k res where res: "0 \<le> res" "res < 2*pi" and x: "x = pi* 2* real_of_int k + res"
      using real_div_split_coi[of "2*pi" x 0 thesis] by fastforce
    have "res \<le> arccos t | 2*pi - arccos t \<le> res" using asm x
      apply (subst (asm) not_ex)
      apply (drule spec[of _ "k"])
      by (simp add: algebra_simps | safe)+
    then show "\<exists>xa. x \<in> {2 * pi * real_of_int xa - arccos t..2 * pi * real_of_int xa + arccos t}"
    proof(elim disjE; intro exI)
      assume "res \<le> arccos t"
      then show "x \<in> {2 * pi * real_of_int k - arccos t..2 * pi * real_of_int k + arccos t}"
        using x res by auto
    next
      assume "2 * pi - arccos t \<le> res"
      then show "x \<in> {2 * pi * real_of_int (k+1) - arccos t..2 * pi * real_of_int (k+1) + arccos t}"
        using x res by (auto simp: algebra_simps)
    qed
  qed
  finally show ?thesis by auto
qed

lemma cos_leq_iff: 
  assumes "t \<in> {-1..1}"
  shows "cos x \<le> (t::real) \<longleftrightarrow> (\<exists>k::int. x \<in> {pi * (2*k) + arccos t..pi*(2*(k+1)) - arccos t})"
    (is "_ = ?r")
proof-
  have "(\<not> (cos x \<le> t)) = (t < cos x)" by auto
  also have "\<dots> =  (\<exists>k::int. x \<in> {2*pi*k - arccos t<..<2*pi*k + arccos t})"
    using assms by (fact cos_greater_iff)
  also have "\<dots> = (\<not> ( ?r))"
  proof (safe)
    fix k l assume asm: "x \<in> {2 * pi * real_of_int k - arccos t<..<2 * pi * real_of_int k + arccos t}"
      "x \<in> {pi * (2 * real_of_int l) + arccos t..pi * (2 * (real_of_int l + 1)) - arccos t}"
    hence "2 * pi * real_of_int k - arccos t < pi * (2 * (real_of_int l + 1)) - arccos t" by (auto simp: algebra_simps)
    hence "k \<le> l" by auto
    have "pi * (2 * real_of_int l) + arccos t \<le> x" using asm by auto
    also have "\<dots> < 2 * pi * real_of_int k + arccos t" using asm by simp
    finally have "l < k" by simp
    with \<open>k\<le>l\<close> show False by simp
  next
    assume asm: "\<nexists>xa. x \<in> {pi * (2 * real_of_int xa) + arccos t..pi * (2 * (real_of_int xa + 1)) - arccos t}"
    moreover obtain k res where res: "0 \<le> res" "res < 2*pi" and x: "x = pi* 2* real_of_int k + res"
      using real_div_split_coi[of "2*pi" x 0 thesis] by fastforce
    have "res < arccos t | 2*pi - arccos t < res" using asm x
      apply (subst (asm) not_ex)
      apply (drule spec[of _ "k"])
      by (simp add: algebra_simps | safe)+
    then show "\<exists>xa. x \<in> {2 * pi * real_of_int xa - arccos t<..<2 * pi * real_of_int xa + arccos t}"
    proof(elim disjE; intro exI)
      assume "res < arccos t"
      then show "x \<in> {2 * pi * real_of_int k - arccos t<..<2 * pi * real_of_int k + arccos t}"
        using x res by auto
    next
      assume "2 * pi - arccos t < res"
      then show "x \<in> {2 * pi * real_of_int (k+1) - arccos t<..<2 * pi * real_of_int (k+1) + arccos t}"
        using x res by (auto simp: algebra_simps)
    qed
  qed
  finally show ?thesis by auto
qed


subsection\<open>Nonnegative derivatives with finitely many zeroes are still increasing\<close>
\<comment>\<open>The following 2 lemmata, in their statement and the second proof, are taken from DERIV.thy\<close>
lemma DERIV_pos_imp_increasing_open_fin_zeroes:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes "finite N"
  assumes "a < b"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>y. DERIV f x :> y \<and> y \<ge> 0 \<and> (y = 0 \<longrightarrow> x \<in> N))"
    and con: "continuous_on {a..b} f"
  shows "f a < f b"
  using assms
proof(induction N arbitrary: a b set: finite)
  case empty
  have "(0 \<le> y \<and> (y = 0 \<longrightarrow> x \<in> {})) = (0 < y)" for x y :: real by auto
  then show ?case using empty DERIV_pos_imp_increasing_open by presburger
next
  case (insert x F)
  show ?case
  proof(cases "x\<in>{a<..<b}")
    case True
    have "f a < f x"
    proof (rule insert(3))
      show "a < t \<Longrightarrow> t < x \<Longrightarrow> \<exists>y. (f has_real_derivative y) (at t) \<and> 0 \<le> y \<and> (y = 0 \<longrightarrow> t \<in> F)" for t
        using insert(5)[of t] True by auto
      show "a < x" using True by simp
      show "continuous_on {a..x} f" using insert(6) True continuous_on_subset by fastforce
    qed
    also have "\<dots> < f b"
    proof (rule insert(3))
      show "x < t \<Longrightarrow> t < b \<Longrightarrow> \<exists>y. (f has_real_derivative y) (at t) \<and> 0 \<le> y \<and> (y = 0 \<longrightarrow> t \<in> F)" for t
        using insert(5)[of t] True by auto
      show "x < b" using True by simp
      show "continuous_on {x..b} f" using insert(6) True continuous_on_subset by fastforce
    qed
    finally show ?thesis .
  next
    case False
    then show ?thesis using insert by auto
  qed
qed

lemma DERIV_pos_imp_increasing_fin_zeros:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  assumes fin: "finite N"
  assumes "a < b"
    and der: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y \<ge> 0 \<and> (y = 0 \<longrightarrow> x \<in> N)"
  shows "f a < f b"
  by (metis less_le_not_le DERIV_atLeastAtMost_imp_continuous_on
      DERIV_pos_imp_increasing_open_fin_zeroes [OF \<open>finite N\<close> \<open>a < b\<close>] der)

subsection\<open>Specializations of the IVT for (strict) monotone real functions\<close>

lemma real_mono_IVT'_set:
  fixes f :: "real \<Rightarrow> real"
  assumes y: "f a \<le> y" "y \<le> f b" "a \<le> b"
  assumes cont: "continuous_on {a..b} f"
  assumes mono: "mono_on {a..b} f"
  shows "\<exists>u v. {x . a \<le> x \<and> x \<le> b \<and> f x = y } = {u..v} \<and> a \<le> u \<and> u \<le> v \<and> v \<le> b"
proof-
  let ?P = "\<lambda>x. a \<le> x \<and> x \<le> b \<and> f x = y"
  let ?S = "{x. ?P x}"
  from IVT'[OF y cont] obtain x where x: "f x = y" "a \<le> x" "x \<le> b" by auto
  have "closed ?S"
    using continuous_closed_preimage_constant[OF cont closed_atLeastAtMost, of y] by simp
  have "connected ?S"
(*     by (smt (verit) UNIV_def x(1) atMost_UNIV_triv dual_order.trans
        intervalE mem_Collect_eq mono monotone_on_def nle_le)
*)
  proof (rule connectedI_interval)
    fix r s t assume asm: "r \<in> ?S" "t\<in>?S" "r \<le> s" "s \<le> t"
    then have "a \<le> s" "s \<le> b" by simp_all
    moreover with asm mono[THEN mono_onD, of r s] mono[THEN mono_onD, of s t]
    have "f s = y" by auto
    ultimately show "s\<in>?S" by simp
  qed
  have "?S \<inter> {a..b} = ?S" by auto
  then have "compact ?S"
    using closed_Int_compact[OF \<open>closed ?S\<close> compact_Icc, of a b] by (simp only:)
  with connected_compact_interval_1[of ?S] \<open>connected ?S\<close>
  obtain u v where "?S = {u..v}" by auto
  then show ?thesis
  proof(intro exI conjI, assumption)
    assume asm: "{x. a \<le> x \<and> x \<le> b \<and> f x = y} = {u..v}"
    with x show "u \<le> v" using disjoint_iff by fastforce
    then show "a \<le> u" "v \<le> b" using asm by fastforce+
  qed
qed

lemma real_smono_IVT'_set:
  fixes f :: "real \<Rightarrow> real"
  assumes y: "f a \<le> y" "y \<le> f b" "a \<le> b"
  assumes cont: "continuous_on {a..b} f"
  assumes smono: "strict_mono_on {a..b} f"
  shows "\<exists>!\<xi>. a \<le> \<xi> \<and> \<xi> \<le> b \<and> f \<xi> = y"
proof-
  have mono: "mono_on {a..b} f" using smono by (fact strict_mono_on_imp_mono_on)
  from real_mono_IVT'_set[OF y cont mono]
  obtain u v where uv: "{x. a \<le> x \<and> x \<le> b \<and> f x = y} = {u..v}" "a \<le> u" "u \<le> v" "v \<le> b"
    by auto
  have "u \<in> {x. a \<le> x \<and> x \<le> b \<and> f x = y}" "v \<in> {x. a \<le> x \<and> x \<le> b \<and> f x = y}"
    using uv by simp_all
  hence "f u = y" "f v = y" by simp_all
  then have False if "u < v"
    using uv(2-4) strict_mono_onD[OF smono _ _ that] by auto
  with uv(3) le_less have "u = v" by auto
  show ?thesis
    by (intro ex1I[of _ u] conjI \<open>f u = y\<close> uv(2) order.trans[OF uv(3,4)])
      (use \<open>u = v\<close> uv(1) in auto)
qed

subsection\<open>Monotonicity rules for @{term mono_on}\<close>

lemma strict_mono_on_less:
  "strict_mono_on S (f:: _ ::linorder \<Rightarrow> _ ::preorder) \<Longrightarrow> x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> (f x < f y) = (x < y)"
proof (intro iffI)
  assume asm: "strict_mono_on S f" "x \<in> S" "y \<in> S" "f x < f y"
  show "x < y"
  proof(rule ccontr)
    assume "\<not> (x < y)"
    hence "y \<le> x" by simp
    then have "f y \<le> f x" using asm strict_mono_on_imp_mono_on[of S f] mono_onD by blast
(*As we have type sort linorder \<Rightarrow> preorder anyway, @thm strict_mono_on_imp_mono_on suffices, 
however, it could be generalized to type sorts order \<Rightarrow> preorder *)
    with asm(4) show False using less_le_not_le by blast
  qed
qed (rule monotone_onD)

lemma sin_antimono_on_pi_halves_3_pi_halves:
"\<lbrakk>pi/2 \<le> x; x \<le> y; y \<le> 3*pi / 2\<rbrakk> \<Longrightarrow> sin y \<le> sin x" 
(*Could be stated as equality if we bound both x and y separately in assms, but i don't need it that general*)
  apply (rule DERIV_nonpos_imp_nonincreasing[of x y sin])
  apply (assumption)
  apply (intro exI conjI derivative_eq_intros)
  apply rule+
proof(subst mult_1_right)
  fix u assume "pi / 2 \<le> x" "x \<le> y" "y \<le> 3 * pi / 2" "x \<le> u" "u \<le> y"
  hence "pi / 2 \<le> u" "u \<le> 3* pi / 2" by simp_all
  then show "cos u \<le> 0"
    by (intro cos_leq_iff[THEN iffD2] exI[of _ 0]) simp_all
qed

section\<open>Main part\<close>
(*
We try to find the lower bound of \<lambda>x. x * sin (1/x)
This is a cont. function on the reals
*)

abbreviation "xsix \<equiv> \<lambda>x::real. x * sin (1/x)"

lemma xsininvx_sym:
  shows "xsix (- x) = xsix x" "xsix 0 = 0" by simp+
\<comment>\<open>Note that Isabelle, due to being a logic of total functions, considers
  the second goal to be a trivial consequence of (semi-)ring axioms.
It's very convenient that limit and Isabelle's function evaluation are equal here,
such that we do not need a case distinction in our function definition.\<close>

lemma continuous_at_0_xsininvx:
  "continuous (at_right 0) (\<lambda>x::real. x * sin(1/x))"
  "continuous (at_left 0) (\<lambda>x::real. x * sin(1/x))"
  unfolding continuous_within by real_asymp+

lemma cont_nonzero_xsininvx: "x \<noteq> 0 \<Longrightarrow> continuous (at x) (\<lambda>x::real. x * sin(1/x))"
  by (intro continuous_intros)

lemma f_cont: "continuous_on UNIV (\<lambda>x::real. x * sin(1/x))"
  unfolding continuous_on_eq_continuous_within
  by (metis cont_nonzero_xsininvx continuous_at_0_xsininvx continuous_at_split)

(*
Differentiation yields (\<lambda>x. - cos (1/x) / x + sin(1/x)) for nonzero x.
The derivative does not exist at zero.
*)

lemma xsix_deriv:
  fixes x::real
  assumes "x \<noteq> 0"
  shows "(xsix has_real_derivative (- cos (1/x) / x + sin(1/x))) (at x)"
  using assms by (fastforce intro: derivative_eq_intros)
(*  by (rule derivative_eq_intros refl | use assms in force)+ *)

lemma xsix_extrema_equiv:
  fixes x::real
  defines "u \<equiv> 1 / x"
  shows "(- cos (1/x) / x + sin(1/x)) = 0 \<longleftrightarrow> tan u = u"
proof(cases "x = 0")
  case False
  have "sin u = 0 \<Longrightarrow> cos u = 0 \<Longrightarrow> False"
    by (metis abs_zero sin_zero_abs_cos_one zero_neq_one)
  with False show ?thesis
    by (auto simp: field_simps tan_def u_def)
qed (auto simp: u_def)


(*
As the minimum does not occur at x = 0, we set u = 1/x.
Simplifying, leaves us with tan u - u = 0 if u \<noteq> \<pi>/2 + k*\<int> -
but in this case, we are simply left with 1 in our derivative, and
0 = nonzero on the rhs, so the equivalence holds.

As tan u is strictly monotone on (-\<pi>/2+ k*\<pi>, \<pi>/2 + k*\<pi>) with limits +-\<infinity>, and
u is bounded in every such interval, and tan u - u is strictly monotone,
there is a unique solution in every such interval, these (rather their inverses)
correspond to the extrema of x*sin(1/x).

(Note that by symmetry of the equation, u is a solution iff -u is one.
HOL being a logic of total functions, tan is 0 at the classically undefined points -
this does not introduce any problems for this application.)

This is more than we need: We need only the least (in absolute value) nonzero solution of
of tan u - u == 0, because this is in fact the sought-after solution - as can be easily seen from a graph.
(Note that it doesn't matter how we know this in advance, only that the inequalities work out)


It then suffices to calculate the solution to tan u - u = 0 for u in (\<pi>/2, 3\<pi>/2) to arbitrary precision.
(this is around 4.4934094579090641753079 or 1.4302966531242027577722\<pi>)
As this does not seem to have a nice closed form, we bound the solution by an appropriate Interval {a..b},
whose bounds satisfy tan a - a \<le> 0 \<le> tan b - b
and derive a lowerbound from these.

*)

lemma xsix_sym_bounded: "(\<And>y. y\<ge>0 \<Longrightarrow> xsix y \<ge> b) \<Longrightarrow> xsix x \<ge> b"
  by (cases "x \<ge> 0") (smt (verit, best) xsininvx_sym(1))+

lemma bd_below_linear_xsininvx: "- abs x \<le> xsix x"
  and bd_above_linear_xsininvx: "xsix x \<le> abs x"
  by (smt (verit) sin_le_one sin_ge_minus_one minus_mult_minus mult_left_le mult_minus_right)+

(*We chose our interval to consider even smaller: As tan pi = 0, it suffices to consider {pi<..<3*pi/2} *)
lemma xsix_bounded_critical_ivl: "\<forall>x\<in>{2/(3*pi) <..<1/pi}. xsix x \<ge> b \<Longrightarrow> xsix x \<ge> b"
proof(rule xsix_sym_bounded)
  fix y::real assume asm: "0 \<le> y" "\<forall>x\<in>{2/(3*pi) <..<1/pi}. xsix x \<ge> b"
  have bd: "b \<le> -0.215"
  proof-
    let ?x = "0.22255"
    have "?x\<in>{2/(3*pi) <..<1/pi}" by (simp, safe) (approximation 6)+
    moreover have "xsix ?x \<le> -0.215" by (approximation 10)
    ultimately show ?thesis using asm(2) by fastforce
  qed
  consider "0 \<le> y" "y \<le> 2/(3*pi)" | "y > 2/(3*pi)" "y < 1/pi" | "y \<ge> 1/pi"
    using \<open>0 \<le> y\<close> by linarith
  thus "b \<le> xsix y"
  proof(cases)
    case 1
    have "b \<le> -0.215" by (fact bd)
    also have "\<dots> \<le> -2 / (3 * pi)" by (approximation 8)
    also have "\<dots> \<le> - abs y" using 1 by auto
    also have "\<dots> \<le> xsix y" by (fact bd_below_linear_xsininvx)
    finally show ?thesis .
  next
    case 2
    then show ?thesis using asm(2) by simp
  next
    case 3
    have "-0.215 \<le> xsix (1/pi)" by (approximation 4)
    also have "\<dots> \<le> xsix y"
    proof(intro DERIV_nonneg_imp_nondecreasing[OF 3, of xsix] exI conjI, rule xsix_deriv)
      fix x assume "1/pi \<le> x"
      moreover have "0 < 1/pi" by simp
      ultimately have "x > 0" by linarith
      then show "x \<noteq> 0" by simp
      have *: "0 \<le> - u * cos u + sin u" if "0 \<le> u" "u \<le> pi" for u
      proof-
        let ?f = "\<lambda>u. -u*cos u + sin u"
        have "0 = ?f 0" by simp
        also have "\<dots> \<le> ?f u"
        proof(intro DERIV_nonneg_imp_nondecreasing[OF that(1)] exI conjI)
          fix a assume asm: \<open>0 \<le> a\<close> "a \<le> u"
          show "((\<lambda>a. - a * cos a + sin a) has_real_derivative sin a * a) (at a)"
            by (fastforce intro: derivative_eq_intros)
          show "0 \<le> sin a * a"
          proof (intro mult_nonneg_nonneg sin_ge_zero asm(1))
            from asm(2) that(2) show "a \<le> pi" by linarith
          qed
        qed
        finally show "0 \<le> - u * cos u + sin u" .
      qed
      let ?u = "1/x"
      have "0 \<le> - ?u * cos ?u + sin ?u"
      proof(rule *)
        show "?u \<ge> 0"
          using \<open>1/pi \<le> x\<close> \<open>0 < 1 / pi\<close> zero_le_divide_1_iff by fastforce
        show "?u \<le> pi"
          using \<open>0 < 1/pi\<close> \<open>1/pi \<le> x\<close> \<open>x > 0\<close> by (simp add: field_split_simps)
      qed
      then show "0 \<le> - cos (1 / x)/x + sin (1 / x) "
        by simp
    qed
    finally show ?thesis using bd by linarith
  qed
qed

lemma tan_minus_id_strict_mono:
  "strict_mono_on {-pi/2+ real_of_int k*pi<..<pi/2 + k*pi} (\<lambda>u. tan u - u)"
  (is "strict_mono_on ?S ?f")
proof (intro strict_mono_onI)
  fix r s assume "r\<in>?S" "s\<in>?S" "r < s"
  show "?f r < ?f s" 
(*The case splits made the choice of rule clear: Showing that ?N is correct takes 30 lines, 
but spares us a case distinction wheter r and s are on the same side of k*pi or different ones*)
  proof(intro DERIV_pos_imp_increasing_fin_zeros[where ?N = "{k*pi}" and ?f = ?f, OF _ \<open>r < s\<close>] conjI exI)
    show "finite {real_of_int k * pi}" by simp
    fix x assume xbounds: "r \<le> x" "x \<le> s"
    have "cos x \<noteq> 0"
    proof (subst cos_zero_iff_int2, safe)
      fix m assume x: "x = real_of_int m * pi + pi / 2"
      then have "m < k"
        using order.strict_trans1[OF \<open>x \<le> s\<close>, of "pi / 2 + real_of_int k * pi"] \<open>s \<in> ?S\<close> by simp
      moreover have "k \<le> m"
      proof-
        have "r \<le> pi * real_of_int m + pi / 2" "pi * real_of_int k < r + pi / 2 "
          using \<open>r \<in> ?S\<close> \<open>r \<le> x\<close> by (simp_all add: x algebra_simps)
        hence "pi * real_of_int k < pi + pi * (real_of_int m)"
          by simp
        hence "pi * real_of_int k < pi * (real_of_int (1+m))"
          by (simp only: of_int_add of_int_1 distrib_left)
        thus "k \<le> m" by simp
      qed
      ultimately show False by simp
    qed
    then show "((\<lambda>u. tan u - u) has_real_derivative 1/(cos x)\<^sup>2 - 1) (at x)"
      by (intro derivative_eq_intros; blast?) (simp add: field_simps)
    show "0 \<le> 1 / (cos x)\<^sup>2 - 1"
    proof-
      have "(cos x)\<^sup>2 \<le> 1"
      proof(cases "cos x \<ge> 0")
        case True
        have "cos x * cos x \<le> 1 * 1" by (intro mult_mono' True cos_le_one)
        then show ?thesis by (simp add: power2_eq_square)
      next
        case False
        have "cos x * cos x \<le> (-1)*(-1)" by (rule mult_mono_nonpos_nonpos) (use False in simp_all)
        then show ?thesis by (simp add: power2_eq_square)
      qed
      thus ?thesis by (simp add: field_split_simps \<open>cos x \<noteq> 0\<close>)
    qed
    show "1 / (cos x)\<^sup>2 - 1 = 0 \<longrightarrow> x \<in> {real_of_int k * pi}"
    proof(simp add: field_simps power2_eq_square, safe)
      have eql: "l = k" if "x = real_of_int l * pi" for l
      proof(cases l k rule: linorder_cases)
        case less
        have "r \<le> pi * real_of_int l" using \<open>r \<le> x\<close> that by (auto simp: mult.commute)
        also have "\<dots> \<le> pi* real_of_int (k-1)" using less by simp
        also have "\<dots> < r - pi + pi / 2" using \<open>r\<in>?S\<close> by (simp add: algebra_simps)
        also have "\<dots> < r" by simp
        finally show ?thesis .
      next
        case greater
        then have "pi*real_of_int (k+1) \<le> pi* real_of_int l" by auto
        also have "\<dots> < pi * real_of_int k + pi / 2"
          using \<open>x \<le> s\<close> \<open>s \<in> ?S\<close> that by (auto simp: algebra_simps)
        finally show ?thesis by (simp add: algebra_simps)
      qed
      assume "cos x * cos x = 1"
      hence "cos x = 1 | cos x = -1" by algebra
      then show "x = pi * real_of_int k"
      proof
        assume "cos x = - 1"
        then obtain l where l: "x = (2 * real_of_int l + 1) *pi" by (auto simp add: cos_eq_minus1)
        let ?l = "2* l +1"
        have "x = real_of_int ?l * pi" using l by simp
        then show "x = pi * real_of_int k" using eql mult.commute by blast
      next
        assume "cos x = 1"
        then obtain l where "x = pi*(2*real_of_int l)" by (auto simp: cos_one_2pi_int)
        with eql[of "(2*l)"] show "x = pi * real_of_int k" by simp
      qed
    qed
  qed
qed

lemma xsix_interval_narrowing:
  fixes lb ub :: real
  defines "dvxsix \<equiv> (\<lambda>x::real. - cos (1/x) / x + sin(1/x))"
    and "dvsgn \<equiv> \<lambda>u::real. tan u - u"
  assumes bds: "2/(3*pi) < lb" "lb \<le> ub" "ub < 1/pi"
    and dvsgn: "dvsgn (1/lb) \<ge> 0" "dvsgn (1/ub) \<le> 0"
  shows "xsix x \<ge> sin (1/lb) * ub"
proof(rule xsix_bounded_critical_ivl, safe)
  fix x assume "x \<in> {2 / (3 * pi)<..<1 / pi}"
  hence xbds: "2 /(3*pi) < x" "x < 1/pi" "0 < x" by simp_all

  from bds have bdssgn[simp]: "0 < ub" "0 < lb" "0 < 1/ub" by auto
  have "continuous_on {lb..ub} dvxsix"
    unfolding dvxsix_def by (intro continuous_intros) (use bds in simp_all)
(*    using bds by (fastforce simp: dvxsix_def intro: continuous_intros)*)
  have "dvxsix y = ((\<lambda>u. cos u * (tan u - u)) o (\<lambda>x. 1/x)) y" if "y\<noteq>0" "cos (1/y) \<noteq> 0" for y
    using that by (simp add: dvxsix_def tan_def o_def field_split_simps split: if_splits)

  have cosnz: "cos (1/y) < 0" if "2/(3*pi) < y" "y < 1/pi" for y
  proof (rule cos_less_iff[THEN iffD2])
    show "\<exists>x. 1 / y \<in> {pi * (2 * real_of_int x) + arccos 0<..<pi * (2 * (real_of_int x + 1)) - arccos 0}" 
    proof (rule exI[where ?x = 0])
      have "pi < 2 / y" "2 / y < 3 * pi" 
        using that apply (simp_all add: field_split_simps)
         apply safe
        using that by simp+
      then show "1 / y \<in> {pi * (2 * real_of_int 0) + arccos 0<..<pi * (2 * (real_of_int 0 + 1)) - arccos 0}" 
        by simp
    qed
  qed simp

  have *: "dvsgn (1/y) \<ge> 0 \<longleftrightarrow> dvxsix y \<le> 0" if "2/(3*pi) < y" "y < 1/pi" for y
    unfolding dvsgn_def dvxsix_def tan_def
    apply (simp only: diff_ge_0_iff_ge diff_le_0_iff_le uminus_add_conv_diff divide_minus_left)
    apply (rule neg_le_divide_eq[of "cos (1/y)" "1/y" "sin (1/y)", simplified])
    using that by (fact cosnz)

  have invbds: "u < 3 * pi / 2" "pi < u" if "u \<in> {1 / ub..1 / lb}" for u
  proof-
    have "u \<le> 1/lb" using that by simp
    also have "\<dots> < (3 * pi) / 2"
      using bds by (auto simp: field_split_simps)
    finally show "u < 3 * pi / 2" .
    have "pi < 1/ub" using bds by (use bds in simp | safe | simp add: field_split_simps)+
    also have "1/ub \<le> u" using that by auto
    finally show "pi < u" .
  qed

  have "1 / ub \<le> 1 / lb"
    using bds by (simp | safe | simp add: field_split_simps)+

  have "continuous_on {pi<..<3* pi / 2} dvsgn" unfolding dvsgn_def
  proof (safe intro!: continuous_intros)
    fix z assume asm: "z \<in> {pi<..<3* pi / 2}" "cos z = 0"
    have "cos z < 0"
    proof(rule cos_less_iff[of 0 z, THEN iffD2])
      show "\<exists>y. z \<in> {pi * (2 * real_of_int y) + arccos 0<..<pi * (2 * (real_of_int y + 1)) - arccos 0}"
        using asm by (auto intro: exI[of _ 0])
    qed simp
    with asm(2) show False by simp
  qed
  then have cont: "continuous_on {1 / ub..1 / lb} dvsgn"
    using invbds by (auto intro: continuous_on_subset)

  moreover have smono: "strict_mono_on {pi / 2<..<3 * pi / 2} dvsgn"
    unfolding dvsgn_def by (fact tan_minus_id_strict_mono[of 1, simplified])
  then have "strict_mono_on {1 / ub..1 / lb} dvsgn"
    by (rule monotone_on_subset) (use invbds in fastforce)

  with real_smono_IVT'_set[of dvsgn "1/ub" 0 "1/lb" , OF dvsgn(2,1) \<open>1/ub \<le> 1/lb\<close> cont]
  obtain \<xi> where xi: "1 / ub \<le> \<xi>" "\<xi> \<le> 1 / lb" "dvsgn \<xi> = 0"
    by fast
  hence "0 < \<xi>" using \<open>0 < 1/ub\<close> by linarith
  define xmin where "xmin \<equiv> 1/\<xi>"
  hence "0 < xmin" using \<open>0 < \<xi>\<close> by (simp_all add: field_split_simps)

  have "lb \<le> xmin" unfolding xmin_def
    using xi(2) \<open>0 < \<xi>\<close> by (simp add: field_split_simps)
  with bds(1) have "2 / (3 * pi) < xmin" by simp

  have "\<xi> * 2 < 3 * pi" 
    using \<open>2 / (3 * pi) < xmin\<close> xmin_def \<open>0 < \<xi>\<close> by (auto simp: field_split_simps)

  have "pi < \<xi> * 2"
    using xi(1) invbds(2)[of "1/ub", simplified] \<open>1 / ub \<le> 1 / lb\<close> bdssgn(3) by linarith

  have "1 / \<xi> \<le> ub"
  proof-
    have "0 < \<xi> / ub" by (rule divide_pos_pos) fact+
    with divide_left_mono[of "1/ ub" \<xi> 1, OF \<open>1/ub \<le> \<xi>\<close>]
    show ?thesis by simp
  qed
 (*Non-strict inequality would suffice*)
  have "xsix x > xsix xmin" if "x < xmin"
  proof (intro DERIV_neg_imp_decreasing_open [OF that] exI conjI)
    show "\<lbrakk>x < u; u < xmin\<rbrakk> \<Longrightarrow> (xsix has_real_derivative dvxsix u) (at u)" for u
      unfolding dvxsix_def by (rule xsix_deriv) (use \<open>0 < x\<close> in simp)
    show "continuous_on {x..xmin} xsix" using continuous_on_subset[OF f_cont subset_UNIV] .
    {
      fix u assume "x<u" "u<xmin"
      hence "2 / (3 * pi) < u" "u \<noteq> 0" "u > 0" using xbds by (auto simp: xmin_def)

      have "u < 1 / pi" using \<open>u < xmin\<close> \<open>1 / \<xi> \<le> ub\<close> bds(2,3) by (simp add: xmin_def)

      have "dvxsix u < 0 \<longleftrightarrow> dvsgn (1/u) > 0"
        using *[of u, symmetric, OF \<open>2/(3*pi) < u\<close> \<open>u < 1/pi\<close>] xsix_extrema_equiv[of u]
        by (auto simp: dvxsix_def dvsgn_def)
      moreover have "dvsgn (1/u) > 0"
      proof(rule smono[THEN strict_mono_onD, of \<xi> "1/u", simplified, simplified xi(3)])
        show "pi < \<xi> * 2" by fact
        show "2 / u < 3 * pi" using \<open>u > 0\<close> \<open>2 / (3 * pi) < u\<close> by (simp add: field_split_simps)
        show "\<xi> < 1 / u"
          using \<open>u > 0\<close> \<open>u < xmin\<close> \<open>0 < \<xi>\<close> by (simp add: field_split_simps xmin_def)
      qed
      ultimately show "dvxsix u < 0"
        by (simp only:)
    }
  qed
  moreover have "xsix x > xsix xmin" if "x > xmin"
  proof (intro DERIV_pos_imp_increasing_open [OF that] exI conjI)
    show "\<lbrakk>xmin < u\<rbrakk> \<Longrightarrow> (xsix has_real_derivative dvxsix u) (at u)" for u
      unfolding dvxsix_def by (rule xsix_deriv) (use \<open>0 < xmin\<close> in simp)
    show "continuous_on {xmin..x} xsix" using continuous_on_subset[OF f_cont subset_UNIV] .
    {
      fix u assume "xmin < u" "u < x"
      hence u: "2 / (3 * pi) < u" "u < 1 / pi" "u\<noteq> 0" "u > 0"
        using \<open>xmin > 0\<close> \<open>2 / (3 * pi) < xmin\<close> xbds(2) by auto

      have "dvxsix u > 0 \<longleftrightarrow> dvsgn (1/u) < 0"
        using *[of u, symmetric, OF \<open>2 / (3 * pi) < u\<close> \<open>u < 1 / pi\<close>] xsix_extrema_equiv[of u]
        by (auto simp: dvxsix_def dvsgn_def)
      moreover have "dvsgn (1/u) < 0"
      proof(rule smono[THEN strict_mono_onD, of "1/u" \<xi>, simplified, simplified xi(3)])
        show "pi < 2 / u" using u by (auto simp: field_split_simps)
        show "\<xi> * 2 < 3 * pi" by fact
        show "1 / u < \<xi>" using xmin_def u(4) apply (auto simp: field_split_simps)
          by (metis \<open>0 < \<xi>\<close> \<open>xmin < u\<close> divide_less_eq mult.commute)
      qed
      ultimately show "0 < dvxsix u"
        by simp
    }
  qed
  ultimately have "xsix x \<ge> xsix xmin" by fastforce
  also have "xsix xmin \<ge> sin (1/lb) * ub"
  proof (subst mult.commute, rule mult_mono_nonneg_nonpos)
    show "sin (1 / lb) \<le> sin (1 / xmin)"
    proof(rule sin_antimono_on_pi_halves_3_pi_halves)
      show "pi / 2 \<le> 1 / xmin" "1 / xmin \<le> 1 / lb" "1 / lb \<le> 3 * pi / 2"
        using xi(2) \<open>pi < \<xi> * 2\<close> \<open>0 <lb \<close> bds(1) by (simp_all add: xmin_def field_split_simps)
    qed
    show "sin (1 / xmin) \<le> 0"
    proof (rule sin_le_zero)
      show "1 / xmin < 2 * pi" using xmin_def \<open>2 / (3 * pi) < xmin\<close> \<open>0 < \<xi>\<close>
        by (auto simp: field_split_simps)
      show "pi \<le> 1/xmin" unfolding xmin_def
        using strict_mono_on_less[OF smono, of pi \<xi>, simplified,
            simplified \<open>\<xi> * 2 < 3 * pi\<close> \<open>dvsgn \<xi> = 0\<close>] \<open>pi < \<xi> * 2\<close> by (simp add: dvsgn_def)
    qed
    show "0 \<le> xmin" using \<open>0 < xmin\<close> by simp
    show "xmin \<le> ub" unfolding xmin_def by fact
  qed
  finally show "sin (1 / lb) * ub \<le> xsix x" .
qed

lemma xsix_lowerbound_78:
  "xsix x \<ge> -0.21723362821122165740827932556247073422304491543558748236544902771450534358906339"
  (is "?u \<le> _")
proof-
\<comment>\<open>Because of approximation, we need this awkward format\<close>
  let ?lb = "1 / (1.430296653124202757772198445458548368922031531701193929953629437593394396862924 * pi )"
  and ?ub = "1 / (1.430296653124202757772198445458548368922031531701193929953629437593394396862923 * pi )"
(*For comparison:*)
  let ?uclaim= "-0.21723362821122165740827932556247073422304491543558748236544902771450534358906339"
  and ?ureal = "-0.2172336282112216574082793255624707342230449154355874823654490277145053435890632291855"

  have "?u \<le> sin (1 / ?lb) * ?ub" by (approximation 267)
  also have "\<dots> \<le> xsix x"
  proof(rule xsix_interval_narrowing)
    show "2 / (3 * pi) < ?lb" by (approximation 11)
    show "?ub < 1/pi" by (approximation 7)
    show "0 \<le> tan (1/?lb) - 1/?lb" by (approximation 264)
    show "?lb \<le> ?ub" by (approximation 262)
    show "tan (1/?ub) - 1/?ub \<le> 0" by (approximation 263)
  qed
  finally show ?thesis .
qed
thm_oracles xsix_lowerbound_78

lemma xsix_lowerbound_78_accurate:
  "\<exists>x. xsix x \<le> -0.21723362821122165740827932556247073422304491543558748236544902771450534358906322"
  (is "\<exists> _. _ \<le> ?u")
proof
  let ?c = "0.22254815844566587021279399510165087142555"
  show "xsix ?c \<le> ?u"
    by (approximation 266)
qed

(* Some more accurate approximations *)
(* tan u = u:     4.4934094579090641753078809272803220822155838722900408028958239619269503145971040987290578094558796915217692198610142800856895097383716922678652322815875333643634255776924777218315283356126190621743243209552544584281718198128769916450794366574987465597477701162901897834303180402120789785639552495164930363632701299681005660940581280051337204986035996815212767258392274928680217482017711289563747923617 *)
(* Inverse:       0.22254815844566587021279399510165087142554929477784419829132148116298129579839475032751823430854169880053677086999327161560964446311937387308588696695863207210857250487460514742679241149761398946457396544419242893634108555710976289388864872440547970738810222143838305002168666211728290866369769260902282618097580733777131890647046787587457203752213366996712943880415039199347593995557680191680896236 *)
(* As above: pi * 1.43029665312420275777219844545854836892203153170119392995362943759339439686292363111039530428710912219056571062570378765611579293221988341910498987218764695231338749364729041738277909099221115969321003426275178169518101811898743299946540337179926250241196249924552075797456395589467167792141902271890485140758261084949520515825794737630838916061071463995063795092427324911986255721394474145179154082 *)
(* fun value:    -0.217233628211221657408279325562470734223044915435587482365449027714505343589063229185568050653923549515201952458893528114289285662812423223140145807009244068852432001945819543671963439301580914832264043840392738459092163793189680761561174015833233133410258971812751450475739863486413807323228906803836974217393494207837640114181242960291748550852075031683003233842292014573852360201738422702322340 *)
end