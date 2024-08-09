section \<open>A Simple Probabilistic Proof by Paul Erdős.\<close>

theory Probabilistic_Example_Erdos
  imports "HOL-Library.Ramsey" "HOL-Probability.Probability" "HOL-ex.Sketch_and_Explore"

begin

theorem Erdos_1963:
  assumes X: "\<F> \<subseteq> nsets X n" "finite X"
    and "card \<F> = m" and m: "m < 2^(n-1)" and n: "0 < n" "n \<le> card X"
  obtains f::"'a\<Rightarrow>nat" where "f \<in> X \<rightarrow>\<^sub>E {..<2}" "\<And>F c. \<lbrakk>F \<in> \<F>; c<2\<rbrakk> \<Longrightarrow> \<not> f ` F \<subseteq> {c}"
proof -
  have "finite \<F>"
    using X finite_imp_finite_nsets finite_subset by blast
  define \<Omega> where "\<Omega> \<equiv> X \<rightarrow>\<^sub>E {..<2::nat}"
  define M where "M \<equiv> uniform_count_measure \<Omega>"
  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_uniform_count_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_uniform_count_measure)
  have card\<Omega>: "card \<Omega> = 2 ^ card X"
    using \<open>finite X\<close> by (simp add: \<Omega>_def card_funcsetE)
  have \<Omega>: "finite \<Omega>" "\<Omega> \<noteq> {}"
    using card\<Omega> less_irrefl by fastforce+
  interpret P: prob_space M
    unfolding M_def by (intro prob_space_uniform_count_measure \<Omega>)
  define mchrome where "mchrome \<equiv> \<lambda>c F. {f \<in> \<Omega>. f ` F \<subseteq> {c}}"
      \<comment>\<open>the event to avoid: monochromatic sets\<close>
  have mchrome_ev: "mchrome c F \<in> P.events" if "c<2" for F c
    by (auto simp: sets_eq mchrome_def \<Omega>_def)
  have mchrome_sub_\<Omega>: "mchrome c F \<subseteq> \<Omega>" if "c<2" for F c
    using mchrome_ev sets_eq that by auto
  have card_mchrome: "card (mchrome c F) = 2 ^ (card X - n)" if "F \<in> \<F>" "c<2" for F c
  proof -
    have F: "finite F" "card F = n"
      using X nsets_def that by auto
    have "F \<subseteq> X"
      using assms that by (force simp: nsets_def)
    with F \<open>finite X\<close> have "card ((X-F) \<rightarrow>\<^sub>E {..<2::nat}) = 2 ^ (card X - n)"
      by (simp add: card_funcsetE card_Diff_subset)
    moreover
    have "bij_betw (\<lambda>f. restrict f (X-F)) (mchrome c F) (X-F \<rightarrow>\<^sub>E {..<2::nat})"
    proof (intro bij_betwI)
      show "(\<lambda>g x. if x\<in>F then c else g x) \<in> (X - F \<rightarrow>\<^sub>E {..<2::nat}) \<rightarrow> mchrome c F"
        using that \<open>F \<subseteq> X\<close> by (auto simp: mchrome_def \<Omega>_def)
    qed (fastforce simp: mchrome_def \<Omega>_def)+
    ultimately show ?thesis
      by (metis bij_betw_same_card)
  qed

  have emeasure_eq: "emeasure M C = (if C \<subseteq> \<Omega> then ennreal (card C / card \<Omega>) else 0)" for C
    by (simp add: M_def emeasure_uniform_count_measure_if \<open>finite \<Omega>\<close>)

  have prob_mchrome: "P.prob (mchrome c F) = 1 / 2^n"  
    if "F \<in> \<F>" "c<2" for F c
  proof -
    have "emeasure M (mchrome c F) = ennreal (2 ^ (card X - n) / card \<Omega>)"
      using that mchrome_sub_\<Omega> by (simp add: emeasure_eq card_mchrome)
    also have "\<dots> = ennreal (1 / 2^n)"
    proof -
      have eq: "(1 / 2 ^ n) = real (2 ^ card X div 2 ^ n) * (1 / 2 ^ card X)"
        using n by (simp add: power_diff card_mchrome card\<Omega> le_imp_power_dvd real_of_nat_div)
      show ?thesis
        by (simp add: eq assms(6) card\<Omega> power_diff_power_eq) 
    qed
    finally have "emeasure M (mchrome c F) = ennreal (1 / 2^n)" .
    then show ?thesis
      by (simp add: P.emeasure_eq_measure)
  qed

  have "(\<Union>F\<in>\<F>. \<Union>c<2. mchrome c F) \<subseteq> \<Omega>"
    by (auto simp: mchrome_def \<Omega>_def)
  moreover have "(\<Union>F\<in>\<F>. \<Union>c<2. mchrome c F) \<noteq> \<Omega>"
  proof -
    have "P.prob (\<Union>F\<in>\<F>. \<Union>c<2. mchrome c F) \<le> (\<Sum>F\<in>\<F>. P.prob (\<Union>c<2. mchrome c F))"
      by (metis \<open>finite \<F>\<close> mchrome_ev measure_UNION_le countable_Un_Int(1) lessThan_iff)
    also have "\<dots> \<le> (\<Sum>F\<in>\<F>. \<Sum>c<2. P.prob (mchrome c F))"
      by (smt (verit, best) mchrome_ev sum_mono measure_UNION_le finite_lessThan lessThan_iff)
    also have "\<dots> = m * 2 * (1 / 2^n)"
      by (simp add: prob_mchrome \<open>card \<F> = m\<close>)
    also have "\<dots> < 1"
    proof -
      have "real (m * 2) < 2 ^ n"
        using mult_strict_right_mono [OF m, of 2] \<open>n>0\<close>
        by (metis of_nat_less_numeral_power_cancel_iff pos2 power_minus_mult) 
      then show ?thesis
        by (simp add: divide_simps)
    qed
    finally have "P.prob (\<Union>F\<in>\<F>. \<Union>c<2. mchrome c F) < 1" .
    then show ?thesis
      using P.prob_space space_eq by force
  qed
  ultimately obtain f where f:"f \<in> \<Omega> - (\<Union>F\<in>\<F>. \<Union>c<2. mchrome c F)"
    by blast
  with that show ?thesis
    by (fastforce simp: mchrome_def \<Omega>_def)
qed

end
