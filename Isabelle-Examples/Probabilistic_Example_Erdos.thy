section \<open>A Simple Probabilistic Proof by Paul Erdős.\<close>

theory Probabilistic_Example_Erdos
  imports "HOL-Library.Ramsey" "HOL-Probability.Probability" "HOL-ex.Sketch_and_Explore"

begin

thm real_of_nat_div (*INSERT BEFORE TO GENERALISE*)

context field_char_0
begin

lemma of_nat_of_nat_div_aux:
  "of_nat x / of_nat d = of_nat (x div d) + of_nat (x mod d) / of_nat d"
proof -
  have "x = (x div d) * d + x mod d"
    by auto
  then have "of_nat x = of_nat (x div d) * of_nat d + of_nat(x mod d)"
    by (metis of_nat_add of_nat_mult)
  then show ?thesis
    by (auto simp add: divide_simps)
qed

lemma of_nat_of_nat_div: "d dvd n \<Longrightarrow> of_nat(n div d) = of_nat n / of_nat d"
  by (subst of_nat_of_nat_div_aux) (auto simp add: dvd_eq_mod_eq_0 [symmetric])

end


context linordered_field
begin

lemma of_nat_div_le_of_nat: "of_nat (n div x) \<le> of_nat n / of_nat x"
  by (metis le_add_same_cancel1 of_nat_0_le_iff of_nat_of_nat_div_aux zero_le_divide_iff) 

end

subsection \<open>Probabilistic lower bounds: the main  theorem and applications\<close>

theorem
  fixes X :: "'a set"
  assumes X: "\<F> \<subseteq> nsets X n" "finite X"
    and m: "card \<F> = m" "m < 2^(n-1)" and n: "0 < n" "n \<le> card X"
  obtains f::"'a\<Rightarrow>nat" where "f \<in> X \<rightarrow>\<^sub>E {..<2}" "\<And>F c. \<lbrakk>F \<in> \<F>; c<2\<rbrakk> \<Longrightarrow> \<not> f ` F \<subseteq> {c}"
proof -
  have "finite \<F>"
    using X finite_imp_finite_nsets finite_subset by blast
  define \<Omega> where "\<Omega> \<equiv> X \<rightarrow>\<^sub>E {..<2::nat}"
  define M where "M \<equiv> uniform_count_measure \<Omega>"
  have card\<Omega>: "card \<Omega> = 2 ^ card X"
    using \<open>finite X\<close> by (simp add: \<Omega>_def card_funcsetE)
  have \<Omega>: "finite \<Omega>" "\<Omega> \<noteq> {}"
    using card\<Omega> less_irrefl by fastforce+
  interpret P: prob_space M
    unfolding M_def by (intro prob_space_uniform_count_measure \<Omega>)

  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_uniform_count_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_uniform_count_measure)
  have fin_\<Omega>[simp]: "finite \<Omega>"
    by (simp add: \<Omega>_def \<open>finite X\<close> finite_PiE)

\<comment>\<open>the event to avoid: monochromatic sets\<close>
  define mchrome where "mchrome \<equiv> \<lambda>c F. {f \<in> \<Omega>. f ` F \<subseteq> {c}}"
  have mchrome_ev: "mchrome c F \<in> P.events" if "c<2" for F c
    by (auto simp: sets_eq mchrome_def \<Omega>_def)
  have mchrome_sub_\<Omega>: "mchrome c F \<subseteq> \<Omega>" if "c<2" for F c
    using mchrome_ev sets_eq that by auto
  have card_mchrome: "card (mchrome c F) = 2 ^ (card X - n)" if "F \<in> \<F>" "c<2" for F c
  proof -
    have F: "finite F" "card F = n"
      using X(1) nsets_def that(1) by auto
    have "F \<subseteq> X"
      by (metis (no_types, lifting) assms(1) mem_Collect_eq nsets_def subset_iff that(1))
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
    by (simp add: M_def emeasure_uniform_count_measure_if)

  have prob_mchrome: "P.prob (mchrome c F) = 1 / 2^n"  
    if "F \<in> \<F>" "c<2" for F c
  proof -
    have "emeasure M (mchrome c F) = card(mchrome c F) * ennreal (1 / card \<Omega>)"
      using that
      apply (simp add: emeasure_eq card_mchrome)
      apply (auto simp: )
       apply (metis Multiseries_Expansion.intyness_numeral comm_monoid_mult_class.mult_1 ennreal_mult'' ennreal_of_nat_eq_real_of_nat mult_of_nat_commute numeral_eq_of_nat of_nat_0_le_iff of_nat_power times_divide_eq_left)
      using mchrome_sub_\<Omega> that(2) apply blast
      done
    also have "\<dots> = ennreal (1 / 2^n)"
    proof -
      have "real (2 ^ card X div 2 ^ n) * (1 / 2 ^ card X) = (1 / 2 ^ n)"
        using n by (simp add: power_diff card_mchrome card\<Omega> le_imp_power_dvd of_nat_of_nat_div)
      with that show ?thesis
        unfolding card_mchrome card\<Omega>
        by (smt (z3) Multiseries_Expansion.intyness_simps(3) assms(6) card_mchrome ennreal_mult' ennreal_of_nat_eq_real_of_nat numerals(2) of_nat_0_le_iff of_nat_le_0_iff power_diff_power_eq semiring_1_class.of_nat_simps(2) that(2))
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
      by (simp add: prob_mchrome m)
    also have "\<dots> < 1"
      using m \<open>n>0\<close>
      apply (simp add: divide_simps)
      by (metis diff_Suc_1' gr0_implies_Suc mult_2 mult_2_right mult_strict_left_mono of_nat_less_iff of_nat_numeral of_nat_power power_Suc rel_simps(51))
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
